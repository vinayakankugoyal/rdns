//! A caching, blocklisting DNS forwarder with Prometheus metrics and a TUI.

use crate::blocklist::DNSBlocklist;
use crate::cache::DNSCache;
use crate::packet::DNSPacket;
use chrono::Local;
use clap::Parser;
use std::collections::HashMap;
use std::io;
use std::net::SocketAddr;
use std::sync::atomic::{AtomicU16, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::net::UdpSocket;
use tokio::sync::broadcast;
use warp::Filter;

mod blocklist;
mod cache;
mod metrics;
mod packet;
mod tui;

/// Maximum size of a UDP DNS message (RFC 1035).
const MAX_PACKET_SIZE: usize = 512;

/// Port the Prometheus metrics endpoint listens on.
const METRICS_PORT: u16 = 3030;

/// Capacity of the broadcast channel used for log lines.
const LOG_CHANNEL_CAPACITY: usize = 100;

/// Interval between cache cleanup sweeps.
const CACHE_CLEANUP_INTERVAL: Duration = Duration::from_secs(10);

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Address of the upstream DNS resolver
    #[arg(short, long, default_value = "1.1.1.1:53")]
    resolver: SocketAddr,

    /// Port to listen on for DNS requests
    #[arg(short, long, default_value_t = 53)]
    port: u16,

    /// Disable the TUI and run in headless mode
    #[arg(long, default_value_t = false)]
    no_tui: bool,
}

/// A query forwarded upstream, awaiting its response.
struct PendingQuery {
    /// Client to relay the response back to.
    client: SocketAddr,
    /// Transaction ID from the client's original query.
    original_id: u16,
    /// When the query was forwarded, for latency measurement.
    sent_at: Instant,
}

/// Shared state for the forwarder, cloned across tasks behind one `Arc`.
struct Server {
    /// Socket clients talk to us on.
    client_socket: UdpSocket,
    /// Socket we talk to the upstream resolver on.
    resolver_socket: UdpSocket,
    resolver_addr: SocketAddr,
    cache: DNSCache,
    /// Kept behind its own `Arc` so the TUI can hold a reference too.
    blocklist: Arc<DNSBlocklist>,
    /// Forwarded queries keyed by the transaction ID we assigned them.
    pending: Mutex<HashMap<u16, PendingQuery>>,
    /// Source of transaction IDs for forwarded queries.
    next_id: AtomicU16,
    log_tx: broadcast::Sender<String>,
}

impl Server {
    /// Sends a timestamped line to the log channel, ignoring the absence of
    /// subscribers (e.g. in headless mode).
    fn log(&self, message: impl AsRef<str>) {
        let timestamp = Local::now().format("%H:%M:%S");
        let _ = self
            .log_tx
            .send(format!("[{}] {}", timestamp, message.as_ref()));
    }
}

/// Serves Prometheus metrics over HTTP on [`METRICS_PORT`].
async fn run_metrics_server() {
    let metrics_route = warp::path("metrics").and(warp::get()).map(|| {
        use prometheus::Encoder;
        let encoder = prometheus::TextEncoder::new();
        let mut buffer = Vec::new();
        if encoder.encode(&prometheus::gather(), &mut buffer).is_err() {
            return String::new();
        }
        String::from_utf8(buffer).unwrap_or_default()
    });
    warp::serve(metrics_route)
        .run(([0, 0, 0, 0], METRICS_PORT))
        .await;
}

/// Relays upstream resolver responses back to the clients that asked for
/// them, recording latency and populating the cache.
async fn process_resolver_responses(server: Arc<Server>) {
    let mut buf = [0; MAX_PACKET_SIZE];

    loop {
        let (size, source) = match server.resolver_socket.recv_from(&mut buf).await {
            Ok(received) => received,
            Err(e) => {
                server.log(format!("Failed to receive from resolver: {}", e));
                continue;
            }
        };
        if source != server.resolver_addr {
            continue;
        }

        let Some(mut packet) = DNSPacket::from_bytes(&buf[..size]) else {
            continue;
        };

        let pending_entry = server
            .pending
            .lock()
            .unwrap()
            .remove(&packet.header.packet_id);

        let Some(query) = pending_entry else {
            server.log("Transaction ID not found!");
            continue;
        };

        let latency = query.sent_at.elapsed();
        metrics::RESPONSE_TIME.observe(latency.as_secs_f64());
        metrics::record_latency(latency.as_millis() as u64);

        packet.header.packet_id = query.original_id;
        if let Err(e) = server
            .client_socket
            .send_to(&packet.to_bytes(), query.client)
            .await
        {
            server.log(format!("Failed to relay response: {}", e));
            continue;
        }

        if let Some(question) = packet.questions.first() {
            server.log(format!(
                "[{}] {} -> FORWARDED ({}ms)",
                query.client,
                question.display_name(),
                latency.as_millis()
            ));
        }

        // The packet is no longer needed, so its parts can move into the
        // cache without cloning.
        if !packet.questions.is_empty() {
            let question = packet.questions.swap_remove(0);
            server.cache.insert(question, packet.answers);
        }
    }
}

/// Handles a single client query: answers from the blocklist or cache when
/// possible, otherwise forwards it upstream.
async fn handle_dns_request(server: Arc<Server>, data: Vec<u8>, source: SocketAddr) {
    let start = Instant::now();
    let Some(mut packet) = DNSPacket::from_bytes(&data) else {
        return;
    };

    let Some(question) = packet.questions.first() else {
        return;
    };
    let q_name = question.display_name();

    if packet.questions.len() > 1 {
        server.log(format!(
            "Received {} questions from {}, processing first",
            packet.questions.len(),
            source
        ));
    }

    if server.blocklist.contains(&q_name) {
        metrics::BLOCKED_REQUESTS.inc();
        let latency = start.elapsed();
        metrics::RESPONSE_TIME.observe(latency.as_secs_f64());
        metrics::record_latency(latency.as_millis() as u64);

        let answers = [question.to_blocked_answer()];
        let response = packet.response_bytes(&answers);
        match server.client_socket.send_to(&response, source).await {
            Ok(_) => server.log(format!("[{}] {} -> BLOCKED", source, q_name)),
            Err(e) => server.log(format!("Failed to send blocked response: {}", e)),
        }
        return;
    }

    if let Some(answers) = server.cache.get(question) {
        metrics::CACHE_HITS.inc();
        let latency = start.elapsed();
        metrics::RESPONSE_TIME.observe(latency.as_secs_f64());
        metrics::record_latency(latency.as_millis() as u64);

        let response = packet.response_bytes(&answers);
        match server.client_socket.send_to(&response, source).await {
            Ok(_) => server.log(format!(
                "[{}] {} -> CACHE HIT ({}µs)",
                source,
                q_name,
                latency.as_micros()
            )),
            Err(e) => server.log(format!("Failed to send cached response: {}", e)),
        }
        return;
    }

    metrics::CACHE_MISSES.inc();

    let original_id = packet.header.packet_id;
    let new_id = server.next_id.fetch_add(1, Ordering::Relaxed);

    server.pending.lock().unwrap().insert(
        new_id,
        PendingQuery {
            client: source,
            original_id,
            sent_at: Instant::now(),
        },
    );

    packet.header.packet_id = new_id;
    if let Err(e) = server
        .resolver_socket
        .send_to(&packet.to_bytes(), server.resolver_addr)
        .await
    {
        server.log(format!("Failed to forward request: {}", e));
        server.pending.lock().unwrap().remove(&new_id);
    }
}

/// Periodically evicts expired cache entries.
async fn cleanup_cache(server: Arc<Server>) {
    loop {
        tokio::time::sleep(CACHE_CLEANUP_INTERVAL).await;
        server.cache.cleanup(Instant::now());
    }
}

#[tokio::main]
async fn main() -> io::Result<()> {
    let args = Args::parse();

    let (log_tx, _) = broadcast::channel(LOG_CHANNEL_CAPACITY);

    let server = Arc::new(Server {
        client_socket: UdpSocket::bind(("0.0.0.0", args.port)).await?,
        resolver_socket: UdpSocket::bind("0.0.0.0:0").await?,
        resolver_addr: args.resolver,
        cache: DNSCache::new(),
        blocklist: Arc::new(DNSBlocklist::new()),
        pending: Mutex::new(HashMap::new()),
        next_id: AtomicU16::new(0),
        log_tx: log_tx.clone(),
    });

    tokio::spawn(run_metrics_server());

    tokio::spawn({
        let server = Arc::clone(&server);
        async move {
            tokio::time::sleep(Duration::from_millis(500)).await;
            match server.blocklist.update().await {
                Ok(count) => server.log(format!("Blocklist loaded: {} domains", count)),
                Err(e) => server.log(format!("Failed to update blocklist: {}", e)),
            }
        }
    });

    tokio::spawn(process_resolver_responses(Arc::clone(&server)));
    tokio::spawn(cleanup_cache(Arc::clone(&server)));

    if !args.no_tui {
        let tui_blocklist = Arc::clone(&server.blocklist);
        let tui_rx = log_tx.subscribe();
        tokio::spawn(async move {
            if let Err(e) = tui::run(tui_rx, tui_blocklist).await {
                eprintln!("TUI error: {}", e);
            }
            // The TUI exiting (user pressed 'q') shuts down the whole app.
            std::process::exit(0);
        });
    }

    let mut buf = [0; MAX_PACKET_SIZE];
    loop {
        let (size, source) = server.client_socket.recv_from(&mut buf).await?;
        if source == server.resolver_addr {
            continue;
        }

        tokio::spawn(handle_dns_request(
            Arc::clone(&server),
            buf[..size].to_vec(),
            source,
        ));
    }
}

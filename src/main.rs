//! A caching, blocklisting DNS forwarder with Prometheus metrics and a TUI.

use crate::blocklist::DNSBlocklist;
use crate::cache::DNSCache;
use crate::packet::{DNSPacket, MAX_UDP_PAYLOAD, Question, RCODE_NOERROR, RCODE_SERVFAIL, set_id};
use chrono::Local;
use clap::Parser;
use std::io;
use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::net::UdpSocket;
use tokio::sync::broadcast;
use warp::Filter;

mod blocklist;
mod cache;
mod metrics;
mod packet;
mod tui;

#[cfg(test)]
#[path = "spec/forwarder_spec.rs"]
mod forwarder_spec;

/// Port the Prometheus metrics endpoint listens on.
const METRICS_PORT: u16 = 3030;

/// Capacity of the broadcast channel used for log lines.
const LOG_CHANNEL_CAPACITY: usize = 100;

/// Receive buffer for upstream responses: the largest possible UDP
/// payload, so no response is ever cut short, whatever EDNS size the
/// client asked the upstream for.
const MAX_UPSTREAM_PAYLOAD: usize = 65535;

/// How long to wait for the upstream resolver before answering SERVFAIL.
const UPSTREAM_TIMEOUT: Duration = Duration::from_secs(5);

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

    /// Keep cache entries for at least this many seconds, even when record
    /// TTLs are shorter. Served TTLs still count down to 0.
    #[arg(long, default_value_t = 0)]
    min_cache_ttl: u32,

    /// Disable the TUI and run in headless mode
    #[arg(long, default_value_t = false)]
    no_tui: bool,
}

/// Shared state for the forwarder, cloned across tasks behind one `Arc`.
struct Server {
    /// Socket clients talk to us on.
    client_socket: UdpSocket,
    resolver_addr: SocketAddr,
    /// How long to wait for the upstream before answering SERVFAIL.
    upstream_timeout: Duration,
    cache: DNSCache,
    /// Kept behind its own `Arc` so the TUI can hold a reference too.
    blocklist: Arc<DNSBlocklist>,
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

    /// Forwards the raw `query` upstream and waits for the response that
    /// answers `question`. Returns the raw response and its parsed form.
    ///
    /// Each query gets its own socket on a kernel-chosen ephemeral port,
    /// connected to the resolver (so datagrams from any other address are
    /// discarded by the kernel), and a random transaction ID. A datagram is
    /// accepted only if it is a well-formed response with that ID to the
    /// same question; anything else is ignored until the timeout.
    async fn forward(
        &self,
        mut query: Vec<u8>,
        question: &Question,
    ) -> io::Result<(Vec<u8>, DNSPacket)> {
        let local: SocketAddr = if self.resolver_addr.is_ipv4() {
            (Ipv4Addr::UNSPECIFIED, 0).into()
        } else {
            (Ipv6Addr::UNSPECIFIED, 0).into()
        };
        let socket = UdpSocket::bind(local).await?;
        socket.connect(self.resolver_addr).await?;

        let id: u16 = rand::random();
        set_id(&mut query, id);
        socket.send(&query).await?;

        let mut buf = vec![0; MAX_UPSTREAM_PAYLOAD];
        let wait_for_answer = async {
            loop {
                let size = socket.recv(&mut buf).await?;
                let Some(response) = DNSPacket::from_bytes(&buf[..size]) else {
                    continue;
                };
                if response.header.packet_id == id
                    && response.header.qr == 1
                    && response.questions.first() == Some(question)
                {
                    return Ok((buf[..size].to_vec(), response));
                }
            }
        };
        tokio::time::timeout(self.upstream_timeout, wait_for_answer)
            .await
            .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "upstream timed out"))?
    }

    /// Sends `response` to the client that sent `query`. If it is larger
    /// than the client can receive, sends an empty response with TC set
    /// instead.
    async fn reply(
        &self,
        query: &DNSPacket,
        response: Vec<u8>,
        client: SocketAddr,
    ) -> io::Result<()> {
        let response = if response.len() > query.udp_payload_limit() {
            query.truncated_bytes(response[3] & 0x0f)
        } else {
            response
        };
        self.client_socket.send_to(&response, client).await?;
        Ok(())
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

/// Handles a single client query: answers from the blocklist or cache when
/// possible, otherwise forwards it upstream and relays the response.
async fn handle_dns_request(server: Arc<Server>, data: Vec<u8>, source: SocketAddr) {
    let start = Instant::now();
    let Some(packet) = DNSPacket::from_bytes(&data) else {
        return;
    };
    // Only queries are answered; stray responses are dropped.
    if packet.header.qr == 1 {
        return;
    }
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
        record_latency(start);

        let answers: Vec<_> = question.to_blocked_answer().into_iter().collect();
        let response = packet.response_bytes(RCODE_NOERROR, &answers, &[], 0);
        match server.reply(&packet, response, source).await {
            Ok(()) => server.log(format!("[{}] {} -> BLOCKED", source, q_name)),
            Err(e) => server.log(format!("Failed to send blocked response: {}", e)),
        }
        return;
    }

    if let Some(hit) = server.cache.get(question) {
        metrics::CACHE_HITS.inc();
        let latency = record_latency(start);

        let cached = &hit.response;
        let response =
            packet.response_bytes(cached.rcode, &cached.answers, &cached.authorities, hit.age);
        match server.reply(&packet, response, source).await {
            Ok(()) => server.log(format!(
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

    let (mut raw, upstream) = match server.forward(data, question).await {
        Ok(response) => response,
        Err(e) => {
            server.log(format!("[{}] {} -> SERVFAIL ({})", source, q_name, e));
            let response = packet.response_bytes(RCODE_SERVFAIL, &[], &[], 0);
            let _ = server.reply(&packet, response, source).await;
            return;
        }
    };
    let latency = record_latency(start);

    // Relay the upstream bytes untouched apart from the ID, so nothing is
    // lost or reshaped in re-serialization.
    set_id(&mut raw, packet.header.packet_id);
    if let Err(e) = server.reply(&packet, raw, source).await {
        server.log(format!("Failed to relay response: {}", e));
        return;
    }
    server.log(format!(
        "[{}] {} -> FORWARDED ({}ms)",
        source,
        q_name,
        latency.as_millis()
    ));

    server.cache.insert(question.clone(), upstream);
}

/// Records the time since `start` in the latency metrics and returns it.
fn record_latency(start: Instant) -> Duration {
    let latency = start.elapsed();
    metrics::RESPONSE_TIME.observe(latency.as_secs_f64());
    metrics::record_latency(latency.as_millis() as u64);
    latency
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
        resolver_addr: args.resolver,
        upstream_timeout: UPSTREAM_TIMEOUT,
        cache: DNSCache::new(args.min_cache_ttl),
        blocklist: Arc::new(DNSBlocklist::new()),
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

    let mut buf = [0; MAX_UDP_PAYLOAD];
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

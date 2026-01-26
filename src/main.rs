use chrono::Local;
use clap::Parser;
use crate::blocklist::DNSBlocklist;
use crate::cache::DNSCache;
use crate::packet::DNSPacket;
use std::collections::HashMap;
use std::io;
use std::net::SocketAddr;
use std::sync::atomic::AtomicU16;
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

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Address of the upstream DNS resolver
    #[arg(short, long, default_value = "1.1.1.1:53")]
    resolver: String,

    /// Port to listen on for DNS requests
    #[arg(short, long, default_value_t = 53)]
    port: u16,
}

async fn run_metrics_server() {
    let metrics_route = warp::path("metrics").and(warp::get()).map(|| {
        use prometheus::Encoder;
        let encoder = prometheus::TextEncoder::new();
        let mut buffer = Vec::new();
        encoder.encode(&prometheus::gather(), &mut buffer).unwrap();
        String::from_utf8(buffer).unwrap()
    });
    warp::serve(metrics_route).run(([0, 0, 0, 0], 3032)).await;
}

async fn process_resolver_responses(
    resolver_socket: Arc<UdpSocket>,
    client_socket: Arc<UdpSocket>,
    pending: Arc<Mutex<HashMap<u16, (SocketAddr, u16, Instant)>>>,
    cache: Arc<DNSCache>,
    log_tx: broadcast::Sender<String>,
    resolver_addr: String,
) {
    let mut buf = [0; 512];

    loop {
        let (size, source) = resolver_socket.recv_from(&mut buf).await.unwrap();
        if source.to_string() != resolver_addr {
            continue;
        }

        let mut packet = DNSPacket::from_bytes(&buf[0..size]);

        let original_packet_id = packet.header.packet_id;
        let pending_entry = {
            let mut pending_map = pending.lock().unwrap();
            pending_map.remove(&original_packet_id)
        };

        if let Some((forwaridng_address, tid, start_time)) = pending_entry {
            let latency = start_time.elapsed();
            metrics::RESPONSE_TIME.observe(latency.as_secs_f64());
            metrics::record_latency(latency.as_millis() as u64);
            packet.header.packet_id = tid;
            client_socket
                .send_to(&packet.to_bytes(), forwaridng_address)
                .await
                .unwrap();

            if !packet.questions.is_empty() {
                 // Clean up question string for display
                 let q_name = packet.questions[0].to_string().replace("question=", "");
                 let timestamp = Local::now().format("%H:%M:%S");
                 let _ = log_tx.send(format!("[{}] [{}] {} -> FORWARDED ({}ms)", timestamp, forwaridng_address, q_name, start_time.elapsed().as_millis()));
            }

            if !packet.questions.is_empty() {
                cache.insert(packet.questions[0].clone(), packet.answers.clone());
            }
        } else {
             let timestamp = Local::now().format("%H:%M:%S");
             let _ = log_tx.send(format!("[{}] Transaction ID not found!", timestamp));
        }
    }
}

async fn handle_dns_request(
    data: Vec<u8>,
    client_socket: Arc<UdpSocket>,
    source: SocketAddr,
    resolver_socket: Arc<UdpSocket>,
    cache: Arc<DNSCache>,
    pending: Arc<Mutex<HashMap<u16, (SocketAddr, u16, Instant)>>>,
    transaction_id: Arc<AtomicU16>,
    blocklist: Arc<DNSBlocklist>,
    log_tx: broadcast::Sender<String>,
    resolver_addr: String,
) {
    let start = Instant::now();
    let _timer = metrics::RESPONSE_TIME.start_timer();
    let mut packet = DNSPacket::from_bytes(&data);

    if packet.questions.len() == 0 {
        return;
    }

    let q_name = packet.questions[0].to_string().replace("question=", "");

    if packet.questions.len() > 1 {
        let timestamp = Local::now().format("%H:%M:%S");
        let _ = log_tx.send(format!("[{}] Received {} questions from {}, processing first", timestamp, packet.questions.len(), source));
    }

    if blocklist.contains(&packet.questions[0]) {
        metrics::BLOCKED_REQUESTS.inc();
        let latency = start.elapsed();
        metrics::record_latency(latency.as_millis() as u64);

        packet.answers = vec![packet.questions[0].to_blocked_answer()];
        packet.header.qr = 1;
        packet.header.ra = 1;
        packet.header.ancount = packet.answers.len() as u16;
        packet.header.nscount = 0;
        packet.header.arcount = 0;
        packet.authorities = Vec::new();
        packet.resources = Vec::new();

        if let Err(e) = client_socket.send_to(&packet.to_bytes(), source).await {
            let timestamp = Local::now().format("%H:%M:%S");
            let _ = log_tx.send(format!("[{}] Failed to send blocked response: {}", timestamp, e));
        } else {
            let timestamp = Local::now().format("%H:%M:%S");
            let _ = log_tx.send(format!("[{}] [{}] {} -> BLOCKED", timestamp, source, q_name));
        }
        return;
    }

    let cached_answers = cache.get(&packet.questions[0]);

    if let Some(answers) = cached_answers {
        metrics::CACHE_HITS.inc();
        let latency = start.elapsed();
        metrics::record_latency(latency.as_millis() as u64);

        packet.answers = answers;
        packet.header.qr = 1;
        packet.header.ra = 1;
        packet.header.ancount = packet.answers.len() as u16;
        packet.header.nscount = 0;
        packet.header.arcount = 0;
        packet.authorities = Vec::new();
        packet.resources = Vec::new();

        if let Err(e) = client_socket.send_to(&packet.to_bytes(), source).await {
             let timestamp = Local::now().format("%H:%M:%S");
             let _ = log_tx.send(format!("[{}] Failed to send cached response: {}", timestamp, e));
        } else {
             let timestamp = Local::now().format("%H:%M:%S");
             let _ = log_tx.send(format!("[{}] [{}] {} -> CACHE HIT ({}µs)", timestamp, source, q_name, latency.as_micros()));
        }
        return;
    }

    metrics::CACHE_MISSES.inc();

    let original_id = packet.header.packet_id;
    let new_id = transaction_id.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

    {
        let mut pending_map = pending.lock().unwrap();
        pending_map.insert(new_id, (source, original_id, Instant::now()));
    }

    packet.header.packet_id = new_id;

    if let Err(e) = resolver_socket
        .send_to(&packet.to_bytes(), &resolver_addr)
        .await
    {
         let _ = log_tx.send(format!("Failed to forward request: {}", e));
    }
}

async fn cleanup_cache(cache: Arc<DNSCache>) {
    loop {
        tokio::time::sleep(Duration::from_secs(10)).await;
        cache.cleanup(Instant::now());
    }
}

#[tokio::main]
async fn main() -> io::Result<()> {
    let args = Args::parse();

    // Channel for log messages
    let (log_tx, _) = broadcast::channel(100);

    tokio::spawn(run_metrics_server());

    let blocklist = Arc::new(DNSBlocklist::new());

    let client_socket = UdpSocket::bind(format!("0.0.0.0:{}", args.port)).await?;
    let client_socket_ref = Arc::new(client_socket);

    let blocklist_updater = blocklist.clone();
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(500)).await;
        blocklist_updater.update().await;
    });

    let resolver_socket = UdpSocket::bind("0.0.0.0:0").await?;
    let resolver_socket_ref = Arc::new(resolver_socket);

    let cache = Arc::new(DNSCache::new());
    let pending: Arc<Mutex<HashMap<u16, (SocketAddr, u16, Instant)>>> =
        Arc::new(Mutex::new(HashMap::new()));
    let transaction_id: Arc<AtomicU16> = Arc::new(AtomicU16::new(0));

    let client_socket_clone = client_socket_ref.clone();
    let resolver_socket_clone = resolver_socket_ref.clone();
    let pending_clone = pending.clone();
    let cache_clone = cache.clone();
    let log_tx_clone = log_tx.clone();
    let resolver_addr = args.resolver.clone();

    tokio::spawn(process_resolver_responses(
        resolver_socket_clone,
        client_socket_clone,
        pending_clone,
        cache_clone,
        log_tx_clone,
        resolver_addr,
    ));

    let cache_cleanup = cache.clone();
    tokio::spawn(cleanup_cache(cache_cleanup));

    // Spawn TUI
    let tui_blocklist = blocklist.clone();
    let tui_rx = log_tx.subscribe();
    tokio::spawn(async move {
        if let Err(e) = tui::run(tui_rx, tui_blocklist).await {
            eprintln!("TUI error: {}", e);
        }
        // If TUI exits (user pressed 'q'), we might want to shutdown the whole app.
        // For now, let's just exit the process.
        std::process::exit(0);
    });

    let mut buf = [0; 512];

    loop {
        let (size, source) = client_socket_ref.recv_from(&mut buf).await?;

        if source.to_string() == args.resolver {
            continue;
        }

        let data = buf[0..size].to_vec();
        let client_socket_clone = client_socket_ref.clone();
        let resolver_socket_clone = resolver_socket_ref.clone();
        let pending_clone = pending.clone();
        let cache_clone = cache.clone();
        let transaction_id_clone = transaction_id.clone();
        let blocklist_clone = blocklist.clone();
        let log_tx_clone = log_tx.clone();
        let resolver_addr = args.resolver.clone();

        tokio::spawn(handle_dns_request(
            data,
            client_socket_clone,
            source,
            resolver_socket_clone,
            cache_clone,
            pending_clone,
            transaction_id_clone,
            blocklist_clone,
            log_tx_clone,
            resolver_addr,
        ));
    }
}
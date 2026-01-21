use crate::cache::DNSCache;
use crate::packet::DNSPacket;
use lazy_static::lazy_static;
use prometheus::{Counter, Histogram, register_counter, register_histogram};
use std::collections::HashMap;
use std::io;
use std::net::SocketAddr;
use std::sync::atomic::AtomicU16;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::net::UdpSocket;
use warp::Filter;

mod cache;
mod packet;

lazy_static! {
    static ref CACHE_HITS: Counter =
        register_counter!("dns_cache_hits", "Number of cache hits").unwrap();
    static ref CACHE_MISSES: Counter =
        register_counter!("dns_cache_misses", "Number of cache misses").unwrap();
    static ref RESPONSE_TIME: Histogram =
        register_histogram!("dns_response_time_seconds", "Response time in seconds").unwrap();
}

async fn run_metrics_server() {
    let metrics_route = warp::path("metrics").and(warp::get()).map(|| {
        use prometheus::Encoder;
        let encoder = prometheus::TextEncoder::new();
        let mut buffer = Vec::new();
        encoder.encode(&prometheus::gather(), &mut buffer).unwrap();
        String::from_utf8(buffer).unwrap()
    });
    warp::serve(metrics_route).run(([0, 0, 0, 0], 3030)).await;
}

async fn process_resolver_responses(
    resolver_socket: Arc<UdpSocket>,
    client_socket: Arc<UdpSocket>,
    pending: Arc<Mutex<HashMap<u16, (SocketAddr, u16, Instant)>>>,
    cache: Arc<DNSCache>,
) {
    let mut buf = [0; 512];

    loop {
        let (size, source) = resolver_socket.recv_from(&mut buf).await.unwrap();
        if source.to_string() != "1.1.1.1:53" {
            continue;
        }

        let mut packet = DNSPacket::from_bytes(&buf[0..size]);

        for a in packet.answers.iter() {
            println!("{}", a)
        }

        let original_packet_id = packet.header.packet_id;
        let pending_entry = {
            let mut pending_map = pending.lock().unwrap();
            pending_map.remove(&original_packet_id)
        };

        if let Some((forwaridng_address, tid, start_time)) = pending_entry {
            RESPONSE_TIME.observe(start_time.elapsed().as_secs_f64());
            packet.header.packet_id = tid;
            client_socket
                .send_to(&packet.to_bytes(), forwaridng_address)
                .await
                .unwrap();

            cache.insert(packet.questions[0].clone(), packet.answers.clone());
        } else {
            eprintln!("transaction id not found!")
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
) {
    let timer = RESPONSE_TIME.start_timer();
    let mut packet = DNSPacket::from_bytes(&data);
    if packet.questions.len() > 1 {
        println!(
            "recieved {} questions; processing only the first...",
            packet.questions.len()
        );
    }

    let cached_answers = cache.get(&packet.questions[0]);

    if let Some(answers) = cached_answers {
        CACHE_HITS.inc();
        timer.observe_duration();

        packet.answers = answers;
        packet.header.qr = 1;
        packet.header.ra = 1;
        packet.header.ancount = packet.answers.len() as u16;
        packet.header.nscount = 0;
        packet.header.arcount = 0;
        packet.authorities = Vec::new();
        packet.resources = Vec::new();

        if let Err(e) = client_socket.send_to(&packet.to_bytes(), source).await {
            eprintln!("Failed to send response to client: {}", e);
        }
        return;
    }

    CACHE_MISSES.inc();

    let original_id = packet.header.packet_id;
    let new_id = transaction_id.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

    {
        let mut pending_map = pending.lock().unwrap();
        pending_map.insert(new_id, (source, original_id, Instant::now()));
    }

    packet.header.packet_id = new_id;

    if let Err(e) = resolver_socket
        .send_to(&packet.to_bytes(), "1.1.1.1:53")
        .await
    {
        eprintln!("Failed to forward request to resolver: {}", e);
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
    tokio::spawn(run_metrics_server());

    let client_socket = UdpSocket::bind("0.0.0.0:53").await?;
    let client_socket_ref = Arc::new(client_socket);

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

    tokio::spawn(process_resolver_responses(
        resolver_socket_clone,
        client_socket_clone,
        pending_clone,
        cache_clone,
    ));

    let cache_cleanup = cache.clone();
    tokio::spawn(cleanup_cache(cache_cleanup));

    let mut buf = [0; 512];

    loop {
        let (size, source) = client_socket_ref.recv_from(&mut buf).await?;

        if source.to_string() == "1.1.1.1:53" {
            continue;
        }

        let data = buf[0..size].to_vec();
        let client_socket_clone = client_socket_ref.clone();
        let resolver_socket_clone = resolver_socket_ref.clone();
        let pending_clone = pending.clone();
        let cache_clone = cache.clone();
        let transaction_id_clone = transaction_id.clone();

        tokio::spawn(handle_dns_request(
            data,
            client_socket_clone,
            source,
            resolver_socket_clone,
            cache_clone,
            pending_clone,
            transaction_id_clone,
        ));
    }
}

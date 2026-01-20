use crate::packet::{Answer, DNSPacket, Question};
use lazy_static::lazy_static;
use prometheus::{register_counter, register_histogram, Counter, Histogram};
use std::collections::HashMap;
use std::io;
use std::net::SocketAddr;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::net::UdpSocket;
use warp::Filter;

mod packet;

lazy_static! {
    static ref CACHE_HITS: Counter =
        register_counter!("dns_cache_hits", "Number of cache hits").unwrap();
    static ref CACHE_MISSES: Counter =
        register_counter!("dns_cache_misses", "Number of cache misses").unwrap();
    static ref RESPONSE_TIME: Histogram =
        register_histogram!("dns_response_time_seconds", "Response time in seconds").unwrap();
}

#[tokio::main]
async fn main() -> io::Result<()> {
    tokio::spawn(async move {
        let metrics_route = warp::path("metrics").and(warp::get()).map(|| {
            use prometheus::Encoder;
            let encoder = prometheus::TextEncoder::new();
            let mut buffer = Vec::new();
            encoder.encode(&prometheus::gather(), &mut buffer).unwrap();
            String::from_utf8(buffer).unwrap()
        });
        warp::serve(metrics_route).run(([0, 0, 0, 0], 3030)).await;
    });

    let client_socket = UdpSocket::bind("0.0.0.0:53").await?;
    let client_socket_ref = Arc::new(client_socket);

    let resolver_socket = UdpSocket::bind("0.0.0.0:0").await?;
    let resolver_socket_ref = Arc::new(resolver_socket);

    let cache: Arc<Mutex<HashMap<Question, (Vec<Answer>, Instant)>>> =
        Arc::new(Mutex::new(HashMap::new()));
    let pending: Arc<Mutex<HashMap<u16, (SocketAddr, u16, Instant)>>> =
        Arc::new(Mutex::new(HashMap::new()));
    let mut transaction_id: u16 = 0;

    let client_socket_clone = client_socket_ref.clone();
    let resolver_socket_clone = resolver_socket_ref.clone();
    let pending_clone = pending.clone();
    let cache_clone = cache.clone();

    tokio::spawn(async move {
        let mut buf = [0; 512];

        loop {
            let (size, source) = resolver_socket_clone.recv_from(&mut buf).await.unwrap();
            if source.to_string() != "1.1.1.1:53" {
                continue;
            }

            let mut packet = DNSPacket::from_bytes(&buf[0..size]);

            for a in packet.answers.iter() {
                println!("{}", a)
            }

            let original_packet_id = packet.header.packet_id;
            let pending_entry = {
                let mut pending_map = pending_clone.lock().unwrap();
                pending_map.remove(&original_packet_id)
            };

            if let Some((forwaridng_address, tid, start_time)) = pending_entry {
                RESPONSE_TIME.observe(start_time.elapsed().as_secs_f64());
                packet.header.packet_id = tid;
                client_socket_clone
                    .send_to(&packet.to_bytes(), forwaridng_address)
                    .await
                    .unwrap();

                let mut cache = cache_clone.lock().unwrap();
                let min_ttl = packet.answers.iter().map(|a| a.ttl).min().unwrap_or(300);
                cache.insert(
                    packet.questions[0].clone(),
                    (
                        packet.answers.clone(),
                        Instant::now() + Duration::from_secs(min_ttl as u64),
                    ),
                );
            } else {
                eprintln!("transaction id not found!")
            }
        }
    });

    let mut buf = [0; 512];

    loop {
        let (size, source) = client_socket_ref.recv_from(&mut buf).await?;
        let timer = RESPONSE_TIME.start_timer();

        if source.to_string() == "1.1.1.1:53" {
            continue;
        }

        let mut packet = DNSPacket::from_bytes(&buf[0..size]);

        if packet.questions.len() > 1 {
            println!(
                "recieved {} questions; processing only the first...",
                packet.questions.len()
            );
        }

        let mut cache_ref = cache.lock().unwrap();
        if let Some((answers, expiry)) = cache_ref.get(&packet.questions[0]) {
            if *expiry > Instant::now() {
                CACHE_HITS.inc();
                timer.observe_duration();

                packet.answers = answers.clone();
                packet.header.qr = 1;
                packet.header.ra = 1;
                packet.header.ancount = packet.answers.len() as u16;
                client_socket_ref
                    .send_to(&packet.to_bytes(), source)
                    .await?;
                continue;
            } else {
                cache_ref.remove(&packet.questions[0]);
            }
        }
        CACHE_MISSES.inc();

        let original_id = packet.header.packet_id;
        transaction_id = transaction_id.wrapping_add(1);
        let new_id = transaction_id;

        {
            let mut pending_map = pending.lock().unwrap();
            pending_map.insert(new_id, (source, original_id, Instant::now()));
        }

        packet.header.packet_id = new_id;

        resolver_socket_ref
            .send_to(&packet.to_bytes(), "1.1.1.1:53")
            .await
            .unwrap();
    }
}

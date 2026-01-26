use lazy_static::lazy_static;
use prometheus::{Counter, Histogram, register_counter, register_histogram};
use std::sync::Mutex;
use std::collections::VecDeque;

lazy_static! {
    pub static ref CACHE_HITS: Counter =
        register_counter!("dns_cache_hits", "Number of cache hits").unwrap();
    pub static ref CACHE_MISSES: Counter =
        register_counter!("dns_cache_misses", "Number of cache misses").unwrap();
    pub static ref RESPONSE_TIME: Histogram =
        register_histogram!("dns_response_time_seconds", "Response time in seconds").unwrap();
    pub static ref BLOCKED_REQUESTS: Counter =
        register_counter!("dns_blocked_requests", "Number of blocked DNS requests").unwrap();
    pub static ref RECENT_LATENCIES: Mutex<VecDeque<u64>> = Mutex::new(VecDeque::with_capacity(100));
}

pub fn record_latency(latency_ms: u64) {
    if let Ok(mut latencies) = RECENT_LATENCIES.lock() {
        if latencies.len() >= 100 {
            latencies.pop_front();
        }
        latencies.push_back(latency_ms);
    }
}

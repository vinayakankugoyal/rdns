//! Prometheus metrics and a small in-memory latency ring buffer for the TUI.

use prometheus::{Counter, Histogram, register_counter, register_histogram};
use std::collections::VecDeque;
use std::sync::{LazyLock, Mutex};

/// Number of recent latency samples retained for the TUI chart.
const RECENT_LATENCY_CAPACITY: usize = 100;

pub static CACHE_HITS: LazyLock<Counter> =
    LazyLock::new(|| register_counter!("dns_cache_hits", "Number of cache hits").unwrap());

pub static CACHE_MISSES: LazyLock<Counter> =
    LazyLock::new(|| register_counter!("dns_cache_misses", "Number of cache misses").unwrap());

pub static RESPONSE_TIME: LazyLock<Histogram> = LazyLock::new(|| {
    register_histogram!("dns_response_time_seconds", "Response time in seconds").unwrap()
});

pub static BLOCKED_REQUESTS: LazyLock<Counter> = LazyLock::new(|| {
    register_counter!("dns_blocked_requests", "Number of blocked DNS requests").unwrap()
});

pub static RECENT_LATENCIES: LazyLock<Mutex<VecDeque<u64>>> =
    LazyLock::new(|| Mutex::new(VecDeque::with_capacity(RECENT_LATENCY_CAPACITY)));

/// Records a latency sample for the TUI chart, evicting the oldest once full.
pub fn record_latency(latency_ms: u64) {
    if let Ok(mut latencies) = RECENT_LATENCIES.lock() {
        if latencies.len() >= RECENT_LATENCY_CAPACITY {
            latencies.pop_front();
        }
        latencies.push_back(latency_ms);
    }
}

//! TTL-based cache for DNS responses.
//!
//! What is cached, and for how long, follows RFC 1035 §3.2.1 and RFC 2308:
//!
//! * a NOERROR response with answers lives for its smallest record TTL;
//! * a negative response (NXDOMAIN, or NOERROR with no answers) lives for
//!   `min(SOA TTL, SOA MINIMUM)` and is not cached without an SOA;
//! * truncated responses, error responses (SERVFAIL, REFUSED, …) and
//!   anything with a TTL of 0 are not cached;
//! * a TTL with the top bit set counts as 0 (RFC 2181 §8), so no entry
//!   lives longer than 2³¹ − 1 seconds.
//!
//! An operator-chosen minimum lifetime (`--min-cache-ttl`) can extend how
//! long entries are kept, but records are always served with their
//! *remaining* TTL, saturating at 0, so downstream caches never hold them
//! longer than the authority allowed.

use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
    time::{Duration, Instant},
};

use crate::packet::{Answer, DNSPacket, Question, RCODE_NOERROR, RCODE_NXDOMAIN};

/// The parts of an upstream response the cache replays.
#[derive(Debug)]
pub struct CachedResponse {
    pub rcode: u8,
    pub answers: Vec<Answer>,
    /// For negative responses, the SOA that bounds the negative TTL.
    pub authorities: Vec<Answer>,
}

struct CacheEntry {
    response: Arc<CachedResponse>,
    inserted: Instant,
    expiration: Instant,
}

/// A cache lookup result: the response plus how long it has been cached,
/// which callers subtract from every TTL they serve.
pub struct CacheHit {
    pub response: Arc<CachedResponse>,
    /// Seconds since insertion, rounded up.
    pub age: u32,
}

/// A thread-safe DNS response cache keyed by question.
///
/// Responses are stored behind an `Arc` so lookups hand out a cheap
/// reference instead of cloning every record.
pub struct DNSCache {
    store: RwLock<HashMap<Question, CacheEntry>>,
    /// Minimum time (seconds) an entry is kept, regardless of record TTLs.
    min_ttl: u32,
}

/// How long `response` may be cached, or `None` if it must not be.
pub fn cache_ttl(response: &DNSPacket) -> Option<u32> {
    if response.header.tc == 1 {
        return None;
    }
    let ttl = match response.header.rcode {
        RCODE_NOERROR if !response.answers.is_empty() => {
            response.answers.iter().map(|a| received_ttl(a.ttl)).min()?
        }
        RCODE_NOERROR | RCODE_NXDOMAIN => {
            let soa = response
                .authorities
                .iter()
                .find_map(|a| Some((a.ttl, a.soa_minimum()?)))?;
            received_ttl(soa.0).min(received_ttl(soa.1))
        }
        _ => return None,
    };
    (ttl > 0).then_some(ttl)
}

/// A TTL as received: values with the top bit set count as 0 (RFC 2181
/// §8: "Implementations should treat TTL values received with the most
/// significant bit set as if the entire value received was zero").
fn received_ttl(ttl: u32) -> u32 {
    if ttl >= 0x8000_0000 { 0 } else { ttl }
}

impl DNSCache {
    pub fn new(min_ttl: u32) -> Self {
        Self {
            store: RwLock::new(HashMap::new()),
            min_ttl,
        }
    }

    /// Returns the cached response for `q`, if present and not expired.
    pub fn get(&self, q: &Question) -> Option<CacheHit> {
        self.get_at(q, Instant::now())
    }

    fn get_at(&self, q: &Question, now: Instant) -> Option<CacheHit> {
        let cache = self.store.read().unwrap();
        let entry = cache.get(q).filter(|entry| entry.expiration > now)?;
        let age = now.saturating_duration_since(entry.inserted);
        let age = age.as_secs() + u64::from(age.subsec_nanos() > 0);
        Some(CacheHit {
            response: Arc::clone(&entry.response),
            age: u32::try_from(age).unwrap_or(u32::MAX),
        })
    }

    /// Caches `response` under `q` if [`cache_ttl`] allows it. Returns
    /// whether it was cached.
    pub fn insert(&self, q: Question, response: DNSPacket) -> bool {
        self.insert_at(q, response, Instant::now())
    }

    fn insert_at(&self, q: Question, response: DNSPacket, now: Instant) -> bool {
        let Some(ttl) = cache_ttl(&response) else {
            return false;
        };
        let negative = response.answers.is_empty();
        let authorities = if negative {
            response
                .authorities
                .into_iter()
                .filter(|a| a.soa_minimum().is_some())
                .collect()
        } else {
            Vec::new()
        };
        let entry = CacheEntry {
            response: Arc::new(CachedResponse {
                rcode: response.header.rcode,
                answers: response.answers,
                authorities,
            }),
            inserted: now,
            expiration: now + Duration::from_secs(ttl.max(self.min_ttl).into()),
        };
        self.store.write().unwrap().insert(q, entry);
        true
    }

    /// Drops every entry that has expired as of `now`.
    pub fn cleanup(&self, now: Instant) {
        self.store
            .write()
            .unwrap()
            .retain(|_, entry| entry.expiration > now);
    }
}

#[cfg(test)]
#[path = "spec/cache_spec.rs"]
mod spec;

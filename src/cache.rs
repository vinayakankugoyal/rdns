//! TTL-based cache for DNS responses.

use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
    time::{Duration, Instant},
};

use crate::packet::{Answer, Question};

/// Minimum time (seconds) an entry stays cached, regardless of record TTLs.
const MIN_CACHE_TTL: u32 = 300;

/// TTL assumed for responses that carry no answers.
const DEFAULT_CACHE_TTL: u32 = 300;

struct CacheEntry {
    answers: Arc<[Answer]>,
    expiration: Instant,
}

/// A thread-safe DNS response cache keyed by question.
///
/// Answers are stored behind an `Arc` so lookups hand out a cheap reference
/// instead of cloning every record.
pub struct DNSCache {
    store: RwLock<HashMap<Question, CacheEntry>>,
}

impl DNSCache {
    pub fn new() -> Self {
        Self {
            store: RwLock::new(HashMap::new()),
        }
    }

    /// Returns the cached answers for `q`, if present and not expired.
    pub fn get(&self, q: &Question) -> Option<Arc<[Answer]>> {
        let cache = self.store.read().unwrap();
        cache
            .get(q)
            .filter(|entry| entry.expiration > Instant::now())
            .map(|entry| Arc::clone(&entry.answers))
    }

    /// Caches `answers` for `q`, expiring after the smallest record TTL
    /// (clamped to at least [`MIN_CACHE_TTL`]).
    pub fn insert(&self, q: Question, answers: Vec<Answer>) {
        let min_ttl = answers
            .iter()
            .map(|a| a.ttl)
            .min()
            .unwrap_or(DEFAULT_CACHE_TTL);
        let effective_ttl = min_ttl.max(MIN_CACHE_TTL);

        let entry = CacheEntry {
            answers: answers.into(),
            expiration: Instant::now() + Duration::from_secs(effective_ttl.into()),
        };
        self.store.write().unwrap().insert(q, entry);
    }

    /// Drops every entry that has expired as of `now`.
    pub fn cleanup(&self, now: Instant) {
        self.store
            .write()
            .unwrap()
            .retain(|_, entry| entry.expiration > now);
    }
}

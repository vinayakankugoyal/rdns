use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
    time::{Duration, Instant},
};

use crate::packet::{Answer, Question};

struct CacheEntry {
    answers: Vec<Answer>,
    expiration: Instant,
}

pub struct DNSCache {
    store: Arc<RwLock<HashMap<Question, CacheEntry>>>,
}

impl DNSCache {
    pub fn new() -> Self {
        Self {
            store: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub fn get(&self, q: &Question) -> Option<Vec<Answer>> {
        let cache = self.store.read().unwrap();
        if let Some(entry) = cache.get(q) {
            if entry.expiration > Instant::now() {
                return Some(entry.answers.clone());
            }
        }
        None
    }

    pub fn insert(&self, q: Question, answers: Vec<Answer>) {
        let mut cache = self.store.write().unwrap();

        let min_ttl = answers.iter().map(|a| a.ttl).min().unwrap_or(300);
        let effective_ttl = std::cmp::max(min_ttl, 300);

        cache.insert(
            q,
            CacheEntry {
                answers,
                expiration: Instant::now() + Duration::from_secs(effective_ttl as u64),
            },
        );
    }

    pub fn cleanup(&self, expiration: Instant) {
        let mut cache = self.store.write().unwrap();
        cache.retain(|_, entry| entry.expiration > expiration);
    }
}

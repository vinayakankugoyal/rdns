use std::{
    collections::HashSet,
    sync::{Arc, RwLock},
};

use crate::packet::Question;

pub struct DNSBlocklist {
    store: Arc<RwLock<HashSet<String>>>,
}

impl DNSBlocklist {
    pub fn new() -> Self {
        Self {
            store: Arc::new(RwLock::new(HashSet::new())),
        }
    }

    pub async fn update(&self) {
        let url = "https://raw.githubusercontent.com/StevenBlack/hosts/master/hosts";

        match reqwest::get(url).await {
            Ok(res) => {
                if let Ok(body) = res.text().await {
                    let mut new_domains = HashSet::new();
                    for line in body.lines() {
                        let line = line.trim();
                        if line.is_empty() || line.starts_with('#') {
                            continue;
                        }
                        // Hosts file format: 0.0.0.0 domain.com
                        let parts: Vec<&str> = line.split_whitespace().collect();
                        if parts.len() >= 2 && parts[0] == "0.0.0.0" {
                            new_domains.insert(parts[1].to_string());
                        }
                    }
                    let mut store = self.store.write().unwrap();
                    *store = new_domains;
                }
            }
            Err(_) => {
            }
        }
    }

    pub fn contains(&self, q: &Question) -> bool {
        let blocklist = self.store.read().unwrap();
        return blocklist.contains(&q.to_string().replace("question=", ""));
    }

    pub fn len(&self) -> usize {
        let blocklist = self.store.read().unwrap();
        blocklist.len()
    }
}

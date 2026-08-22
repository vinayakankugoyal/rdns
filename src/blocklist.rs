//! Domain blocklist sourced from a hosts-file style URL.

use std::{collections::HashSet, sync::RwLock};

/// URL of the hosts-format blocklist to download.
const BLOCKLIST_URL: &str = "https://raw.githubusercontent.com/StevenBlack/hosts/master/hosts";

/// A thread-safe set of blocked domain names.
pub struct DNSBlocklist {
    store: RwLock<HashSet<String>>,
}

impl DNSBlocklist {
    pub fn new() -> Self {
        Self {
            store: RwLock::new(HashSet::new()),
        }
    }

    /// Downloads the blocklist and replaces the current set of domains.
    ///
    /// Returns the number of domains loaded.
    pub async fn update(&self) -> Result<usize, reqwest::Error> {
        let body = reqwest::get(BLOCKLIST_URL).await?.text().await?;

        let new_domains: HashSet<String> = body
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .filter_map(|line| {
                // Hosts file format: `0.0.0.0 domain.com`
                let mut parts = line.split_whitespace();
                match (parts.next(), parts.next()) {
                    (Some("0.0.0.0"), Some(domain)) => Some(domain.to_string()),
                    _ => None,
                }
            })
            .collect();

        let count = new_domains.len();
        *self.store.write().unwrap() = new_domains;
        Ok(count)
    }

    /// Returns whether `domain` (dotted presentation form) is blocked.
    pub fn contains(&self, domain: &str) -> bool {
        self.store.read().unwrap().contains(domain)
    }

    /// Returns the number of blocked domains.
    pub fn len(&self) -> usize {
        self.store.read().unwrap().len()
    }
}

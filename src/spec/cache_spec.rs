//! Executable specification of the response cache (see `spec/SPEC.md`).

use super::*;

fn answer(ttl: u32) -> Answer {
    Answer {
        name: vec![
            7, b'e', b'x', b'a', b'm', b'p', b'l', b'e', 3, b'c', b'o', b'm', 0,
        ],
        tp: 1,
        class: 1,
        ttl,
        length: 4,
        data: vec![1, 2, 3, 4],
    }
}

fn question() -> Question {
    Question {
        name: answer(0).name,
        tp: 1,
        class: 1,
    }
}

/// C1. get(insert(q, a)) = a while the entry is live.          holds
#[test]
fn c1_insert_then_get() {
    let c = DNSCache::new();
    c.insert(question(), vec![answer(600)]);
    let got = c.get(&question()).unwrap();
    assert_eq!(got.len(), 1);
    assert_eq!(got[0].data, [1, 2, 3, 4]);
}

/// C2. cleanup(now) removes exactly the entries with expiration ≤ now. holds
#[test]
fn c2_cleanup_removes_only_expired() {
    let c = DNSCache::new();
    c.insert(question(), vec![answer(600)]);
    c.cleanup(Instant::now());
    assert!(c.get(&question()).is_some());
    c.cleanup(Instant::now() + Duration::from_secs(601));
    assert!(c.store.read().unwrap().is_empty());
}

/// C3. A record served from the cache never claims to be valid for longer
/// than the cache will keep it: served TTL ≤ remaining lifetime.
///
/// Fails: `get` hands back the TTL the record arrived with. After 599 s of
/// a 600 s entry, a client is still told "cache this for 600 s", so
/// downstream caches hold the record up to twice as long as the authority
/// allowed (and indefinitely longer across chained caches).
#[test]
#[ignore = "bug: cached answers are served with their original, undecremented TTL"]
fn c3_counterexample_served_ttl_not_decremented() {
    let c = DNSCache::new();
    c.insert(question(), vec![answer(600)]);
    // Fast-forward: the entry has 1 second left to live.
    let deadline = Instant::now() + Duration::from_secs(1);
    c.store
        .write()
        .unwrap()
        .get_mut(&question())
        .unwrap()
        .expiration = deadline;

    let served = c.get(&question()).unwrap();
    let remaining = deadline.saturating_duration_since(Instant::now()).as_secs();
    assert!(
        served[0].ttl as u64 <= remaining,
        "served ttl {} > remaining lifetime {remaining}s",
        served[0].ttl
    );
}

/// C4. A TTL-0 record is not served from the cache (RFC 1035 §3.2.1:
/// "zero values are interpreted to mean that the RR can only be used for
/// the transaction in progress, and should not be cached").
///
/// Fails by design today (MIN_CACHE_TTL clamps every entry to ≥ 300 s);
/// recorded so the decision is explicit. Combined with C3 the client is
/// also told TTL 0 while getting a 5-minute-old answer.
#[test]
#[ignore = "bug: TTL-0 / short-TTL records are cached for at least 300s"]
fn c4_counterexample_ttl_zero_is_cached() {
    let c = DNSCache::new();
    c.insert(question(), vec![answer(0)]);
    assert!(c.get(&question()).is_none());
}

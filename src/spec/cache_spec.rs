//! Executable specification of the response cache (see `docs/SPEC.md`).

use super::*;

const NXDOMAIN_FLAGS: u16 = 0x8183;
const NOERROR_FLAGS: u16 = 0x8180;

fn wire(name: &str) -> Vec<u8> {
    let mut out = Vec::new();
    for label in name.split('.').filter(|l| !l.is_empty()) {
        out.push(label.len() as u8);
        out.extend_from_slice(label.as_bytes());
    }
    out.push(0);
    out
}

/// A response for `name` with `flags`, A records with the given TTLs, and
/// optionally an SOA (with that TTL and MINIMUM) in the authority section.
fn response(name: &str, flags: u16, ttls: &[u32], soa: Option<(u32, u32)>) -> DNSPacket {
    let mut m = Vec::new();
    for v in [0x1234, flags, 1, ttls.len() as u16, soa.is_some() as u16, 0] {
        m.extend(u16::to_be_bytes(v));
    }
    m.extend(wire(name));
    m.extend([0, 1, 0, 1]);
    for ttl in ttls {
        m.extend([0xC0, 12, 0, 1, 0, 1]);
        m.extend(ttl.to_be_bytes());
        m.extend([0, 4, 1, 2, 3, 4]);
    }
    if let Some((ttl, minimum)) = soa {
        m.extend([0xC0, 12, 0, 6, 0, 1]);
        m.extend(ttl.to_be_bytes());
        m.extend([0, 22, 0, 0]); // RDLENGTH 22: MNAME ".", RNAME "."
        m.extend([0; 16]);
        m.extend(minimum.to_be_bytes());
    }
    DNSPacket::from_bytes(&m).expect("test response must be well formed")
}

fn question(name: &str) -> Question {
    Question {
        name: wire(name),
        tp: 1,
        class: 1,
    }
}

/// C1. get(insert(q, r)) replays r's answers while the entry is live.
#[test]
fn c1_insert_then_get() {
    let c = DNSCache::new(0);
    assert!(c.insert(
        question("example.com"),
        response("example.com", NOERROR_FLAGS, &[600], None)
    ));
    let hit = c.get(&question("example.com")).unwrap();
    assert_eq!(hit.response.rcode, RCODE_NOERROR);
    assert_eq!(hit.response.answers[0].data, [1, 2, 3, 4]);
}

/// C2. cleanup(now) removes exactly the entries with expiration ≤ now.
#[test]
fn c2_cleanup_removes_only_expired() {
    let c = DNSCache::new(0);
    let t0 = Instant::now();
    c.insert_at(
        question("a.test"),
        response("a.test", NOERROR_FLAGS, &[60], None),
        t0,
    );
    c.insert_at(
        question("b.test"),
        response("b.test", NOERROR_FLAGS, &[600], None),
        t0,
    );
    c.cleanup(t0 + Duration::from_secs(60));
    let store = c.store.read().unwrap();
    assert!(!store.contains_key(&question("a.test")));
    assert!(store.contains_key(&question("b.test")));
}

/// C3. Served TTL ≤ remaining lifetime of the entry, for every age and
/// every minimum TTL setting. Regression for #13.
#[test]
fn c3_served_ttl_never_exceeds_remaining_lifetime_exhaustive() {
    for min_ttl in [0, 300, 1000] {
        let c = DNSCache::new(min_ttl);
        let t0 = Instant::now();
        c.insert_at(
            question("example.com"),
            response("example.com", NOERROR_FLAGS, &[600], None),
            t0,
        );
        let lifetime = Duration::from_secs(600u64.max(min_ttl.into()));
        for ms in (0..=1_100_000).step_by(250) {
            let now = t0 + Duration::from_millis(ms);
            let hit = c.get_at(&question("example.com"), now);
            assert_eq!(
                hit.is_some(),
                now < t0 + lifetime,
                "min_ttl={min_ttl} t={ms}ms"
            );
            if let Some(hit) = hit {
                let served = hit.response.answers[0].ttl.saturating_sub(hit.age);
                let remaining = (t0 + lifetime).duration_since(now).as_secs_f64();
                assert!(
                    f64::from(served) <= remaining,
                    "min_ttl={min_ttl} t={ms}ms: served {served} > remaining {remaining}"
                );
            }
        }
    }
}

/// C3, per record: in an entry whose records have different TTLs, every
/// record served at time `t` with TTL `s` is dropped downstream by
/// `max(t, its own expiry)`, for every age and minimum TTL setting. The
/// test above only inserts one record. Regression for #24, which found
/// that C3's earlier wording ("every served TTL ≤ the entry's remaining
/// lifetime") is false for such entries; the last assertion keeps that
/// counterexample.
#[test]
fn c3_records_never_outlive_their_ttl_exhaustive() {
    let ttls = [60, 3600, 600];
    for min_ttl in [0, 300, 1000] {
        let c = DNSCache::new(min_ttl);
        let t0 = Instant::now();
        c.insert_at(
            question("example.com"),
            response("example.com", NOERROR_FLAGS, &ttls, None),
            t0,
        );
        let lifetime = Duration::from_secs(60u64.max(min_ttl.into()));
        for ms in (0..=4_000_000).step_by(250) {
            let t = Duration::from_millis(ms);
            let hit = c.get_at(&question("example.com"), t0 + t);
            assert_eq!(hit.is_some(), t < lifetime, "min_ttl={min_ttl} t={ms}ms");
            let Some(hit) = hit else { continue };
            for a in &hit.response.answers {
                let served = Duration::from_secs(a.ttl.saturating_sub(hit.age).into());
                let expiry = Duration::from_secs(a.ttl.into());
                assert!(
                    t + served <= t.max(expiry),
                    "min_ttl={min_ttl} t={ms}ms: TTL {} record held until {:?}",
                    a.ttl,
                    t + served
                );
            }
        }
    }
    // The old wording's counterexample: at t = 0 the entry has 60 s left,
    // but the 3600 s record is (rightly) served with TTL 3600.
    let c = DNSCache::new(0);
    let t0 = Instant::now();
    c.insert_at(
        question("example.com"),
        response("example.com", NOERROR_FLAGS, &ttls, None),
        t0,
    );
    let hit = c.get_at(&question("example.com"), t0).unwrap();
    assert!(hit.response.answers.iter().any(|a| a.ttl > 60));
}

/// C4. The cache-lifetime policy (RFC 1035 §3.2.1, RFC 2308). Regression
/// for #11, #12 and #13.
#[test]
fn c4_cache_ttl_policy() {
    let ok = NOERROR_FLAGS;
    let cases: &[(&str, DNSPacket, Option<u32>)] = &[
        (
            "answers: min TTL",
            response("x.test", ok, &[600, 60, 300], None),
            Some(60),
        ),
        (
            "TTL 0 is not cached",
            response("x.test", ok, &[0], None),
            None,
        ),
        (
            "one TTL 0 is enough",
            response("x.test", ok, &[600, 0], None),
            None,
        ),
        (
            "TC is not cached",
            response("x.test", 0x8380, &[600], None),
            None,
        ),
        (
            "SERVFAIL is not cached",
            response("x.test", 0x8182, &[], None),
            None,
        ),
        (
            "REFUSED is not cached",
            response("x.test", 0x8185, &[], None),
            None,
        ),
        (
            "NXDOMAIN: min(SOA TTL, MINIMUM)",
            response("x.test", NXDOMAIN_FLAGS, &[], Some((3600, 900))),
            Some(900),
        ),
        (
            "NODATA: min(SOA TTL, MINIMUM)",
            response("x.test", ok, &[], Some((120, 900))),
            Some(120),
        ),
        (
            "NXDOMAIN without SOA",
            response("x.test", NXDOMAIN_FLAGS, &[], None),
            None,
        ),
        (
            "NODATA without SOA",
            response("x.test", ok, &[], None),
            None,
        ),
    ];
    for (what, packet, want) in cases {
        assert_eq!(cache_ttl(packet), *want, "{what}");
    }
}

/// C5. A negative entry replays its RCODE and SOA. Regression for #11.
#[test]
fn c5_negative_entries_keep_rcode_and_soa() {
    let c = DNSCache::new(0);
    let r = response("nope.test", NXDOMAIN_FLAGS, &[], Some((3600, 900)));
    assert!(c.insert(question("nope.test"), r));
    let hit = c.get(&question("nope.test")).unwrap();
    assert_eq!(hit.response.rcode, RCODE_NXDOMAIN);
    assert_eq!(hit.response.authorities.len(), 1);
    assert_eq!(hit.response.authorities[0].soa_minimum(), Some(900));
}

/// C6. Lookups ignore the case of the name. Regression for #8.
#[test]
fn c6_lookups_ignore_case() {
    let c = DNSCache::new(0);
    c.insert(
        question("Example.COM"),
        response("Example.COM", NOERROR_FLAGS, &[600], None),
    );
    assert!(c.get(&question("example.com")).is_some());
    assert!(c.get(&question("EXAMPLE.com")).is_some());
}

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
        // A negative answer behind a CNAME: the answer section holds the
        // chain, the authority section the target zone's SOA. Both bound
        // the lifetime (the record type in the answer section doesn't
        // matter to the policy). Regression for #18.
        (
            "NXDOMAIN behind a CNAME: the CNAME's TTL bounds it",
            response("x.test", NXDOMAIN_FLAGS, &[30], Some((3600, 3600))),
            Some(30),
        ),
        (
            "NXDOMAIN behind a CNAME: the negative TTL bounds it",
            response("x.test", NXDOMAIN_FLAGS, &[3600], Some((3600, 60))),
            Some(60),
        ),
        (
            "NXDOMAIN with answers but no SOA",
            response("x.test", NXDOMAIN_FLAGS, &[3600], None),
            None,
        ),
        (
            "NODATA behind a CNAME: the negative TTL bounds it",
            response("x.test", ok, &[3600], Some((60, 60))),
            Some(60),
        ),
        (
            "NODATA behind a CNAME: the CNAME's TTL bounds it",
            response("x.test", ok, &[30], Some((3600, 3600))),
            Some(30),
        ),
        // TTLs with the top bit set count as 0 (RFC 2181 §8). Regression
        // for #21.
        (
            "top bit set: not cached",
            response("x.test", ok, &[0x8000_0000], None),
            None,
        ),
        (
            "one TTL with the top bit is enough",
            response("x.test", ok, &[600, 0xFFFF_FFFF], None),
            None,
        ),
        (
            "2³¹ − 1 is the largest TTL",
            response("x.test", ok, &[0x7FFF_FFFF], None),
            Some(0x7FFF_FFFF),
        ),
        (
            "SOA TTL with the top bit",
            response("x.test", NXDOMAIN_FLAGS, &[], Some((0x8000_0000, 900))),
            None,
        ),
        (
            "SOA MINIMUM with the top bit",
            response("x.test", NXDOMAIN_FLAGS, &[], Some((900, 0xFFFF_FFFF))),
            None,
        ),
        (
            "NXDOMAIN behind a CNAME whose TTL has the top bit",
            response("x.test", NXDOMAIN_FLAGS, &[0x8000_0000], Some((3600, 3600))),
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

/// C5′. A negative answer behind a CNAME keeps its SOA too, and replays
/// its CNAME. Regression for #18.
#[test]
fn c5_cname_negatives_keep_soa() {
    for flags in [NXDOMAIN_FLAGS, NOERROR_FLAGS] {
        let c = DNSCache::new(0);
        let r = response("www.test", flags, &[30], Some((3600, 900)));
        assert!(c.insert(question("www.test"), r));
        let hit = c.get(&question("www.test")).unwrap();
        assert_eq!(hit.response.rcode, flags as u8 & 0x0f);
        assert_eq!(hit.response.answers.len(), 1);
        assert_eq!(hit.response.authorities.len(), 1);
        assert_eq!(hit.response.authorities[0].soa_minimum(), Some(900));
    }
}

/// C7. Nothing stale: without `--min-cache-ttl`, an entry stops being
/// served once any of its records, or its negative TTL, has expired.
/// Regression for #18.
#[test]
fn c7_nothing_served_stale() {
    let cases = [
        response("a.test", NOERROR_FLAGS, &[600, 60], None),
        response("b.test", NXDOMAIN_FLAGS, &[], Some((3600, 900))),
        response("c.test", NXDOMAIN_FLAGS, &[30], Some((3600, 3600))),
        response("d.test", NOERROR_FLAGS, &[3600], Some((60, 60))),
    ];
    for r in cases {
        let q = r.questions[0].clone();
        let deadline = r
            .answers
            .iter()
            .map(|a| a.ttl)
            .chain(
                r.authorities
                    .iter()
                    .map(|a| a.ttl.min(a.soa_minimum().unwrap())),
            )
            .min()
            .unwrap();
        let c = DNSCache::new(0);
        let t0 = Instant::now();
        c.insert_at(q.clone(), r, t0);
        let deadline = t0 + Duration::from_secs(deadline.into());
        assert!(c.get_at(&q, deadline - Duration::from_millis(1)).is_some());
        assert!(c.get_at(&q, deadline).is_none(), "{q} served stale");
    }
}

/// C8. Honest negative TTLs: a downstream resolver given a cached negative
/// answer at any time `t` caches it for `min(served SOA TTL, MINIMUM)`,
/// and that never reaches past the negative TTL `min(SOA TTL, MINIMUM)`
/// set by the authority, whatever `min_cache_ttl` is. Before the fix the
/// SOA was replayed with its full TTL, so at t = 299.5 s an SOA with TTL
/// 3600 and MINIMUM 300 told downstream to keep the NXDOMAIN until
/// t = 599.5 s. Regression for #20.
#[test]
fn c8_negative_ttls_are_honest_exhaustive() {
    for min_ttl in [0, 300, 3600] {
        for (soa_ttl, minimum) in [(3600, 300), (300, 3600), (86400, 60)] {
            let negative_ttl = u64::from(soa_ttl.min(minimum));
            let c = DNSCache::new(min_ttl);
            let t0 = Instant::now();
            let r = response("nope.test", NXDOMAIN_FLAGS, &[], Some((soa_ttl, minimum)));
            c.insert_at(question("nope.test"), r, t0);
            for ms in (0..=4_000_000).step_by(500) {
                let t = Duration::from_millis(ms);
                let Some(hit) = c.get_at(&question("nope.test"), t0 + t) else {
                    continue;
                };
                let soa = &hit.response.authorities[0];
                let served = soa.ttl.saturating_sub(hit.age);
                let held = u64::from(served.min(soa.soa_minimum().unwrap()));
                let until = t + Duration::from_secs(held);
                assert!(
                    until <= t.max(Duration::from_secs(negative_ttl)),
                    "min_ttl={min_ttl} soa=({soa_ttl},{minimum}) t={ms}ms: held until {until:?}"
                );
            }
        }
    }
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

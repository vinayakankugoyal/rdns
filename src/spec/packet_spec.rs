//! Executable specification of the DNS wire codec (see `docs/SPEC.md`).
//!
//! Each test checks one property from the spec. A test whose name ends in
//! `_exhaustive` covers the property's whole input domain; the others use a
//! seeded generator ("bounded"), so every run checks the same cases.

use super::*;

// ---------------------------------------------------------------------------
// Test-only helpers
// ---------------------------------------------------------------------------

/// Deterministic xorshift64* PRNG, so every run checks the same cases.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn byte(&mut self) -> u8 {
        self.next() as u8
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Encodes a dotted name as uncompressed wire format.
fn wire(name: &str) -> Vec<u8> {
    let mut out = Vec::new();
    for label in name.split('.').filter(|l| !l.is_empty()) {
        out.push(label.len() as u8);
        out.extend_from_slice(label.as_bytes());
    }
    out.push(0);
    out
}

fn header(id: u16, flags: u16, qd: u16, an: u16, ns: u16, ar: u16) -> Vec<u8> {
    [id, flags, qd, an, ns, ar]
        .iter()
        .flat_map(|v| v.to_be_bytes())
        .collect()
}

/// A query for `name` with the given type, class IN.
fn query(name: &str, tp: u16) -> Vec<u8> {
    let mut p = header(0x1234, 0x0100, 1, 0, 0, 0);
    p.extend(wire(name));
    p.extend(tp.to_be_bytes());
    p.extend(1u16.to_be_bytes());
    p
}

/// Spec predicate WF(name): a domain name in uncompressed wire format is a
/// sequence of labels of length 1..=63 terminated by the root label, at
/// most 255 bytes in total (RFC 1035 §3.1, §2.3.4).
fn well_formed_name(name: &[u8]) -> bool {
    let mut i = 0;
    while i < name.len() {
        let len = name[i] as usize;
        if len == 0 {
            return i + 1 == name.len() && name.len() <= 255;
        }
        if len > 63 || i + 1 + len > name.len() {
            return false;
        }
        i += 1 + len;
    }
    false
}

/// Reference decoder: the name at `off` as RFC 1035 §4.1.4 defines it,
/// with loops cut off by a hop limit. The parser must agree with it on
/// every name it accepts.
fn reference_name(buf: &[u8], mut off: usize) -> Option<Vec<u8>> {
    let mut out = Vec::new();
    let mut hops = 0;
    loop {
        let b = *buf.get(off)?;
        if b & 0xC0 == 0xC0 {
            hops += 1;
            if hops > 127 {
                return None;
            }
            off = ((b as usize & 0x3F) << 8) | *buf.get(off + 1)? as usize;
        } else if b & 0xC0 != 0 {
            return None;
        } else if b == 0 {
            out.push(0);
            return Some(out);
        } else {
            let l = b as usize;
            out.extend_from_slice(buf.get(off..off + 1 + l)?);
            off += 1 + l;
        }
    }
}

/// Re-runs the test named `child` in a fresh process and reports whether
/// it exited normally. Rust aborts the whole process on stack overflow
/// instead of panicking, so a regression to unbounded recursion can only be
/// observed cleanly from outside.
fn child_exits_cleanly(child: &str) -> bool {
    std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", child, "--nocapture", "--test-threads=1"])
        .env("RDNS_SPEC_CHILD", "1")
        .output()
        .unwrap()
        .status
        .success()
}

// ---------------------------------------------------------------------------
// H1. The header codec is a bijection on 12-byte strings.
// ---------------------------------------------------------------------------

/// ∀ b ∈ Byte¹², write(read(b)) = b. The only bytes the codec transforms
/// are the two flag bytes, so every value of those is checked (2¹⁶ cases),
/// with random values for the rest.
#[test]
fn h1_header_roundtrip_exhaustive() {
    let mut rng = Rng(0xD15EA5E);
    for flags in 0..=u16::MAX {
        let mut b = [0u8; HEADER_LEN];
        for x in b.iter_mut() {
            *x = rng.byte();
        }
        b[2..4].copy_from_slice(&flags.to_be_bytes());
        let mut out = Vec::new();
        Header::from_bytes(&b).write_to(&mut out);
        assert_eq!(out, b, "flags={flags:#06x}");
    }
}

// ---------------------------------------------------------------------------
// P1. Parsing is total: from_bytes terminates on every input.
// ---------------------------------------------------------------------------

/// Bounded check over random inputs, compression pointers included.
#[test]
fn p1_parser_total_on_random_inputs() {
    let mut rng = Rng(42);
    for _ in 0..50_000 {
        let len = rng.below(80);
        let mut b: Vec<u8> = (0..len).map(|_| rng.byte()).collect();
        if b.len() >= HEADER_LEN {
            // Keep counts small so the body gets parsed.
            b[4] = 0;
            b[5] = rng.byte() % 4;
            b[6] = 0;
            b[7] = rng.byte() % 4;
        }
        let _ = DNSPacket::from_bytes(&b);
    }
}

/// Regression for #3: names whose pointers form a cycle, either a pointer
/// to itself or a label followed by a pointer back to that label. Run in a
/// child process so a regression fails the test instead of aborting the
/// test harness.
#[test]
fn p1_pointer_cycles_terminate() {
    assert!(
        child_exits_cleanly("packet::spec::p1_child_parse_pointer_cycles"),
        "parsing a compression-pointer cycle aborted the process"
    );
}

/// Body of the test above; a no-op unless run as its child.
#[test]
fn p1_child_parse_pointer_cycles() {
    if std::env::var_os("RDNS_SPEC_CHILD").is_none() {
        return;
    }
    let cycles: [&[u8]; 3] = [
        &[0xC0, 0x0C],                // pointer to itself
        &[1, b'a', 0xC0, 0x0C],       // label, then pointer back to it
        &[0xC0, 0x0E, 0xC0, 0x0C, 0], // two pointers pointing at each other
    ];
    for name in cycles {
        let mut pkt = header(1, 0x0100, 1, 0, 0, 0);
        pkt.extend(name);
        pkt.extend([0, 1, 0, 1]);
        assert!(DNSPacket::from_bytes(&pkt).is_none());
    }
}

// ---------------------------------------------------------------------------
// P2. Soundness: every name the parser accepts is well formed and equals
//     the reference decoding.
// ---------------------------------------------------------------------------

#[test]
fn p2_parsed_names_are_sound() {
    let mut rng = Rng(7);
    for _ in 0..200_000 {
        let mut b = header(1, 0x0100, 1, 0, 0, 0);
        let len = rng.below(24);
        b.extend((0..len).map(|_| match rng.below(4) {
            0 => 0xC0 | rng.byte() & 0x01,
            1 => rng.byte(),
            _ => rng.byte() % 8,
        }));
        let Some(p) = DNSPacket::from_bytes(&b) else {
            continue;
        };
        let q = &p.questions[0];
        assert!(well_formed_name(&q.name), "input={b:02x?}");
        assert_eq!(
            Some(q.name.clone()),
            reference_name(&b, HEADER_LEN),
            "input={b:02x?}"
        );
    }
}

/// Regression for #4: a label that runs past the end of the message, and a
/// pointer past the end, are rejected rather than decoded partially.
#[test]
fn p2_truncated_names_rejected() {
    for body in [&[5, b'a', b'b', b'c', b'd'][..], &[0xC0, 0xFF, 0, 1, 0, 1]] {
        let mut b = header(1, 0x0100, 1, 0, 0, 0);
        b.extend(body);
        assert!(DNSPacket::from_bytes(&b).is_none(), "accepted {b:02x?}");
    }
}

/// Names longer than 255 bytes are rejected.
#[test]
fn p2_overlong_names_rejected() {
    let mut b = header(1, 0x0100, 1, 0, 0, 0);
    // 4 labels of 63 bytes = 256 bytes before the root.
    for _ in 0..4 {
        b.push(63);
        b.extend([b'a'; 63]);
    }
    b.extend([0, 0, 1, 0, 1]);
    assert!(DNSPacket::from_bytes(&b).is_none());
}

// ---------------------------------------------------------------------------
// P3. Completeness: every well-formed, backward-compressed message parses,
//     and its names decode to what was encoded.
// ---------------------------------------------------------------------------

#[test]
fn p3_well_formed_messages_parse() {
    let mut rng = Rng(11);
    for _ in 0..5_000 {
        // Random names over a tiny alphabet, so suffixes repeat and get
        // compressed.
        let names: Vec<String> = (0..1 + rng.below(4))
            .map(|_| {
                (0..1 + rng.below(4))
                    .map(|_| ["a", "bb", "ccc", "example", "com"][rng.below(5)])
                    .collect::<Vec<_>>()
                    .join(".")
            })
            .collect();
        let mut m = header(1, 0x8180, names.len() as u16, 0, 0, 0);
        let mut seen: Vec<(String, usize)> = Vec::new();
        for name in &names {
            // Compress against the longest suffix written so far.
            let labels: Vec<&str> = name.split('.').collect();
            let mut i = 0;
            while i < labels.len() {
                let suffix = labels[i..].join(".");
                if let Some((_, off)) = seen.iter().find(|(s, _)| *s == suffix) {
                    m.extend([0xC0 | (off >> 8) as u8, *off as u8]);
                    break;
                }
                seen.push((suffix, m.len()));
                m.push(labels[i].len() as u8);
                m.extend(labels[i].as_bytes());
                i += 1;
            }
            if i == labels.len() {
                m.push(0);
            }
            m.extend([0, 1, 0, 1]);
        }
        let p = DNSPacket::from_bytes(&m).unwrap_or_else(|| panic!("rejected {m:02x?}"));
        for (q, name) in p.questions.iter().zip(&names) {
            assert_eq!(q.name, wire(name));
        }
    }
}

// ---------------------------------------------------------------------------
// P4. Records are self-contained: RDATA that holds names is decompressed,
//     so a record copied into a new message (as the cache does) decodes to
//     the same thing.
// ---------------------------------------------------------------------------

/// Regression for #5: an NXDOMAIN response whose SOA has an RNAME that
/// points into its own MNAME.
#[test]
fn p4_soa_rdata_is_self_contained() {
    let mut m = header(9, 0x8183, 1, 0, 1, 0);
    m.extend(wire("nope.example.com")); // "example.com" at offset 17
    m.extend([0, 1, 0, 1]);
    let rdata_start = m.len() + 12;
    m.extend([0xC0, 17, 0, 6, 0, 1, 0, 0, 0x0E, 0x10]);
    let mut rdata = vec![3, b'n', b's', b'1', 0xC0, 17]; // ns1.example.com
    rdata.push(10);
    rdata.extend(b"hostmaster");
    rdata.extend([0xC0, rdata_start as u8 + 4]); // -> "example.com" via MNAME
    rdata.extend([0; 20]);
    m.extend((rdata.len() as u16).to_be_bytes());
    m.extend(&rdata);

    let original = DNSPacket::from_bytes(&m).unwrap();
    let mut want = wire("ns1.example.com");
    want.extend(wire("hostmaster.example.com"));
    want.extend([0; 20]);
    assert_eq!(original.authorities[0].data, want);

    // Copy the SOA into a brand-new message, as a cache hit does.
    let q = DNSPacket::from_bytes(&query("nope.example.com", 1)).unwrap();
    let copy = q.response_bytes(RCODE_NXDOMAIN, &[], &original.authorities, 0);
    let copy = DNSPacket::from_bytes(&copy).unwrap();
    assert_eq!(copy.authorities[0].data, want);
}

/// MX, SRV, CNAME: the name part is decompressed and fixed parts kept.
#[test]
fn p4_name_bearing_rdata_is_decompressed() {
    let mut m = header(9, 0x8180, 1, 3, 0, 0);
    m.extend(wire("example.com"));
    m.extend([0, 15, 0, 1]);
    m.extend([0xC0, 12, 0, 5, 0, 1, 0, 0, 0, 60, 0, 2, 0xC0, 12]); // CNAME
    m.extend([0xC0, 12, 0, 15, 0, 1, 0, 0, 0, 60, 0, 7, 0, 10]); // MX 10
    m.extend([2, b'm', b'x', 0xC0, 12]);
    m.extend([0xC0, 12, 0, 33, 0, 1, 0, 0, 0, 60, 0, 8, 0, 1, 0, 2, 0, 53]); // SRV
    m.extend([0xC0, 12]);
    let p = DNSPacket::from_bytes(&m).unwrap();
    assert_eq!(p.answers[0].data, wire("example.com"));
    assert_eq!(
        p.answers[1].data,
        [&[0, 10][..], &wire("mx.example.com")].concat()
    );
    assert_eq!(
        p.answers[2].data,
        [&[0, 1, 0, 2, 0, 53][..], &wire("example.com")].concat()
    );
}

/// RDATA whose fields don't exactly fill RDLENGTH is rejected.
#[test]
fn p4_rdata_length_mismatch_rejected() {
    let mut m = header(9, 0x8180, 1, 1, 0, 0);
    m.extend(wire("example.com"));
    m.extend([0, 5, 0, 1]);
    // CNAME claims 3 bytes of RDATA but holds a 2-byte pointer.
    m.extend([0xC0, 12, 0, 5, 0, 1, 0, 0, 0, 60, 0, 3, 0xC0, 12, 0]);
    assert!(DNSPacket::from_bytes(&m).is_none());
}

// ---------------------------------------------------------------------------
// P5. Truncated messages are rejected, not decoded partially.
// ---------------------------------------------------------------------------

/// Regression for #6: every proper prefix of a valid response is rejected.
#[test]
fn p5_truncated_sections_rejected_exhaustive() {
    let mut m = header(9, 0x8180, 1, 2, 0, 0);
    m.extend(wire("example.com"));
    m.extend([0, 1, 0, 1]);
    m.extend([0xC0, 12, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 1, 2, 3, 4]);
    m.extend([0xC0, 12, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 5, 6, 7, 8]);
    assert!(DNSPacket::from_bytes(&m).is_some());
    for cut in 0..m.len() {
        assert!(
            DNSPacket::from_bytes(&m[..cut]).is_none(),
            "accepted a {cut}-byte prefix"
        );
    }
}

// ---------------------------------------------------------------------------
// B1. Synthesized blocked answers are well typed.
// ---------------------------------------------------------------------------

/// Regression for #7: A gets 0.0.0.0, AAAA gets ::, and every other type
/// gets no record (an empty NOERROR) instead of A-shaped data.
#[test]
fn b1_blocked_answers_are_well_typed_exhaustive() {
    let p = DNSPacket::from_bytes(&query("ads.example.com", 1)).unwrap();
    for tp in 0..=u16::MAX {
        let q = Question {
            tp,
            ..p.questions[0].clone()
        };
        match (tp, q.to_blocked_answer()) {
            (TYPE_A, Some(a)) => assert_eq!(a.data, [0; 4]),
            (TYPE_AAAA, Some(a)) => assert_eq!(a.data, [0; 16]),
            (TYPE_A | TYPE_AAAA, None) => panic!("type {tp}: no answer"),
            (_, None) => {}
            (_, Some(a)) => panic!("type {tp}: {a:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// R1. A synthesized response answers the query: same ID and question,
//     QR=1, RCODE as given, counts equal to the records written.
// R2. Served TTLs are aged: each TTL is reduced by `age`, saturating at 0.
// R3. The truncated form is a TC=1 response with no records.
// ---------------------------------------------------------------------------

#[test]
fn r1_response_bytes_shape() {
    let mut rng = Rng(99);
    for _ in 0..2_000 {
        let mut q = query("example.com", 1);
        q[0] = rng.byte();
        q[1] = rng.byte();
        let p = DNSPacket::from_bytes(&q).unwrap();
        let n = rng.below(5);
        let rcode = rng.byte() & 0x0f;
        let answers: Vec<_> = (0..n)
            .map(|_| p.questions[0].to_blocked_answer().unwrap())
            .collect();
        let r = DNSPacket::from_bytes(&p.response_bytes(rcode, &answers, &[], 0)).unwrap();
        assert_eq!(r.header.packet_id, p.header.packet_id);
        assert_eq!((r.header.qr, r.header.rcode, r.header.tc), (1, rcode, 0));
        assert_eq!(r.answers.len(), n);
        assert_eq!(r.header.ancount as usize, n);
        assert_eq!((r.header.nscount, r.header.arcount), (0, 0));
        assert_eq!(r.questions, p.questions);
    }
}

/// R5. A response to a query with an OPT record carries one: root owner,
/// the UDP size rdns accepts, version 0, and the query's DO bit; a query
/// without OPT gets none (RFC 6891 §7). Holds for answers, errors and the
/// truncated form. Regression for #23.
#[test]
fn r5_opt_echoed() {
    for (opt_ttl, has_opt) in [(None, false), (Some(0u32), true), (Some(0x8000), true)] {
        let mut q = query("example.com", 1);
        if let Some(ttl) = opt_ttl {
            q[11] = 1; // ARCOUNT = 1
            q.extend([0, 0, 41, 0x04, 0xD0]); // root, OPT, payload 1232
            q.extend(ttl.to_be_bytes());
            q.extend([0, 0]);
        }
        let p = DNSPacket::from_bytes(&q).unwrap();
        let answers = [p.questions[0].to_blocked_answer().unwrap()];
        for bytes in [
            p.response_bytes(RCODE_NOERROR, &answers, &[], 0),
            p.response_bytes(RCODE_SERVFAIL, &[], &[], 0),
            p.truncated_bytes(RCODE_NOERROR),
        ] {
            let r = DNSPacket::from_bytes(&bytes).expect("response must parse");
            assert_eq!(r.header.arcount, u16::from(has_opt));
            match (r.resources.as_slice(), opt_ttl) {
                ([], None) => {}
                ([opt], Some(ttl)) => {
                    assert_eq!((opt.name.as_slice(), opt.tp), (&[0u8][..], TYPE_OPT));
                    assert_eq!(opt.class as usize, MAX_UDP_PAYLOAD);
                    assert_eq!(opt.ttl, ttl & 0x8000, "DO not copied, or version/RCODE set");
                    assert!(opt.data.is_empty());
                }
                (rs, _) => panic!("unexpected additional section {rs:?}"),
            }
        }
    }
}

#[test]
fn r2_ttls_are_aged() {
    let p = DNSPacket::from_bytes(&query("example.com", 1)).unwrap();
    let a = p.questions[0].to_blocked_answer().unwrap();
    for age in (0..=700).chain([u32::MAX]) {
        let bytes = p.response_bytes(0, std::slice::from_ref(&a), &[], age);
        let r = DNSPacket::from_bytes(&bytes).unwrap();
        assert_eq!(r.answers[0].ttl, a.ttl.saturating_sub(age));
    }
}

#[test]
fn r3_truncated_bytes_shape() {
    let p = DNSPacket::from_bytes(&query("example.com", 1)).unwrap();
    let r = DNSPacket::from_bytes(&p.truncated_bytes(RCODE_NOERROR)).unwrap();
    assert_eq!((r.header.qr, r.header.tc), (1, 1));
    assert!(r.answers.is_empty());
    assert_eq!(r.questions, p.questions);
}

// ---------------------------------------------------------------------------
// E1. The client's UDP size limit is its EDNS payload size, clamped to
//     [512, 4096], or 512 without EDNS.
// ---------------------------------------------------------------------------

#[test]
fn e1_udp_payload_limit() {
    let plain = DNSPacket::from_bytes(&query("example.com", 1)).unwrap();
    assert_eq!(plain.udp_payload_limit(), 512);
    for (advertised, want) in [(0u16, 512), (1232, 1232), (4096, 4096), (65535, 4096)] {
        let mut q = query("example.com", 1);
        q[11] = 1; // ARCOUNT = 1
        q.extend([0, 0, 41]); // root owner, type OPT
        q.extend(advertised.to_be_bytes()); // CLASS = payload size
        q.extend([0, 0, 0, 0, 0, 0]); // TTL, RDLENGTH = 0
        let p = DNSPacket::from_bytes(&q).unwrap();
        assert_eq!(p.udp_payload_limit(), want);
    }
}

// ---------------------------------------------------------------------------
// Q1. Question equality ignores ASCII case in the name (RFC 4343), and
//     hashing agrees with equality.
// ---------------------------------------------------------------------------

#[test]
fn q1_question_equality_ignores_case() {
    use std::collections::hash_map::DefaultHasher;
    let hash = |q: &Question| {
        let mut h = DefaultHasher::new();
        q.hash(&mut h);
        h.finish()
    };
    let a = DNSPacket::from_bytes(&query("Example.COM", 1)).unwrap();
    let b = DNSPacket::from_bytes(&query("example.com", 1)).unwrap();
    let c = DNSPacket::from_bytes(&query("example.com", 28)).unwrap();
    assert_eq!(a.questions[0], b.questions[0]);
    assert_eq!(hash(&a.questions[0]), hash(&b.questions[0]));
    assert_ne!(b.questions[0], c.questions[0]);
}

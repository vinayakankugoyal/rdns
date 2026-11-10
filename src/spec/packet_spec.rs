//! Executable specification of the DNS wire codec (see `spec/SPEC.md`).
//!
//! Each `#[test]` checks one property from the spec. Properties checked
//! over their whole input domain say "exhaustive"; the rest use a seeded
//! generator ("bounded"). A property the code currently violates is marked
//! `#[ignore]` with the issue that tracks it, so `cargo test` stays green
//! and `cargo test -- --ignored` reproduces every open counterexample.

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

/// Wire-format RDATA length each record type must have, where fixed.
fn fixed_rdlength(tp: u16) -> Option<usize> {
    match tp {
        1 => Some(4),   // A
        28 => Some(16), // AAAA
        _ => None,
    }
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

/// Resolves a (possibly compressed) name at `off` in `buf` the way RFC 1035
/// §4.1.4 defines it, rejecting loops. This is the reference the parser is
/// compared against.
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
/// it exited normally. Stack overflow aborts the whole process rather than
/// panicking, so non-termination of the parser can only be observed from
/// outside.
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
// H1. Header codec is a bijection on 12-byte strings.   STATUS: holds
// ---------------------------------------------------------------------------

/// ∀ b ∈ Byte¹², write(read(b)) = b.
///
/// The only bytes the codec transforms are the two flag bytes (2 and 3);
/// the rest are copied as big-endian u16s. We check every value of the
/// flag bytes exhaustively (2¹⁶ cases) against random values for the rest.
#[test]
fn h1_header_roundtrip_exhaustive_over_flags() {
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

/// Bounded check over random inputs *without* compression pointers that
/// loop. Holds: absent a pointer cycle, every step of `qname` advances.
#[test]
fn p1_parser_total_on_random_acyclic_inputs() {
    let mut rng = Rng(42);
    for _ in 0..20_000 {
        let len = rng.below(80);
        let mut b: Vec<u8> = (0..len).map(|_| rng.byte()).collect();
        // Clear the pointer tag everywhere so no pointer can form a cycle.
        for x in b.iter_mut().skip(HEADER_LEN) {
            if *x & 0xC0 == 0xC0 {
                *x &= 0x3F;
            }
        }
        let _ = DNSPacket::from_bytes(&b);
    }
}

/// Counterexample: a 14-byte query whose name is a pointer to itself.
/// `qname` follows it forever and overflows the stack, which aborts the
/// whole process. Any client that can reach the port can send this.
#[test]
#[ignore = "bug: compression-pointer loop overflows the stack (crashes the server)"]
fn p1_counterexample_self_pointer() {
    assert!(
        child_exits_cleanly("packet::spec::p1_child_parse_self_pointer"),
        "parsing a self-referencing pointer aborted the process"
    );
}

/// Body of the counterexample above; a no-op unless run as its child.
#[test]
fn p1_child_parse_self_pointer() {
    if std::env::var_os("RDNS_SPEC_CHILD").is_none() {
        return;
    }
    let mut pkt = header(1, 0x0100, 1, 0, 0, 0);
    pkt.extend([0xC0, 0x0C]); // pointer to offset 12, i.e. to itself
    let _ = DNSPacket::from_bytes(&pkt);
}

// ---------------------------------------------------------------------------
// P2. Parsed names are well formed: WF(q.name) for every parsed question.
// ---------------------------------------------------------------------------

/// Holds for names that are actually complete in the buffer.
#[test]
fn p2_complete_names_are_well_formed() {
    for name in ["a", "example.com", "x.y.z.w", "localhost"] {
        let p = DNSPacket::from_bytes(&query(name, 1)).unwrap();
        assert!(well_formed_name(&p.questions[0].name));
        assert_eq!(p.questions[0].name, wire(name));
    }
}

/// Bounded check: whenever the parser returns a question, its name agrees
/// with the RFC 1035 reference resolver (and so is terminated by the root
/// label). Fails: when the name is truncated or a pointer target is out of
/// range, `qname` returns a prefix with no terminator and the parser goes
/// on to read TYPE/CLASS from whatever bytes follow.
#[test]
#[ignore = "bug: truncated / dangling names are accepted as questions"]
fn p2_parsed_names_match_reference() {
    let mut rng = Rng(7);
    for _ in 0..50_000 {
        let mut b = header(1, 0x0100, 1, 0, 0, 0);
        let len = rng.below(24);
        b.extend((0..len).map(|_| rng.byte() & 0x3F | (rng.byte() & 0x80)));
        // Drop cycles: they are P1's business.
        if (HEADER_LEN..b.len()).any(|i| b[i] & 0xC0 == 0xC0) {
            continue;
        }
        let Some(p) = DNSPacket::from_bytes(&b) else {
            continue;
        };
        for q in &p.questions {
            assert_eq!(
                Some(q.name.clone()),
                reference_name(&b, HEADER_LEN),
                "input={b:02x?}"
            );
        }
    }
}

/// A concrete witness for the above: the label says 5 bytes follow but the
/// packet ends after 4 more. The parser reports a question with an empty,
/// unterminated name and type/class taken from the label's bytes.
#[test]
#[ignore = "bug: truncated / dangling names are accepted as questions"]
fn p2_counterexample_truncated_label() {
    let mut b = header(1, 0x0100, 1, 0, 0, 0);
    b.extend([5, b'a', b'b', b'c', b'd']);
    let p = DNSPacket::from_bytes(&b).unwrap();
    assert!(
        p.questions.iter().all(|q| well_formed_name(&q.name)),
        "parsed {:?}",
        p.questions
    );
}

// ---------------------------------------------------------------------------
// P3. Re-serialization is faithful: for a well-formed message m,
//     parse(to_bytes(parse(m))) ≡ parse(m)   (records compared after
//     decompression, against the reference resolver).
// ---------------------------------------------------------------------------

/// Holds for messages whose only compressed names are owner names and
/// NS/CNAME/PTR/MX RDATA — the types the parser decompresses.
#[test]
fn p3_roundtrip_with_decompressed_types() {
    let mut m = header(9, 0x8180, 1, 2, 0, 0);
    m.extend(wire("www.example.com"));
    m.extend([0, 5, 0, 1]);
    // CNAME www.example.com -> example.com (compressed, points at offset 16)
    m.extend([0xC0, 12, 0, 5, 0, 1, 0, 0, 0, 60, 0, 2, 0xC0, 16]);
    // A example.com 93.184.216.34
    m.extend([0xC0, 16, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 93, 184, 216, 34]);

    let p = DNSPacket::from_bytes(&m).unwrap();
    let q = DNSPacket::from_bytes(&p.to_bytes()).unwrap();
    assert_eq!(q.answers.len(), 2);
    assert_eq!(q.answers[0].data, wire("example.com"));
    assert_eq!(q.answers[1].name, wire("example.com"));
    assert_eq!(q.answers[1].data, [93, 184, 216, 34]);
}

/// Counterexample: an NXDOMAIN response with an SOA in the authority
/// section. SOA RDATA holds two compressed names but is copied verbatim,
/// while the owner name before it is expanded from a 2-byte pointer to the
/// full name. Every pointer in the SOA that targets bytes at or after the
/// expanded name now lands in the wrong place.
#[test]
#[ignore = "bug: SOA (and other un-decompressed RDATA) pointers are corrupted on relay"]
fn p3_counterexample_soa_pointers_shift() {
    let mut m = header(9, 0x8183, 1, 0, 1, 0); // NXDOMAIN
    m.extend(wire("nope.example.com")); // offset 12..30, "example.com" at 17
    m.extend([0, 1, 0, 1]);
    // Authority: owner = pointer to "example.com" (offset 17).
    let soa_rdata_start = m.len() + 12;
    m.extend([0xC0, 17, 0, 6, 0, 1, 0, 0, 0x0E, 0x10]);
    let mut rdata = Vec::new();
    rdata.extend([3, b'n', b's', b'1', 0xC0, 17]); // MNAME ns1.example.com
    // RNAME hostmaster + pointer back into MNAME's suffix, i.e. a pointer
    // into this very record (the common "compress against earlier RDATA").
    rdata.extend([10]);
    rdata.extend(b"hostmaster");
    rdata.extend([0xC0, soa_rdata_start as u8 + 4]);
    rdata.extend([0; 20]); // SERIAL..MINIMUM
    m.extend((rdata.len() as u16).to_be_bytes());
    m.extend(&rdata);

    let original = DNSPacket::from_bytes(&m).unwrap();
    let relayed_bytes = original.to_bytes();
    let relayed = DNSPacket::from_bytes(&relayed_bytes).unwrap();
    let soa = &relayed.authorities[0];
    let rdata_off = relayed_bytes.len() - soa.data.len();
    let mname = reference_name(&relayed_bytes, rdata_off);
    let rname = reference_name(&relayed_bytes, rdata_off + 6);
    assert_eq!(mname, Some(wire("ns1.example.com")));
    assert_eq!(rname, Some(wire("hostmaster.example.com")));
}

/// Header counts agree with section lengths after relay. Fails: when the
/// parser stops early (truncated message, e.g. a >512-byte response cut by
/// the receive buffer), `to_bytes` still writes the *original* counts.
#[test]
#[ignore = "bug: relayed header counts can disagree with the records written"]
fn p3_counterexample_counts_disagree_after_truncation() {
    let mut m = header(9, 0x8180, 1, 2, 0, 0);
    m.extend(wire("example.com"));
    m.extend([0, 1, 0, 1]);
    m.extend([0xC0, 12, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 1, 2, 3, 4]);
    m.extend([0xC0, 12, 0, 1, 0, 1, 0, 0]); // second record cut short

    let p = DNSPacket::from_bytes(&m).unwrap();
    assert_eq!(p.answers.len(), 1);
    let out = p.to_bytes();
    let ancount = u16::from_be_bytes([out[6], out[7]]) as usize;
    assert_eq!(ancount, p.answers.len());
}

// ---------------------------------------------------------------------------
// B1. Synthesized blocked answers are well typed: if the RR type has a
//     fixed RDATA size, rdlength equals it.
// ---------------------------------------------------------------------------

#[test]
fn b1_blocked_answer_for_a_is_well_typed() {
    let p = DNSPacket::from_bytes(&query("ads.example.com", 1)).unwrap();
    let a = p.questions[0].to_blocked_answer();
    assert_eq!(a.data.len(), 4);
    assert_eq!(a.length as usize, a.data.len());
}

/// Counterexample: an AAAA (type 28) query for a blocked name gets an AAAA
/// record carrying 4 bytes of RDATA. AAAA RDATA is 16 bytes (RFC 3596), so
/// the response is malformed. MX, TXT, HTTPS, … get the same 4 zero bytes.
#[test]
#[ignore = "bug: blocked AAAA/MX/TXT/... queries get malformed 4-byte RDATA"]
fn b1_counterexample_blocked_aaaa() {
    for tp in [28u16, 15, 16, 65] {
        let p = DNSPacket::from_bytes(&query("ads.example.com", tp)).unwrap();
        let a = p.questions[0].to_blocked_answer();
        if a.tp == tp {
            match fixed_rdlength(tp) {
                Some(n) => assert_eq!(a.data.len(), n, "type {tp}"),
                None => panic!("type {tp}: answered with A-shaped RDATA {:?}", a.data),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// R1. A synthesized response answers the query: same ID and question,
//     QR=1, ANCOUNT = |answers|, NS/ARCOUNT = 0.          STATUS: holds
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
        let answers: Vec<_> = (0..n).map(|_| p.questions[0].to_blocked_answer()).collect();
        let r = DNSPacket::from_bytes(&p.response_bytes(&answers)).unwrap();
        assert_eq!(r.header.packet_id, p.header.packet_id);
        assert_eq!(r.header.qr, 1);
        assert_eq!(r.answers.len(), n);
        assert_eq!(r.header.ancount as usize, n);
        assert_eq!((r.header.nscount, r.header.arcount), (0, 0));
        assert_eq!(r.questions, p.questions);
    }
}

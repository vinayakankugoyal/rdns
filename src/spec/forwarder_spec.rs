//! End-to-end specification of the forwarder (see `docs/SPEC.md`).
//!
//! Each test runs the real request handler on loopback sockets against a
//! scripted fake upstream resolver and a fake client.

use super::*;
use crate::packet::{RCODE_NXDOMAIN, TYPE_AAAA};

fn wire(name: &str) -> Vec<u8> {
    let mut out = Vec::new();
    for label in name.split('.').filter(|l| !l.is_empty()) {
        out.push(label.len() as u8);
        out.extend_from_slice(label.as_bytes());
    }
    out.push(0);
    out
}

/// A message with one question (`name`, type A) followed by `body`.
fn message(id: u16, flags: u16, [an, ns, ar]: [u16; 3], name: &str, body: &[u8]) -> Vec<u8> {
    let mut m = Vec::new();
    for v in [id, flags, 1, an, ns, ar] {
        m.extend(v.to_be_bytes());
    }
    m.extend(wire(name));
    m.extend([0, 1, 0, 1]);
    m.extend(body);
    m
}

fn query(id: u16, name: &str) -> Vec<u8> {
    message(id, 0x0100, [0, 0, 0], name, &[])
}

/// A query carrying an EDNS OPT record advertising `size` bytes.
fn edns_query(id: u16, name: &str, size: u16) -> Vec<u8> {
    let mut opt = vec![0, 0, 41];
    opt.extend(size.to_be_bytes());
    opt.extend([0, 0, 0, 0, 0, 0]);
    message(id, 0x0100, [0, 0, 1], name, &opt)
}

/// An A record whose owner is a pointer to the question name.
fn a_record(ttl: u32, ip: [u8; 4]) -> Vec<u8> {
    let mut r = vec![0xC0, 12, 0, 1, 0, 1];
    r.extend(ttl.to_be_bytes());
    r.extend([0, 4]);
    r.extend(ip);
    r
}

/// An SOA record (owner = question name) with the given TTL and MINIMUM,
/// whose RNAME is compressed against its MNAME. `at` is the record's
/// offset in the message.
fn soa_record(at: usize, ttl: u32, minimum: u32) -> Vec<u8> {
    let mut r = vec![0xC0, 12, 0, 6, 0, 1];
    r.extend(ttl.to_be_bytes());
    let mut rdata = vec![3, b'n', b's', b'1', 0xC0, 12];
    rdata.extend([10]);
    rdata.extend(b"hostmaster");
    rdata.extend([0xC0, (at + 12 + 4) as u8]);
    rdata.extend([0; 16]);
    rdata.extend(minimum.to_be_bytes());
    r.extend((rdata.len() as u16).to_be_bytes());
    r.extend(rdata);
    r
}

fn id_of(m: &[u8]) -> u16 {
    u16::from_be_bytes([m[0], m[1]])
}

fn rcode_of(m: &[u8]) -> u8 {
    m[3] & 0x0F
}

fn tc_of(m: &[u8]) -> bool {
    m[2] & 0x02 != 0
}

/// A query the fake upstream received, and where it came from.
struct Upstream {
    query: Vec<u8>,
    from: SocketAddr,
}

struct Harness {
    server: Arc<Server>,
    upstream: UdpSocket,
    client: UdpSocket,
}

impl Harness {
    async fn new() -> Self {
        let upstream = UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let (log_tx, _) = broadcast::channel(LOG_CHANNEL_CAPACITY);
        let server = Arc::new(Server {
            client_socket: UdpSocket::bind("127.0.0.1:0").await.unwrap(),
            resolver_addr: upstream.local_addr().unwrap(),
            upstream_timeout: Duration::from_millis(300),
            cache: DNSCache::new(0),
            blocklist: Arc::new(DNSBlocklist::new()),
            log_tx,
        });
        let client = UdpSocket::bind("127.0.0.1:0").await.unwrap();
        Self {
            server,
            upstream,
            client,
        }
    }

    /// Sends `q` from the client. The handler runs in the background.
    fn ask(&self, q: Vec<u8>) {
        let src = self.client.local_addr().unwrap();
        tokio::spawn(handle_dns_request(Arc::clone(&self.server), q, src));
    }

    /// Sends `q` from the client and returns the query the upstream saw.
    async fn forward(&self, q: Vec<u8>) -> Upstream {
        self.ask(q);
        self.upstream_recv().await
    }

    async fn upstream_recv(&self) -> Upstream {
        let mut buf = [0u8; 4096];
        let (n, from) =
            tokio::time::timeout(Duration::from_secs(2), self.upstream.recv_from(&mut buf))
                .await
                .expect("upstream got no query")
                .unwrap();
        Upstream {
            query: buf[..n].to_vec(),
            from,
        }
    }

    /// Replies as the upstream resolver.
    async fn reply(&self, to: &Upstream, bytes: &[u8]) {
        self.upstream.send_to(bytes, to.from).await.unwrap();
    }

    async fn client_recv(&self) -> Vec<u8> {
        let mut buf = [0u8; 8192];
        let (n, _) = tokio::time::timeout(Duration::from_secs(2), self.client.recv_from(&mut buf))
            .await
            .expect("client got no response")
            .unwrap();
        buf[..n].to_vec()
    }

    /// Whether the upstream receives anything within a short window.
    async fn upstream_is_quiet(&self) -> bool {
        let mut buf = [0u8; 4096];
        tokio::time::timeout(
            Duration::from_millis(100),
            self.upstream.recv_from(&mut buf),
        )
        .await
        .is_err()
    }
}

/// F0. A forwarded answer reaches the client with the client's ID, and the
/// next identical query is answered from the cache.
#[tokio::test]
async fn f0_forward_then_cache_hit() {
    let h = Harness::new().await;
    let up = h.forward(query(0xBEEF, "example.com")).await;
    let id = id_of(&up.query);
    h.reply(
        &up,
        &message(
            id,
            0x8180,
            [1, 0, 0],
            "example.com",
            &a_record(600, [93, 184, 216, 34]),
        ),
    )
    .await;
    let r = h.client_recv().await;
    assert_eq!(id_of(&r), 0xBEEF);
    assert!(r.ends_with(&[93, 184, 216, 34]));

    h.ask(query(0xCAFE, "Example.COM"));
    let cached = h.client_recv().await;
    assert!(h.upstream_is_quiet().await, "cache hit went upstream");
    assert_eq!(id_of(&cached), 0xCAFE);
    assert!(cached.ends_with(&[93, 184, 216, 34]));
}

/// F1. An upstream reply is accepted only if its ID *and* question match
/// the query; anything else is ignored and never cached. Regression for #9.
#[tokio::test]
async fn f1_mismatched_replies_ignored() {
    let h = Harness::new().await;
    let up = h.forward(query(1, "a.test")).await;
    let id = id_of(&up.query);

    // Right ID, wrong question; then wrong ID, right question.
    h.reply(
        &up,
        &message(
            id,
            0x8180,
            [1, 0, 0],
            "other.test",
            &a_record(600, [6, 6, 6, 6]),
        ),
    )
    .await;
    h.reply(
        &up,
        &message(
            id ^ 1,
            0x8180,
            [1, 0, 0],
            "a.test",
            &a_record(600, [6, 6, 6, 6]),
        ),
    )
    .await;
    // Then the genuine reply.
    h.reply(
        &up,
        &message(
            id,
            0x8180,
            [1, 0, 0],
            "a.test",
            &a_record(600, [1, 1, 1, 1]),
        ),
    )
    .await;

    let r = h.client_recv().await;
    assert!(r.ends_with(&[1, 1, 1, 1]), "client got {r:02x?}");
    let other = Question {
        name: wire("other.test"),
        tp: 1,
        class: 1,
    };
    assert!(
        h.server.cache.get(&other, false).is_none(),
        "unasked question was cached"
    );
}

/// F1′. Forwarded transaction IDs are unpredictable: consecutive IDs are
/// far apart. For uniformly random IDs, a gap of 256 or less has
/// probability 513/65536 < 1%, so seeing it in more than half of 31 gaps
/// is vanishingly unlikely. A counter, even one shared with other
/// concurrent queries, produces small gaps every time.
#[tokio::test]
async fn f1_transaction_ids_are_unpredictable() {
    let h = Harness::new().await;
    let mut ids = Vec::new();
    for i in 0..32 {
        ids.push(id_of(
            &h.forward(query(0, &format!("q{i}.test"))).await.query,
        ));
    }
    let small_gaps = ids
        .windows(2)
        .filter(|w| {
            let d = w[1].wrapping_sub(w[0]);
            d.min(d.wrapping_neg()) <= 256
        })
        .count();
    assert!(small_gaps <= 15, "IDs look sequential: {ids:?}");
}

/// F2. Every query gets an answer: if the upstream never replies, the
/// client gets SERVFAIL after the timeout. Regression for #10.
#[tokio::test]
async fn f2_unanswered_queries_get_servfail() {
    let h = Harness::new().await;
    let _ = h.forward(query(42, "silent.test")).await;
    let r = h.client_recv().await;
    assert_eq!(id_of(&r), 42);
    assert_eq!(rcode_of(&r), RCODE_SERVFAIL);
}

/// F2′. Concurrent queries answered out of order each get their own answer.
#[tokio::test]
async fn f2_concurrent_queries_are_kept_apart() {
    let h = Harness::new().await;
    let a = h.forward(query(1, "a.test")).await;
    let b = h.forward(query(2, "b.test")).await;
    h.reply(
        &b,
        &message(
            id_of(&b.query),
            0x8180,
            [1, 0, 0],
            "b.test",
            &a_record(60, [2, 2, 2, 2]),
        ),
    )
    .await;
    h.reply(
        &a,
        &message(
            id_of(&a.query),
            0x8180,
            [1, 0, 0],
            "a.test",
            &a_record(60, [1, 1, 1, 1]),
        ),
    )
    .await;
    let mut got = [h.client_recv().await, h.client_recv().await];
    got.sort_by_key(|r| id_of(r));
    assert!(got[0].ends_with(&[1, 1, 1, 1]));
    assert!(got[1].ends_with(&[2, 2, 2, 2]));
}

/// F3. A negative answer replays with its RCODE and SOA; errors are not
/// cached. Regression for #11.
#[tokio::test]
async fn f3_negative_answers_keep_rcode_and_errors_are_not_cached() {
    let h = Harness::new().await;
    let up = h.forward(query(7, "nope.test")).await;
    let body_at = message(0, 0, [0, 0, 0], "nope.test", &[]).len();
    let nx = message(
        id_of(&up.query),
        0x8183,
        [0, 1, 0],
        "nope.test",
        &soa_record(body_at, 3600, 900),
    );
    h.reply(&up, &nx).await;
    assert_eq!(rcode_of(&h.client_recv().await), RCODE_NXDOMAIN);

    h.ask(query(8, "nope.test"));
    let cached = h.client_recv().await;
    assert!(
        h.upstream_is_quiet().await,
        "negative answer was not cached"
    );
    assert_eq!(rcode_of(&cached), RCODE_NXDOMAIN);
    let cached = DNSPacket::from_bytes(&cached).unwrap();
    assert_eq!(cached.authorities[0].soa_minimum(), Some(900));

    // SERVFAIL is relayed but not cached: the next query goes upstream.
    let up = h.forward(query(9, "broken.test")).await;
    h.reply(
        &up,
        &message(id_of(&up.query), 0x8182, [0, 0, 0], "broken.test", &[]),
    )
    .await;
    assert_eq!(rcode_of(&h.client_recv().await), RCODE_SERVFAIL);
    let _ = h.forward(query(10, "broken.test")).await;
}

/// F4. A TC=1 response is relayed with TC=1 and not cached. Regression
/// for #12.
#[tokio::test]
async fn f4_truncated_responses_relayed_not_cached() {
    let h = Harness::new().await;
    let up = h.forward(query(7, "big.test")).await;
    h.reply(
        &up,
        &message(
            id_of(&up.query),
            0x8380,
            [1, 0, 0],
            "big.test",
            &a_record(600, [10, 0, 0, 1]),
        ),
    )
    .await;
    assert!(tc_of(&h.client_recv().await));
    let _ = h.forward(query(8, "big.test")).await; // went upstream again
}

/// F5. A relayed response fits the client's UDP limit: if it doesn't, the
/// client gets TC=1 instead of a silently cut message. Clients that
/// advertise a larger EDNS size get the full response. Regression for #6.
#[tokio::test]
async fn f5_large_responses_respect_client_limit() {
    // (query, records in the reply, client limit, whole reply fits?)
    // 40 A records ≈ 650 bytes; 300 ≈ 4.8 KB, more than rdns ever sends.
    let cases = [
        (query(1, "many.test"), 40u16, 512, false),
        (edns_query(2, "many.test", 4096), 40, 4096, true),
        (edns_query(3, "many.test", 65535), 300, 4096, false),
    ];
    for (q, n, limit, fits) in cases {
        let body: Vec<u8> = (0..n)
            .flat_map(|i| a_record(600, [10, 0, (i >> 8) as u8, i as u8]))
            .collect();
        let h = Harness::new().await;
        let up = h.forward(q).await;
        h.reply(
            &up,
            &message(id_of(&up.query), 0x8180, [n, 0, 0], "many.test", &body),
        )
        .await;
        let r = h.client_recv().await;
        let p = DNSPacket::from_bytes(&r).expect("relayed response must be well formed");
        assert!(r.len() <= limit, "{} bytes > limit {limit}", r.len());
        if fits {
            assert!(!tc_of(&r));
            assert_eq!(p.answers.len(), n as usize);
        } else {
            assert!(tc_of(&r), "{n} records: expected TC");
            assert!(p.answers.is_empty());
        }
    }
}

/// F6. A relayed response is byte-for-byte the upstream's, apart from the
/// ID, so record types rdns doesn't understand pass through intact.
/// Regression for #5.
#[tokio::test]
async fn f6_relay_is_verbatim() {
    let h = Harness::new().await;
    let up = h.forward(query(0x0102, "nope.test")).await;
    let body_at = message(0, 0, [0, 0, 0], "nope.test", &[]).len();
    let nx = message(
        id_of(&up.query),
        0x8183,
        [0, 1, 0],
        "nope.test",
        &soa_record(body_at, 3600, 900),
    );
    h.reply(&up, &nx).await;
    let r = h.client_recv().await;
    assert_eq!(id_of(&r), 0x0102);
    assert_eq!(r[2..], nx[2..]);
}

/// A query with an OPT record setting DO.
fn do_query(id: u16, name: &str) -> Vec<u8> {
    let mut opt = vec![0, 0, 41, 0x04, 0xD0];
    opt.extend([0, 0, 0x80, 0, 0, 0]); // ext RCODE, version, DO, Z; RDLENGTH 0
    message(id, 0x0100, [0, 0, 1], name, &opt)
}

/// F9. DO isolation: a DO=0 client never gets the RRSIGs fetched for a
/// DO=1 client, and a DO=1 client is never served an answer fetched
/// without them. Regression for #19.
#[tokio::test]
async fn f9_do_answers_are_kept_apart() {
    let h = Harness::new().await;
    let up = h.forward(do_query(1, "signed.test")).await;
    let mut body = a_record(600, [192, 0, 2, 1]);
    body.extend([0xC0, 12, 0, 46, 0, 1, 0, 0, 2, 88, 0, 4, 0, 1, 13, 2]); // RRSIG
    h.reply(
        &up,
        &message(id_of(&up.query), 0x8180, [2, 0, 0], "signed.test", &body),
    )
    .await;
    let r = DNSPacket::from_bytes(&h.client_recv().await).unwrap();
    assert_eq!(r.answers.len(), 2);

    // A DO=0 query isn't answered from the DO=1 entry: it goes upstream.
    let up = h.forward(query(2, "signed.test")).await;
    h.reply(
        &up,
        &message(
            id_of(&up.query),
            0x8180,
            [1, 0, 0],
            "signed.test",
            &a_record(600, [192, 0, 2, 1]),
        ),
    )
    .await;
    let r = DNSPacket::from_bytes(&h.client_recv().await).unwrap();
    assert!(r.answers.iter().all(|a| a.tp != 46), "RRSIG sent to DO=0");

    // Both are now cached, each with its own records.
    h.ask(do_query(3, "signed.test"));
    let r = DNSPacket::from_bytes(&h.client_recv().await).unwrap();
    assert!(h.upstream_is_quiet().await);
    assert_eq!(r.answers.len(), 2);
    h.ask(query(4, "signed.test"));
    let r = DNSPacket::from_bytes(&h.client_recv().await).unwrap();
    assert!(h.upstream_is_quiet().await);
    assert_eq!(r.answers.len(), 1);
}

/// F7. Blocked names are blocked in any case, with a well-typed answer.
/// Regression for #7 and #8.
#[tokio::test]
async fn f7_blocking() {
    let h = Harness::new().await;
    h.server
        .blocklist
        .replace(["ads.example.com".to_string()].into());

    h.ask(query(1, "ADS.Example.com"));
    let r = DNSPacket::from_bytes(&h.client_recv().await).unwrap();
    assert_eq!(r.answers[0].data, [0, 0, 0, 0]);

    let mut aaaa = query(2, "ads.example.com");
    let n = aaaa.len();
    aaaa[n - 3] = TYPE_AAAA as u8;
    h.ask(aaaa);
    let r = DNSPacket::from_bytes(&h.client_recv().await).unwrap();
    assert_eq!(r.answers[0].data, [0; 16]);
    assert!(h.upstream_is_quiet().await, "blocked query went upstream");
}

//! End-to-end specification of the forwarder (see `spec/SPEC.md`).
//!
//! Each test runs a real `Server` on loopback sockets against a scripted
//! fake upstream resolver and a fake client.

use super::*;
use crate::packet::Question;

const RCODE_NXDOMAIN: u16 = 3;

fn wire(name: &str) -> Vec<u8> {
    let mut out = Vec::new();
    for label in name.split('.').filter(|l| !l.is_empty()) {
        out.push(label.len() as u8);
        out.extend_from_slice(label.as_bytes());
    }
    out.push(0);
    out
}

fn message(id: u16, flags: u16, counts: [u16; 4], name: &str, body: &[u8]) -> Vec<u8> {
    let mut m = Vec::new();
    m.extend(id.to_be_bytes());
    m.extend(flags.to_be_bytes());
    m.extend(1u16.to_be_bytes());
    for c in counts.iter().skip(1) {
        m.extend(c.to_be_bytes());
    }
    m.extend(wire(name));
    m.extend([0, 1, 0, 1]); // type A, class IN
    m.extend(body);
    m
}

fn query(id: u16, name: &str) -> Vec<u8> {
    message(id, 0x0100, [1, 0, 0, 0], name, &[])
}

/// An A record whose owner is a pointer to the question name.
fn a_record(ttl: u32, ip: [u8; 4]) -> Vec<u8> {
    let mut r = vec![0xC0, 12, 0, 1, 0, 1];
    r.extend(ttl.to_be_bytes());
    r.extend([0, 4]);
    r.extend(ip);
    r
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
            resolver_socket: UdpSocket::bind("127.0.0.1:0").await.unwrap(),
            resolver_addr: upstream.local_addr().unwrap(),
            cache: DNSCache::new(),
            blocklist: Arc::new(DNSBlocklist::new()),
            pending: Mutex::new(HashMap::new()),
            next_id: AtomicU16::new(0),
            log_tx,
        });
        tokio::spawn(process_resolver_responses(Arc::clone(&server)));
        let client = UdpSocket::bind("127.0.0.1:0").await.unwrap();
        Self {
            server,
            upstream,
            client,
        }
    }

    /// Sends `q` as the client and returns the query the upstream saw.
    async fn forward(&self, q: Vec<u8>) -> Vec<u8> {
        let src = self.client.local_addr().unwrap();
        handle_dns_request(Arc::clone(&self.server), q, src).await;
        let mut buf = [0u8; 2048];
        let (n, _) = self.upstream.recv_from(&mut buf).await.unwrap();
        buf[..n].to_vec()
    }

    /// Replies as the upstream resolver.
    async fn upstream_reply(&self, bytes: &[u8]) {
        let to = self.server.resolver_socket.local_addr().unwrap();
        self.upstream.send_to(bytes, to).await.unwrap();
    }

    async fn client_recv(&self) -> Vec<u8> {
        let mut buf = [0u8; 4096];
        let (n, _) = tokio::time::timeout(Duration::from_secs(2), self.client.recv_from(&mut buf))
            .await
            .expect("client got no response")
            .unwrap();
        buf[..n].to_vec()
    }

    /// Asks a query that will be answered from the cache.
    async fn ask_cached(&self, q: Vec<u8>) -> Vec<u8> {
        let src = self.client.local_addr().unwrap();
        handle_dns_request(Arc::clone(&self.server), q, src).await;
        self.client_recv().await
    }
}

fn id_of(m: &[u8]) -> u16 {
    u16::from_be_bytes([m[0], m[1]])
}

fn rcode_of(m: &[u8]) -> u16 {
    (m[3] & 0x0F) as u16
}

fn question(name: &str) -> Question {
    Question {
        name: wire(name),
        tp: 1,
        class: 1,
    }
}

/// F0. Happy path: a forwarded answer reaches the client with the client's
/// ID and is then served from the cache.                        holds
#[tokio::test]
async fn f0_forward_then_cache_hit() {
    let h = Harness::new().await;
    let up = h.forward(query(0xBEEF, "example.com")).await;
    h.upstream_reply(&message(
        id_of(&up),
        0x8180,
        [1, 1, 0, 0],
        "example.com",
        &a_record(600, [93, 184, 216, 34]),
    ))
    .await;
    let r = h.client_recv().await;
    assert_eq!(id_of(&r), 0xBEEF);
    assert!(r.ends_with(&[93, 184, 216, 34]));

    let cached = h.ask_cached(query(0xCAFE, "example.com")).await;
    assert_eq!(id_of(&cached), 0xCAFE);
    assert!(cached.ends_with(&[93, 184, 216, 34]));
}

/// F1. Responses are only accepted for the question that was asked: an
/// upstream reply is matched to a pending query on (ID, question), and
/// only then cached.
///
/// Fails: matching is on the 16-bit ID alone, and the ID is a counter
/// starting at 0 sent from one fixed source port. Whoever can get a UDP
/// datagram to the resolver socket with the resolver's source address
/// (i.e. an off-path spoofer) can guess the ID and plant any record for
/// any name in the cache — the name in the *response* is what is cached.
#[tokio::test]
#[ignore = "bug: upstream responses matched on predictable ID only; cache poisoning"]
async fn f1_counterexample_cache_poisoning() {
    let h = Harness::new().await;
    // IDs are predictable: 0, 1, 2, ...
    let ids: Vec<u16> = [
        h.forward(query(1, "a.test")).await,
        h.forward(query(2, "b.test")).await,
    ]
    .iter()
    .map(|m| id_of(m))
    .collect();
    assert_eq!(
        ids,
        [0, 1],
        "IDs are a counter from 0, so an attacker can predict them"
    );

    // A forged reply for ID 0 that answers a *different* question.
    let forged = message(
        0,
        0x8180,
        [1, 1, 0, 0],
        "bank.test",
        &a_record(86400, [6, 6, 6, 6]),
    );
    h.upstream_reply(&forged).await;
    let _ = h.client_recv().await;
    assert!(
        h.server.cache.get(&question("bank.test")).is_none(),
        "answer for an unasked question was cached"
    );
}

/// F2. At most one in-flight query per ID; a query is never silently
/// dropped while it is still pending.
///
/// Fails: after 2¹⁶ outstanding queries the counter wraps and `insert`
/// overwrites the oldest pending entry; nothing ever expires entries for
/// queries the upstream never answered, so the map only grows until the
/// IDs collide.
#[tokio::test]
#[ignore = "bug: pending queries never time out and IDs wrap onto in-flight queries"]
async fn f2_counterexample_pending_overwritten() {
    let h = Harness::new().await;
    let src = h.client.local_addr().unwrap();
    for i in 0..=u16::MAX as u32 {
        let name = format!("q{i}.test");
        handle_dns_request(Arc::clone(&h.server), query(0, &name), src).await;
    }
    let pending = h.server.pending.lock().unwrap().len();
    assert_eq!(pending, 65_536);
    // One more: query #65536 reuses ID 0 and evicts query #0.
    handle_dns_request(Arc::clone(&h.server), query(0, "one-more.test"), src).await;
    assert_eq!(
        h.server.pending.lock().unwrap().len(),
        65_537,
        "an in-flight query was overwritten by ID wrap-around"
    );
}

/// F3. A response served from the cache carries the RCODE of the response
/// that was cached (negative caching, RFC 2308).
///
/// Fails: the cache stores only the answer section, and `response_bytes`
/// copies the RCODE from the *query* (0). An NXDOMAIN is therefore cached
/// for 300 s as an empty NOERROR ("NODATA") — and SERVFAIL / REFUSED are
/// cached the same way.
#[tokio::test]
#[ignore = "bug: NXDOMAIN/SERVFAIL are cached and replayed as NOERROR"]
async fn f3_counterexample_nxdomain_becomes_noerror() {
    let h = Harness::new().await;
    let up = h.forward(query(7, "nope.test")).await;
    h.upstream_reply(&message(id_of(&up), 0x8183, [1, 0, 0, 0], "nope.test", &[]))
        .await;
    assert_eq!(rcode_of(&h.client_recv().await), RCODE_NXDOMAIN);

    let cached = h.ask_cached(query(8, "nope.test")).await;
    assert_eq!(
        rcode_of(&cached),
        RCODE_NXDOMAIN,
        "cached NXDOMAIN replayed as rcode {}",
        rcode_of(&cached)
    );
}

/// F4. A truncated (TC=1) upstream response is relayed with TC=1 and not
/// cached as if it were complete.
///
/// Fails: the partial answer set is cached and later served with TC=0, so
/// clients never retry over TCP (which rdns doesn't serve anyway).
#[tokio::test]
#[ignore = "bug: truncated (TC) responses are cached and replayed without TC"]
async fn f4_counterexample_tc_cached() {
    let h = Harness::new().await;
    let up = h.forward(query(7, "big.test")).await;
    h.upstream_reply(&message(
        id_of(&up),
        0x8380, // QR, RD, TC, RA
        [1, 1, 0, 0],
        "big.test",
        &a_record(600, [10, 0, 0, 1]),
    ))
    .await;
    let _ = h.client_recv().await;
    let cached = h.ask_cached(query(8, "big.test")).await;
    assert_eq!(
        cached[2] & 0x02,
        0x02,
        "partial answer served from cache without TC"
    );
}

/// F5. A relayed response is either complete or marked truncated: the
/// client never receives a message whose header promises records that are
/// not there.
///
/// Fails: rdns forwards the client's EDNS OPT record (so the upstream may
/// send up to 4096 bytes) but reads the reply into a 512-byte buffer. The
/// tail is silently cut off, the parser stops early, and `to_bytes` writes
/// the original counts over the shortened record list.
#[tokio::test]
#[ignore = "bug: >512-byte (EDNS) upstream responses are silently cut and relayed malformed"]
async fn f5_counterexample_large_response_cut() {
    let h = Harness::new().await;
    let up = h.forward(query(7, "many.test")).await;
    let n = 40u16; // 40 A records ≈ 650 bytes
    let body: Vec<u8> = (0..n)
        .flat_map(|i| a_record(600, [10, 0, 0, i as u8]))
        .collect();
    h.upstream_reply(&message(
        id_of(&up),
        0x8180,
        [1, n, 0, 0],
        "many.test",
        &body,
    ))
    .await;
    let r = h.client_recv().await;
    let p = DNSPacket::from_bytes(&r).unwrap();
    let tc = r[2] & 0x02 != 0;
    assert!(
        tc || p.answers.len() == p.header.ancount as usize,
        "header says {} answers, message holds {}, TC={tc}",
        p.header.ancount,
        p.answers.len()
    );
}

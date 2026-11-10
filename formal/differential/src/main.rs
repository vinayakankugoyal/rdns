//! Differential test: the Lean model (`formal/Main.lean`) against the real
//! rdns codec and cache policy, on generated messages.
//!
//! ```bash
//! cd formal && lake build rdns-model
//! cd differential && cargo run --release -- 100000
//! ```
//!
//! Prints the first disagreements, if any, and exits non-zero on any.

#![allow(dead_code)]

#[path = "../../../src/packet.rs"]
mod packet;
#[path = "../../../src/cache.rs"]
mod cache;

use packet::{Answer, DNSPacket, Question};
use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};

/// xorshift64*: a fixed-seed generator, so every run checks the same cases.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn byte(&mut self) -> u8 {
        self.next() as u8
    }
    fn chance(&mut self, pct: u64) -> bool {
        self.below(100) < pct
    }
}

const TYPES: &[u16] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 14, 15, 16, 17, 18, 21, 28, 33, 41, 46, 65];

/// A name: labels, possibly ending in a compression pointer (which may
/// point anywhere, including forwards or at itself).
fn name(r: &mut Rng, m: &mut Vec<u8>, starts: &mut Vec<usize>) {
    if r.chance(50) && !starts.is_empty() {
        // A pointer to a name written earlier: valid compression.
        let target = starts[r.below(starts.len() as u64) as usize];
        m.push(0xC0 | (target >> 8) as u8 & 0x3F);
        m.push(target as u8);
        return;
    }
    if m.len() < 0x3FFF {
        starts.push(m.len());
    }
    let labels = r.below(4);
    for _ in 0..labels {
        let len = if r.chance(5) { r.below(64) as usize + 60 } else { r.below(6) as usize + 1 };
        let len = len.min(63);
        m.push(len as u8);
        for _ in 0..len {
            m.push(if r.chance(50) { b'a' + r.below(26) as u8 } else { r.byte() });
        }
    }
    if r.chance(10) && m.len() > 12 {
        let target = if r.chance(85) { 12 + r.below((m.len() - 12) as u64) as usize } else { r.below(m.len() as u64 + 4) as usize };
        m.push(0xC0 | (target >> 8) as u8 & 0x3F);
        m.push(target as u8);
    } else if r.chance(3) {
        m.push(0x40 | r.byte() & 0x3F); // reserved label type
    } else {
        m.push(0);
    }
}

fn record(r: &mut Rng, m: &mut Vec<u8>, s: &mut Vec<usize>, soa: bool) {
    name(r, m, s);
    let tp = if soa { 6 } else if r.chance(90) { TYPES[r.below(TYPES.len() as u64) as usize] } else { r.byte() as u16 };
    m.extend(tp.to_be_bytes());
    let class: u16 = if tp == 41 { [0, 100, 512, 1232, 4096, 9000, 65535][r.below(7) as usize] } else { 1 };
    m.extend(class.to_be_bytes());
    let ttl: u32 = match r.below(5) {
        0 => 0,
        1 => r.below(600) as u32,
        2 => 0x8000_0000 | r.next() as u32,
        _ => r.next() as u32,
    };
    m.extend(ttl.to_be_bytes());
    let len_at = m.len();
    m.extend([0, 0]);
    let start = m.len();
    match tp {
        2 | 3 | 4 | 5 | 7 | 8 | 9 | 12 => name(r, m, s),
        6 => {
            name(r, m, s);
            name(r, m, s);
            for _ in 0..20 {
                m.push(r.byte());
            }
        }
        14 | 17 => {
            name(r, m, s);
            name(r, m, s);
        }
        15 | 18 | 21 => {
            m.extend([r.byte(), r.byte()]);
            name(r, m, s);
        }
        33 => {
            for _ in 0..6 {
                m.push(r.byte());
            }
            name(r, m, s);
        }
        _ => {
            for _ in 0..r.below(20) {
                m.push(r.byte());
            }
        }
    }
    let mut len = (m.len() - start) as i64;
    if r.chance(8) {
        len += r.below(5) as i64 - 2;
    }
    let len = len.clamp(0, 65535) as u16;
    m[len_at..len_at + 2].copy_from_slice(&len.to_be_bytes());
}

fn message(r: &mut Rng) -> Vec<u8> {
    if r.chance(10) {
        return (0..r.below(64)).map(|_| r.byte()).collect();
    }
    let counts = [r.below(2) + u64::from(r.chance(90)), r.below(4), r.below(3), r.below(3)];
    let mut m = Vec::new();
    let mut s = Vec::new();
    m.extend((r.next() as u16).to_be_bytes());
    if r.chance(70) {
        // A plausible response: QR, RD, RA, a common RCODE, TC rarely.
        let tc = if r.chance(5) { 0x02 } else { 0 };
        let rcode = [0, 0, 0, 3, 3, 2, 5][r.below(7) as usize];
        m.extend([0x81 | tc, 0x80 | rcode | (r.byte() & 0x70)]);
    } else {
        m.extend([r.byte(), r.byte()]);
    }
    for c in counts {
        m.extend((c as u16).to_be_bytes());
    }
    for _ in 0..counts[0] {
        name(r, &mut m, &mut s);
        m.extend([0, TYPES[r.below(TYPES.len() as u64) as usize] as u8, 0, 1]);
    }
    for i in 0..counts[1] + counts[2] + counts[3] {
        let in_authority = i >= counts[1] && i < counts[1] + counts[2];
        let soa = in_authority && r.chance(60);
        record(r, &mut m, &mut s, soa);
    }
    // Mutations: truncate, extend, flip, or fudge a count.
    match r.below(30) {
        0 if !m.is_empty() => m.truncate(r.below(m.len() as u64) as usize),
        1 => m.extend((0..r.below(8)).map(|_| r.byte())),
        2 if !m.is_empty() => {
            let i = r.below(m.len() as u64) as usize;
            m[i] ^= 1 << r.below(8);
        }
        3 if m.len() >= 12 => {
            let i = 4 + 2 * r.below(4) as usize;
            m[i + 1] = m[i + 1].wrapping_add(1);
        }
        _ => {}
    }
    m
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn render_q(q: &Question) -> String {
    format!("{}.{}.{}", hex(&q.name), q.tp, q.class)
}

fn render_a(a: &Answer) -> String {
    format!("{}.{}.{}.{}.{}", hex(&a.name), a.tp, a.class, a.ttl, hex(&a.data))
}

fn list<T>(xs: &[T], f: fn(&T) -> String) -> String {
    xs.iter().map(f).collect::<Vec<_>>().join(";")
}

/// The same line `Main.lean` prints, computed by rdns itself.
fn render(buf: &[u8]) -> String {
    let Some(p) = DNSPacket::from_bytes(buf) else {
        return "none".into();
    };
    let h = &p.header;
    let ttl = cache::cache_ttl(&p).map_or("-".to_string(), |t| t.to_string());
    format!(
        "H:{}.{}.{}.{}.{}.{}.{}.{}.{}.{}.{}.{}.{}|Q:{}|A:{}|N:{}|R:{}|ttl:{}|resp:{}|tr:{}|lim:{}",
        h.packet_id, h.qr, h.opcode, h.aa, h.tc, h.rd, h.ra, h.z, h.rcode,
        h.qdcount, h.ancount, h.nscount, h.arcount,
        list(&p.questions, render_q),
        list(&p.answers, render_a),
        list(&p.authorities, render_a),
        list(&p.resources, render_a),
        ttl,
        hex(&p.response_bytes(h.rcode, &p.answers, &p.authorities, 7)),
        hex(&p.truncated_bytes(h.rcode)),
        p.udp_payload_limit(),
    )
}

fn main() {
    let n: usize = std::env::args().nth(1).map_or(100_000, |s| s.parse().unwrap());
    let model = std::env::args().nth(2).unwrap_or_else(|| "../.lake/build/bin/rdns-model".into());

    let mut r = Rng(0x5EED_D15C_0BAD_F00D);
    let inputs: Vec<Vec<u8>> = (0..n).map(|_| message(&mut r)).collect();

    let mut child = Command::new(&model)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("run the Lean model (lake build rdns-model)");
    let mut stdin = child.stdin.take().unwrap();
    let feed: Vec<String> = inputs.iter().map(|m| hex(m)).collect();
    let writer = std::thread::spawn(move || {
        for line in feed {
            writeln!(stdin, "{line}").unwrap();
        }
    });
    let out = BufReader::new(child.stdout.take().unwrap());

    let (mut agree, mut parsed, mut cached) = (0, 0, 0);
    let mut disagree = Vec::new();
    for (input, lean) in inputs.iter().zip(out.lines()) {
        let lean = lean.unwrap();
        let rust = render(input);
        if rust == lean {
            agree += 1;
            parsed += usize::from(rust != "none");
            cached += usize::from(rust != "none" && !rust.contains("|ttl:-|"));
        } else {
            disagree.push((hex(input), rust, lean));
        }
    }
    writer.join().unwrap();
    child.wait().unwrap();

    println!(
        "{} inputs: {agree} agree ({parsed} parsed, {cached} cacheable), {} disagree",
        inputs.len(),
        disagree.len()
    );
    for (input, rust, lean) in disagree.iter().take(5) {
        println!("input {input}\n  rust {rust}\n  lean {lean}");
    }
    std::process::exit(i32::from(!disagree.is_empty()));
}

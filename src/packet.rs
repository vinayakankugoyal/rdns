//! DNS wire-format parsing and serialization.
//!
//! Implements the subset of RFC 1035 needed by the forwarder: header,
//! question, and resource-record encoding, including decompression of
//! name pointers in responses.
//!
//! Parsing is strict: a message with a malformed name, a truncated section
//! or RDATA that doesn't match its declared length is rejected as a whole
//! (`from_bytes` returns `None`) rather than partially decoded. The
//! properties this module guarantees are listed in `docs/SPEC.md`.

use std::collections::HashMap;
use std::fmt::Display;
use std::hash::{Hash, Hasher};

pub const TYPE_A: u16 = 1;
pub const TYPE_SOA: u16 = 6;
pub const TYPE_AAAA: u16 = 28;
pub const TYPE_OPT: u16 = 41;

pub const RCODE_NOERROR: u8 = 0;
pub const RCODE_SERVFAIL: u8 = 2;
pub const RCODE_NXDOMAIN: u8 = 3;

/// Size of the fixed DNS header in bytes.
const HEADER_LEN: usize = 12;

/// Largest UDP payload a client may receive without EDNS (RFC 1035 §4.2.1).
pub const DEFAULT_UDP_PAYLOAD: usize = 512;

/// Largest UDP payload rdns will send or receive.
pub const MAX_UDP_PAYLOAD: usize = 4096;

/// Maximum length of a domain name in wire format, including the root
/// label (RFC 1035 §2.3.4).
const MAX_NAME_LEN: usize = 255;

/// TTL (seconds) used for synthesized answers to blocked queries.
const BLOCKED_TTL: u32 = 300;

#[derive(Debug, Clone, Copy)]
pub struct Header {
    pub packet_id: u16,
    pub qr: u8,
    pub opcode: u8,
    pub aa: u8,
    pub tc: u8,
    pub rd: u8,
    pub ra: u8,
    pub z: u8,
    pub rcode: u8,
    pub qdcount: u16,
    pub ancount: u16,
    pub nscount: u16,
    pub arcount: u16,
}

impl Header {
    fn from_bytes(buf: &[u8]) -> Self {
        Self {
            packet_id: u16::from_be_bytes([buf[0], buf[1]]),
            qr: buf[2] >> 7 & 0x01,
            opcode: buf[2] >> 3 & 0x0f,
            aa: buf[2] >> 2 & 0x01,
            tc: buf[2] >> 1 & 0x01,
            rd: buf[2] & 0x01,
            ra: buf[3] >> 7 & 0x01,
            z: buf[3] >> 4 & 0x07,
            rcode: buf[3] & 0x0f,
            qdcount: u16::from_be_bytes([buf[4], buf[5]]),
            ancount: u16::from_be_bytes([buf[6], buf[7]]),
            nscount: u16::from_be_bytes([buf[8], buf[9]]),
            arcount: u16::from_be_bytes([buf[10], buf[11]]),
        }
    }

    fn write_to(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.packet_id.to_be_bytes());
        buf.push(self.qr << 7 | self.opcode << 3 | self.aa << 2 | self.tc << 1 | self.rd);
        buf.push(self.ra << 7 | self.z << 4 | self.rcode);
        buf.extend_from_slice(&self.qdcount.to_be_bytes());
        buf.extend_from_slice(&self.ancount.to_be_bytes());
        buf.extend_from_slice(&self.nscount.to_be_bytes());
        buf.extend_from_slice(&self.arcount.to_be_bytes());
    }
}

/// A question. Equality and hashing treat the name case-insensitively, as
/// DNS does (RFC 4343), so it can key the cache and match responses.
#[derive(Debug, Clone)]
pub struct Question {
    /// Domain name in uncompressed wire format (length-prefixed labels).
    pub name: Vec<u8>,
    pub tp: u16,
    pub class: u16,
}

impl PartialEq for Question {
    fn eq(&self, other: &Self) -> bool {
        // Length octets are < 64, so they never fall in the ASCII letter
        // range and case folding only touches label bytes.
        self.tp == other.tp
            && self.class == other.class
            && self.name.eq_ignore_ascii_case(&other.name)
    }
}

impl Eq for Question {}

impl Hash for Question {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.len().hash(state);
        for b in &self.name {
            b.to_ascii_lowercase().hash(state);
        }
        self.tp.hash(state);
        self.class.hash(state);
    }
}

impl Question {
    fn write_to(&self, buf: &mut Vec<u8>, names: &mut Compressor) {
        names.write(buf, &self.name);
        buf.extend_from_slice(&self.tp.to_be_bytes());
        buf.extend_from_slice(&self.class.to_be_bytes());
    }

    /// Synthesizes the answer for a blocklisted query: `0.0.0.0` for A,
    /// `::` for AAAA, and no record (an empty NOERROR) for any other type,
    /// since no other type has an "unroutable" value.
    pub fn to_blocked_answer(&self) -> Option<Answer> {
        let data = match self.tp {
            TYPE_A => vec![0; 4],
            TYPE_AAAA => vec![0; 16],
            _ => return None,
        };
        Some(Answer {
            name: self.name.clone(),
            tp: self.tp,
            class: self.class,
            ttl: BLOCKED_TTL,
            data,
        })
    }

    /// Returns the domain name in dotted presentation form (e.g. `example.com`).
    pub fn display_name(&self) -> String {
        format_name(&self.name)
    }
}

impl Display for Question {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "question={}", format_name(&self.name))
    }
}

/// Renders a wire-format domain name as a dotted string.
fn format_name(name: &[u8]) -> String {
    let mut labels: Vec<String> = Vec::new();
    let mut n = 0;
    while n < name.len() {
        let length = name[n] as usize;
        if length == 0 || n + 1 + length > name.len() {
            break;
        }
        labels.push(String::from_utf8_lossy(&name[n + 1..n + 1 + length]).into_owned());
        n += 1 + length;
    }
    labels.join(".")
}

#[derive(Debug, Clone)]
pub struct Answer {
    /// Domain name in uncompressed wire format (length-prefixed labels).
    pub name: Vec<u8>,
    pub tp: u16,
    pub class: u16,
    pub ttl: u32,
    /// RDATA, with any embedded domain names decompressed.
    pub data: Vec<u8>,
}

impl Answer {
    /// Writes the record, reducing its TTL by `age` seconds (saturating).
    /// The owner name, and names inside RDATA where compression is allowed,
    /// are compressed against names already in `buf`.
    fn write_to(&self, buf: &mut Vec<u8>, age: u32, names: &mut Compressor) {
        names.write(buf, &self.name);
        buf.extend_from_slice(&self.tp.to_be_bytes());
        buf.extend_from_slice(&self.class.to_be_bytes());
        buf.extend_from_slice(&self.ttl.saturating_sub(age).to_be_bytes());
        let length_at = buf.len();
        buf.extend_from_slice(&[0, 0]);
        match rdata_fields(self) {
            Some(fields) => {
                for (is_name, bytes) in fields {
                    if is_name {
                        names.write(buf, bytes);
                    } else {
                        buf.extend_from_slice(bytes);
                    }
                }
            }
            None => buf.extend_from_slice(&self.data),
        }
        let length = (buf.len() - length_at - 2) as u16;
        buf[length_at..length_at + 2].copy_from_slice(&length.to_be_bytes());
    }

    /// For an SOA record, the MINIMUM field (the last 4 bytes of RDATA),
    /// which bounds how long a negative answer may be cached (RFC 2308).
    pub fn soa_minimum(&self) -> Option<u32> {
        if self.tp != TYPE_SOA || self.data.len() < 20 {
            return None;
        }
        let m = &self.data[self.data.len() - 4..];
        Some(u32::from_be_bytes([m[0], m[1], m[2], m[3]]))
    }
}

impl Display for Answer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data: Vec<String> = self.data.iter().map(|d| d.to_string()).collect();
        write!(
            f,
            "question={}\nanswer={}",
            format_name(&self.name),
            data.join(".")
        )
    }
}

/// One field of an RDATA layout.
enum Field {
    /// A (possibly compressed) domain name.
    Name,
    /// A fixed number of opaque bytes.
    Fixed(usize),
}

/// RDATA layout of the record types that may carry compressed names: the
/// RFC 1035 types, plus RP, AFSDB, RT and SRV, which receivers are asked
/// to decompress (RFC 3597 §4). RDATA of every other type is opaque.
fn rdata_layout(tp: u16) -> Option<&'static [Field]> {
    use Field::*;
    match tp {
        // NS, MD, MF, CNAME, MB, MG, MR, PTR
        2 | 3 | 4 | 5 | 7 | 8 | 9 | 12 => Some(&[Name]),
        // SOA: MNAME, RNAME, SERIAL, REFRESH, RETRY, EXPIRE, MINIMUM
        6 => Some(&[Name, Name, Fixed(20)]),
        // MINFO, RP
        14 | 17 => Some(&[Name, Name]),
        // MX, AFSDB, RT: 16-bit preference + name
        15 | 18 | 21 => Some(&[Fixed(2), Name]),
        // SRV: priority, weight, port + target
        33 => Some(&[Fixed(6), Name]),
        _ => None,
    }
}

/// Whether names inside RDATA of type `tp` may be compressed: only the
/// RFC 1035 types. RFC 3597 §4 forbids it for every later type, and
/// RFC 2782 for SRV in particular.
fn compressible_rdata(tp: u16) -> bool {
    matches!(tp, 2..=9 | 12 | 14 | 15)
}

/// `a`'s RDATA split into its fields, each marked as a name or not, if
/// its names may be compressed and the RDATA matches its layout. The split
/// happens before anything is written, so a mismatch can't leave the
/// compressor pointing into bytes that were never sent.
fn rdata_fields(a: &Answer) -> Option<Vec<(bool, &[u8])>> {
    if !compressible_rdata(a.tp) {
        return None;
    }
    let mut fields = Vec::new();
    let mut rest = &a.data[..];
    for field in rdata_layout(a.tp)? {
        let (is_name, n) = match field {
            Field::Name => (true, name_len(rest)?),
            Field::Fixed(n) => (false, *n),
        };
        fields.push((is_name, rest.get(..n)?));
        rest = &rest[n..];
    }
    rest.is_empty().then_some(fields)
}

/// Length of the uncompressed name at the start of `b`, root label
/// included.
fn name_len(b: &[u8]) -> Option<usize> {
    let mut i = 0;
    loop {
        let len = *b.get(i)? as usize;
        if len > 63 {
            return None;
        }
        i += 1 + len;
        if len == 0 {
            return (i <= b.len()).then_some(i);
        }
    }
}

/// Writes names with compression pointers (RFC 1035 §4.1.4): each name
/// ends in a pointer to the longest suffix already written, byte for byte,
/// so a decoded name is exactly the name that was written.
#[derive(Default)]
struct Compressor {
    /// Offset of every suffix written so far.
    suffixes: HashMap<Vec<u8>, u16>,
}

impl Compressor {
    /// Writes `name`, an uncompressed wire-format name, to `buf`.
    fn write(&mut self, buf: &mut Vec<u8>, name: &[u8]) {
        let mut i = 0;
        while let Some(&len) = name.get(i) {
            let end = i + 1 + len as usize;
            if len == 0 || len > 63 || end > name.len() {
                // The root, or not a well-formed name: write the rest as is.
                buf.extend_from_slice(&name[i..]);
                return;
            }
            let suffix = &name[i..];
            if let Some(&offset) = self.suffixes.get(suffix) {
                buf.extend_from_slice(&(0xC000 | offset).to_be_bytes());
                return;
            }
            // Pointers hold 14 bits, so later offsets can't be targets.
            if buf.len() < 0x4000 {
                self.suffixes.insert(suffix.to_vec(), buf.len() as u16);
            }
            buf.extend_from_slice(&name[i..end]);
            i = end;
        }
    }
}

/// A bounds-checked cursor over a message.
struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        let out = self.buf.get(self.pos..self.pos.checked_add(n)?)?;
        self.pos += n;
        Some(out)
    }

    fn u16(&mut self) -> Option<u16> {
        self.bytes(2).map(|b| u16::from_be_bytes([b[0], b[1]]))
    }

    fn u32(&mut self) -> Option<u32> {
        self.bytes(4)
            .map(|b| u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
    }

    fn name(&mut self) -> Option<Vec<u8>> {
        let (name, used) = read_name(self.buf, self.pos)?;
        self.pos += used;
        Some(name)
    }
}

/// Decodes the domain name at `start`, following compression pointers.
///
/// Returns the uncompressed name and the number of bytes the name occupies
/// at `start`, or `None` if the name is malformed: truncated, longer than
/// 255 bytes, using a reserved label type, or containing a pointer that
/// doesn't point strictly backwards (RFC 1035 §4.1.4: a pointer refers to a
/// *prior* occurrence).
///
/// Termination: every step either appends a label (the 255-byte limit
/// bounds these) or follows a pointer to a strictly smaller offset (so
/// pointers alone can't repeat); hence the loop runs at most
/// `MAX_NAME_LEN + buf.len()` times.
fn read_name(buf: &[u8], start: usize) -> Option<(Vec<u8>, usize)> {
    let mut name = Vec::new();
    let mut pos = start;
    // Bytes consumed at `start`, fixed by the first pointer.
    let mut used = None;
    loop {
        let b = *buf.get(pos)?;
        match b & 0xC0 {
            0xC0 => {
                let low = *buf.get(pos + 1)?;
                let target = ((b as usize & 0x3F) << 8) | low as usize;
                if target >= pos {
                    return None;
                }
                used.get_or_insert_with(|| pos + 2 - start);
                pos = target;
            }
            0x00 => {
                let label = buf.get(pos..pos + 1 + b as usize)?;
                if name.len() + label.len() > MAX_NAME_LEN {
                    return None;
                }
                name.extend_from_slice(label);
                pos += label.len();
                if b == 0 {
                    return Some((name, used.unwrap_or_else(|| pos - start)));
                }
            }
            // 0b01 / 0b10 label types are reserved (RFC 6891 §5).
            _ => return None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct DNSPacket {
    pub header: Header,
    pub questions: Vec<Question>,
    pub answers: Vec<Answer>,
    pub authorities: Vec<Answer>,
    pub resources: Vec<Answer>,
}

impl DNSPacket {
    /// Parses a packet from raw bytes.
    ///
    /// Returns `None` if the message is malformed: too short for a header,
    /// a section shorter than its header count, a malformed name, or RDATA
    /// whose decoded fields don't exactly fill RDLENGTH.
    pub fn from_bytes(buf: &[u8]) -> Option<Self> {
        let header = Header::from_bytes(buf.get(..HEADER_LEN)?);
        let mut r = Reader {
            buf,
            pos: HEADER_LEN,
        };
        // Cap preallocation by what the buffer could possibly hold, so a
        // forged count can't make us allocate for 65535 records.
        let cap = |count: u16| (count as usize).min(buf.len() / 5);

        let mut questions = Vec::with_capacity(cap(header.qdcount));
        for _ in 0..header.qdcount {
            questions.push(Question {
                name: r.name()?,
                tp: r.u16()?,
                class: r.u16()?,
            });
        }
        let sections = [header.ancount, header.nscount, header.arcount].map(|count| {
            let mut records = Vec::with_capacity(cap(count));
            for _ in 0..count {
                records.push(Self::read_record(&mut r)?);
            }
            Some(records)
        });
        let [answers, authorities, resources] = sections;
        Some(Self {
            header,
            questions,
            answers: answers?,
            authorities: authorities?,
            resources: resources?,
        })
    }

    fn read_record(r: &mut Reader) -> Option<Answer> {
        let name = r.name()?;
        let tp = r.u16()?;
        let class = r.u16()?;
        let ttl = r.u32()?;
        let length = r.u16()? as usize;
        let end = r.pos.checked_add(length)?;
        if end > r.buf.len() {
            return None;
        }

        // Names inside RDATA are decompressed so the record stays valid
        // once it is copied out of this message (into the cache, or into
        // a re-serialized message where offsets have moved).
        let data = match rdata_layout(tp) {
            None => r.bytes(length)?.to_vec(),
            Some(layout) => {
                let mut data = Vec::with_capacity(length);
                for field in layout {
                    match field {
                        Field::Name => data.extend(r.name()?),
                        Field::Fixed(n) => data.extend_from_slice(r.bytes(*n)?),
                    }
                    if r.pos > end {
                        return None;
                    }
                }
                if r.pos != end {
                    return None;
                }
                data
            }
        };
        Some(Answer {
            name,
            tp,
            class,
            ttl,
            data,
        })
    }

    /// Serializes a response to this query.
    ///
    /// The header is copied from the query with QR and RA set, the given
    /// RCODE, and counts matching the records written. Every TTL is
    /// reduced by `age` seconds, the time the records spent in the cache.
    /// Names are compressed, so a response rebuilt from cached records is
    /// no larger than the upstream's compressed original.
    pub fn response_bytes(
        &self,
        rcode: u8,
        answers: &[Answer],
        authorities: &[Answer],
        age: u32,
    ) -> Vec<u8> {
        let mut header = self.header;
        header.qr = 1;
        header.ra = 1;
        header.aa = 0;
        header.tc = 0;
        header.rcode = rcode;
        header.qdcount = self.questions.len() as u16;
        header.ancount = answers.len() as u16;
        header.nscount = authorities.len() as u16;
        header.arcount = 0;

        let mut buf = Vec::with_capacity(DEFAULT_UDP_PAYLOAD);
        let mut names = Compressor::default();
        header.write_to(&mut buf);
        for q in &self.questions {
            q.write_to(&mut buf, &mut names);
        }
        for a in answers.iter().chain(authorities) {
            a.write_to(&mut buf, age, &mut names);
        }
        buf
    }

    /// Serializes an empty response to this query with TC set and the
    /// given RCODE, for when the full response is larger than the client
    /// can receive (RFC 2181 §9).
    pub fn truncated_bytes(&self, rcode: u8) -> Vec<u8> {
        let mut buf = self.response_bytes(rcode, &[], &[], 0);
        buf[2] |= 0x02;
        buf
    }

    /// The largest UDP response this query's sender can receive: the
    /// payload size in its EDNS OPT record (RFC 6891 §6.2.3), or 512.
    pub fn udp_payload_limit(&self) -> usize {
        self.resources
            .iter()
            .find(|r| r.tp == TYPE_OPT)
            .map_or(DEFAULT_UDP_PAYLOAD, |opt| opt.class as usize)
            .clamp(DEFAULT_UDP_PAYLOAD, MAX_UDP_PAYLOAD)
    }
}

/// Overwrites the transaction ID of the raw message in `buf`.
pub fn set_id(buf: &mut [u8], id: u16) {
    buf[..2].copy_from_slice(&id.to_be_bytes());
}

#[cfg(test)]
#[path = "spec/packet_spec.rs"]
mod spec;

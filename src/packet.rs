//! DNS wire-format parsing and serialization.
//!
//! Implements the subset of RFC 1035 needed by the forwarder: header,
//! question, and resource-record encoding, including decompression of
//! name pointers in responses.

use std::fmt::Display;

/// DNS record types that embed a (possibly compressed) domain name in RDATA.
const TYPE_NS: u16 = 2;
const TYPE_CNAME: u16 = 5;
const TYPE_MX: u16 = 15;
const TYPE_PTR: u16 = 12;

/// Size of the fixed DNS header in bytes.
const HEADER_LEN: usize = 12;

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

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct Question {
    /// Domain name in uncompressed wire format (length-prefixed labels).
    pub name: Vec<u8>,
    pub tp: u16,
    pub class: u16,
}

impl Question {
    fn write_to(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.name);
        buf.extend_from_slice(&self.tp.to_be_bytes());
        buf.extend_from_slice(&self.class.to_be_bytes());
    }

    /// Synthesizes an answer pointing at 0.0.0.0 for blocklisted queries.
    pub fn to_blocked_answer(&self) -> Answer {
        Answer {
            name: self.name.clone(),
            tp: self.tp,
            class: self.class,
            ttl: BLOCKED_TTL,
            length: 4,
            data: vec![0, 0, 0, 0],
        }
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
    pub length: u16,
    pub data: Vec<u8>,
}

impl Answer {
    fn write_to(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.name);
        buf.extend_from_slice(&self.tp.to_be_bytes());
        buf.extend_from_slice(&self.class.to_be_bytes());
        buf.extend_from_slice(&self.ttl.to_be_bytes());
        buf.extend_from_slice(&self.length.to_be_bytes());
        buf.extend_from_slice(&self.data);
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
    /// Returns `None` if the buffer is too short to contain a DNS header.
    /// Truncated or malformed sections beyond the header yield partial
    /// results rather than an error.
    pub fn from_bytes(buf: &[u8]) -> Option<Self> {
        if buf.len() < HEADER_LEN {
            return None;
        }
        let header = Header::from_bytes(&buf[..HEADER_LEN]);
        let (questions, offset) = Self::parse_questions(buf, HEADER_LEN, header.qdcount);
        let (answers, offset) = Self::parse_answers(buf, offset, header.ancount);
        let (authorities, offset) = Self::parse_answers(buf, offset, header.nscount);
        let (resources, _) = Self::parse_answers(buf, offset, header.arcount);
        Some(Self {
            header,
            questions,
            answers,
            authorities,
            resources,
        })
    }

    /// Serializes the packet to wire format.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(512);
        self.header.write_to(&mut buf);
        for q in &self.questions {
            q.write_to(&mut buf);
        }
        for a in self
            .answers
            .iter()
            .chain(&self.authorities)
            .chain(&self.resources)
        {
            a.write_to(&mut buf);
        }
        buf
    }

    /// Serializes a response to this query carrying the given answers,
    /// without taking ownership of them.
    ///
    /// The header is copied from the query with the response flags set and
    /// authority/additional sections dropped.
    pub fn response_bytes(&self, answers: &[Answer]) -> Vec<u8> {
        let mut header = self.header;
        header.qr = 1;
        header.ra = 1;
        header.ancount = answers.len() as u16;
        header.nscount = 0;
        header.arcount = 0;

        let mut buf = Vec::with_capacity(512);
        header.write_to(&mut buf);
        for q in &self.questions {
            q.write_to(&mut buf);
        }
        for a in answers {
            a.write_to(&mut buf);
        }
        buf
    }

    /// Reads a domain name starting at `start`, following compression
    /// pointers, and returns the uncompressed name along with the number of
    /// bytes consumed at the original position.
    fn qname(buf: &[u8], start: usize) -> (Vec<u8>, usize) {
        let mut name: Vec<u8> = Vec::new();
        let mut n = start;
        loop {
            let Some(&b) = buf.get(n) else {
                // Truncated packet: return what we have.
                return (name, n - start);
            };

            // A pointer (two high bits set) ends the name; the remainder
            // lives at the 14-bit offset it encodes.
            if b & 0b1100_0000 == 0b1100_0000 {
                let Some(&low) = buf.get(n + 1) else {
                    return (name, n - start);
                };
                let target = ((b as u16 & 0x3f) << 8 | low as u16) as usize;
                let (suffix, _) = Self::qname(buf, target);
                name.extend_from_slice(&suffix);
                // The pointer itself occupies two bytes.
                return (name, n + 2 - start);
            }

            if b == 0 {
                name.push(b);
                return (name, n + 1 - start);
            }

            let len = b as usize;
            if n + 1 + len > buf.len() {
                // Truncated label: return what we have.
                return (name, n - start);
            }
            name.push(b);
            name.extend_from_slice(&buf[n + 1..n + 1 + len]);
            n += 1 + len;
        }
    }

    fn parse_questions(buf: &[u8], mut offset: usize, count: u16) -> (Vec<Question>, usize) {
        let mut questions = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let (name, advance) = Self::qname(buf, offset);
            offset += advance;
            // Need 4 bytes for type + class; bail on a truncated packet.
            if offset + 4 > buf.len() {
                break;
            }
            questions.push(Question {
                name,
                tp: u16::from_be_bytes([buf[offset], buf[offset + 1]]),
                class: u16::from_be_bytes([buf[offset + 2], buf[offset + 3]]),
            });
            offset += 4;
        }
        (questions, offset)
    }

    fn parse_answers(buf: &[u8], mut offset: usize, count: u16) -> (Vec<Answer>, usize) {
        let mut answers = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let (name, advance) = Self::qname(buf, offset);
            offset += advance;
            // Need 10 bytes for type + class + ttl + rdlength; bail on a
            // truncated packet.
            if offset + 10 > buf.len() {
                break;
            }
            let tp = u16::from_be_bytes([buf[offset], buf[offset + 1]]);
            let class = u16::from_be_bytes([buf[offset + 2], buf[offset + 3]]);
            let ttl = u32::from_be_bytes([
                buf[offset + 4],
                buf[offset + 5],
                buf[offset + 6],
                buf[offset + 7],
            ]);
            let length = u16::from_be_bytes([buf[offset + 8], buf[offset + 9]]);
            offset += 10;

            // The record data must fit within the buffer.
            if offset + length as usize > buf.len() {
                break;
            }

            // Record types whose RDATA contains a domain name must be
            // decompressed so cached copies don't carry pointers into a
            // packet that no longer exists.
            let data = match tp {
                TYPE_NS | TYPE_CNAME | TYPE_PTR => {
                    let (decompressed, _) = Self::qname(buf, offset);
                    decompressed
                }
                TYPE_MX if length >= 2 => {
                    // MX: 2-byte preference followed by a domain name.
                    let mut mx_data = buf[offset..offset + 2].to_vec();
                    let (decompressed, _) = Self::qname(buf, offset + 2);
                    mx_data.extend_from_slice(&decompressed);
                    mx_data
                }
                _ => buf[offset..offset + length as usize].to_vec(),
            };

            offset += length as usize;

            answers.push(Answer {
                name,
                tp,
                class,
                ttl,
                length: data.len() as u16,
                data,
            });
        }
        (answers, offset)
    }
}

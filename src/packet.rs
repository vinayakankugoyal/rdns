
#[derive(Debug,Clone, Copy)]
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
    pub arcount: u16
}

impl Header {
    pub fn new(buf: &[u8]) -> Self {
        return Self { 
            packet_id: u16::from_be_bytes([buf[0], buf[1]]),
            qr: (buf[2] >> 7 & 0x01),
            opcode: buf[2] >> 3 & 0b00001111,
            aa: (buf[2] >> 2 & 0x01),
            tc: (buf[2] >> 1 & 0x01),
            rd: (buf[2] >> 0 & 0x01),
            ra: (buf[3] >> 7 & 0x01),
            z: buf[3] >> 4 & 0b00000111,
            rcode: buf[3] & 0b00001111,
            qdcount: u16::from_be_bytes([buf[4], buf[5]]),
            ancount: u16::from_be_bytes([buf[6], buf[7]]),
            nscount: u16::from_be_bytes([buf[8], buf[9]]),
            arcount: u16::from_be_bytes([buf[10], buf[11]])
        };
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut result: Vec<u8> = Vec::new();
        result.extend_from_slice(&self.packet_id.to_be_bytes());
        result.extend_from_slice(&(self.qr << 7 | self.opcode << 3 | self.aa << 2 | self.tc << 1 | self.rd).to_be_bytes());
        result.extend_from_slice(&(self.ra << 7 | self.z << 4 | self.rcode).to_be_bytes());
        result.extend_from_slice(&self.qdcount.to_be_bytes());
        result.extend_from_slice(&self.ancount.to_be_bytes());
        result.extend_from_slice(&self.nscount.to_be_bytes());
        result.extend_from_slice(&self.arcount.to_be_bytes());
        result
    }
}

#[derive(Debug,Clone)]
pub struct Question {
    pub name: Vec<u8>,
    pub tp: u16,
    pub class: u16, 
}
impl Question {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut res = self.name.clone();
        res.extend_from_slice(&self.tp.to_be_bytes());
        res.extend_from_slice(&self.class.to_be_bytes());
        res
    }
}

#[derive(Debug, Clone)]
pub struct Answer {
    pub name: Vec<u8>,
    pub tp: u16,
    pub class: u16,
    pub ttl: u32,
    pub length: u16,
    pub data: Vec<u8>,
}

impl Answer {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut result = self.name.clone();
        result.extend_from_slice(&self.tp.to_be_bytes());
        result.extend_from_slice(&self.class.to_be_bytes());
        result.extend_from_slice(&self.ttl.to_be_bytes());
        result.extend_from_slice(&self.length.to_be_bytes());
        result.extend_from_slice(&self.data);
        return result;
    }

    pub fn from_question(question: Question) -> Answer {
        Answer { 
            name: question.name.clone(), 
            tp: question.tp, 
            class: question.class, 
            ttl: 0x3C, 
            length: 4, 
            data: vec![8, 8, 8, 8]
        }
    }
}

#[derive(Debug, Clone)]
pub struct DNSPacket {
    pub header: Header,
    pub questions: Vec<Question>,
    pub answers: Vec<Answer>,
}

impl DNSPacket {
    pub fn from_bytes(buf: &[u8]) -> Self {
        let header = Header::new(&buf[0..12]);
        let (questions, offset) = DNSPacket::parse_questions(&buf, 12, header.qdcount);
        let (answers, _) = DNSPacket::parse_answers(&buf, offset, header.ancount);
        return Self {
            header, 
            questions,
            answers,
        };
    }

    pub fn with_answers(&self) -> DNSPacket {
        let mut header = self.header.clone();
        header.qr = 1;
        header.ancount = header.qdcount;
        if header.opcode != 0 {
            header.rcode = 4;
        }
        let questions = self.questions.clone();
        let mut answers: Vec<Answer> = Vec::new();
        for q in questions.iter() {
            answers.push(Answer::from_question(q.clone()));
        }

        return DNSPacket { header, questions, answers }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut result = self.header.to_bytes();
        for q in self.questions.iter() {
            result.extend_from_slice(&q.to_bytes());
        }
        for a in self.answers.iter() {
            result.extend_from_slice(&a.to_bytes());
        }
        return result;
    }

    pub fn as_forwards(&self) -> Vec<DNSPacket> {
        let mut res: Vec<DNSPacket> = Vec::new();
        for q in self.questions.iter() {
            let mut header = self.header.clone();
            header.qdcount = 1;
            let mut questions: Vec<Question> = Vec::new();
            questions.push(q.clone());
            res.push(
                DNSPacket { header, questions, answers: Vec::new() }
            );
        }
        return  res;
    }

    fn qname(buf: &[u8], start: usize) -> (Vec<u8>, usize) {
        let mut name: Vec<u8> = Vec::new();
        let mut n = start;
        loop {
            if buf[n] & 0b11000000 == 0b11000000 {
                let new_start = buf[n+1] as usize;
                let (common,  _) = Self::qname(&buf, new_start);
                name.extend_from_slice(&common);
                // +2 because we also read the offset and the pointer;
                return (name, n + 2 - start);
            }

            if buf[n] == 0 {
                name.push(buf[n]);
                return (name, n + 1 - start);
            }
            name.push(buf[n]);
            n += 1;
        }
    }

    fn parse_questions(buf: &[u8], mut offset: usize, count: u16) -> (Vec<Question>, usize) {
        let mut questions: Vec<Question> = Vec::new();
        for _ in 0..count {
            let (name, advance) = Self::qname(buf, offset);
            offset += advance;
            questions.push(Question { 
                name,
                tp: u16::from_be_bytes([buf[offset], buf[offset+1]]),
                class: u16::from_be_bytes([buf[offset+2], buf[offset+3]]),  
            });
            offset += 4;
        }
        (questions, offset)
    }

    fn parse_answers(buf: &[u8], mut offset: usize, count: u16) -> (Vec<Answer>, usize) {
        let mut answers: Vec<Answer> = Vec::new();
        for _ in 0..count {
            let (name, advance) = Self::qname(buf, offset);
            offset += advance;
            let tp = u16::from_be_bytes([buf[offset], buf[offset+1]]);
            let class = u16::from_be_bytes([buf[offset+2], buf[offset+3]]);
            let ttl = u32::from_be_bytes([buf[offset+4], buf[offset+5], buf[offset+6], buf[offset+7]]);
            let length = u16::from_be_bytes([buf[offset+8], buf[offset+9]]);
            offset += 10;
            
            let data = buf[offset..offset+length as usize].to_vec();
            
            offset += length as usize;

            answers.push(Answer {
                name,
                tp,
                class,
                ttl,
                length,
                data
            });
        }
        (answers, offset)
    }
}



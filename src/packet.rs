#[derive(Debug,Clone, Copy)]
pub struct Header {
    packet_id: u16,
    qr: u8,
    opcode: u8,
    aa: u8,
    tc: u8,
    rd: u8,
    ra: u8,
    z: u8,
    rcode: u8,
    qdcount: u16,
    ancount: u16,
    nscount: u16,
    arcount: u16
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
    name: Vec<u8>,
    tp: u16,
    class: u16, 
}

impl Question {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut res = self.name.clone();
        res.extend_from_slice(&self.tp.to_be_bytes());
        res.extend_from_slice(&self.class.to_be_bytes());
        res
    }
}

struct Answer {
    name: Vec<u8>,
    tp: u16,
    class: u16,
    ttl: u32,
    length: u16,
    data: u32,
}

impl Answer {
    fn to_bytes(&self) -> Vec<u8> {
        let mut result = self.name.clone();
        result.extend_from_slice(&self.tp.to_be_bytes());
        result.extend_from_slice(&self.class.to_be_bytes());
        result.extend_from_slice(&self.ttl.to_be_bytes());
        result.extend_from_slice(&self.length.to_be_bytes());
        result.extend_from_slice(&self.data.to_be_bytes());
        return result;
    }

    fn from_question(question: Question) -> Answer {
        Answer { 
            name: question.name.clone(), 
            tp: question.tp, 
            class: question.class, 
            ttl: 0x3C, 
            length: 4, 
            data: u32::from_be_bytes([0x08, 0x08, 0x08, 0x08])
        }
    }
}

pub struct RecvPacket {
    pub header: Header,
    pub questions: Vec<Question>,
}

impl RecvPacket {
    pub fn new(buf: &[u8]) -> Self {
        let header = Header::new(&buf[0..12]);
        return Self {
            header: header, 
            questions:  RecvPacket::questions(&buf[12..])
        };
    }

    fn questions(buf: &[u8]) -> Vec<Question>{
        let mut n = 0;
        let mut start = 0;
        let mut questions: Vec<Question> = Vec::new();
        while n < buf.len() {
            let mut name: Vec<u8> = Vec::new();
            loop {
                let ch = buf[n];
                if ch == 0 {
                    name.extend_from_slice(&buf[start..=n]);
                        questions.push(Question {
                        name: name, 
                        tp: u16::from_be_bytes([buf[n+1], buf[n+2]]),
                        class: u16::from_be_bytes([buf[n+3], buf[n+4]])  
                    });
                    start = n + 5;
                    n = n + 5;
                    break;
                }
                
                n = n+1;
            }
            n = n+4;
        }

        return questions;
    }
}

pub struct RespPacket {
    pub header: Header,
    pub questions: Vec<Question>,
    answers: Vec<Answer>,
}

impl RespPacket {
    pub fn from_recv_packet(recv: RecvPacket) -> RespPacket {
        let mut header = recv.header.clone();
        header.qr = 1;
        header.ancount = header.qdcount;
        if header.opcode != 0 {
            header.rcode = 4;
        }
        let questions = recv.questions.clone();
        let mut answers: Vec<Answer> = Vec::new();
        for q in questions.iter() {
            answers.push(Answer::from_question(q.clone()));
        }

        return RespPacket { header, questions, answers }
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
    
}


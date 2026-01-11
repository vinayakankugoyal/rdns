#[allow(unused_imports)]
use std::net::UdpSocket;

mod packet;

fn main() {
    // You can use print statements as follows for debugging, they'll be visible when running tests.
    println!("Logs from your program will appear here!");

    let udp_socket = UdpSocket::bind("127.0.0.1:2053").expect("Failed to bind to address");
    let mut buf = [0; 512];
    
    loop {
        match udp_socket.recv_from(&mut buf) {
            Ok((size, source)) => {
                println!("Received {} bytes from {}", size, source);

                let input_packet = packet::RecvPacket::new(&buf);

                let out_packet = packet::RespPacket::from_recv_packet(input_packet);

                let response = out_packet.to_bytes();

                udp_socket
                    .send_to(&response, source)
                    .expect("Failed to send response");
            }
            Err(e) => {
                eprintln!("Error receiving data: {}", e);
                break;
            }
        }
    }
}


fn parse_header(req: &[u8]) -> Vec<u8> {
    let mut result: Vec<u8> = Vec::new();
    // Packet ID
    result.push(req[0]);
    result.push(req[1]);

    let mut qr_opcode_aa_tc_rd = req[2];
    // Set qr bit to 1;
    qr_opcode_aa_tc_rd = qr_opcode_aa_tc_rd | 1u8 << 7;
    // Set aa bit to 0;
    qr_opcode_aa_tc_rd = qr_opcode_aa_tc_rd & !(1u8 << 2);
    // Set tc bit to 0;
    qr_opcode_aa_tc_rd = qr_opcode_aa_tc_rd & !(1u8 << 1);
    result.push(qr_opcode_aa_tc_rd);

    if qr_opcode_aa_tc_rd >> 3 & 0b00001111 != 0b00000000 {
            // RA Z RCODE
            result.push(0x04);
    } else {
            // RA Z RCODE
            result.push(0x00);
    }

    // QDCOUNT
    result.push(0x00);
    result.push(0x01);
    // ANCOUNT
    result.push(0x00);
    result.push(0x01);
    // NSCOUNT
    result.push(0x00);
    result.push(0x01);
    // ARCOUNT
    result.push(0x00);
    result.push(0x01);

    return result;
}

fn parse_question(req: &[u8]) -> Vec<u8> {
    let mut domain = Vec::new();

    let mut i: usize = 12;
    let mut ch: u8 = req[i];
    while ch != 0x00 {
        domain.push(ch);
        i +=1;
        ch = req[i];
    }
    domain.push(ch);

    i+=1;
    let mut tp: Vec<u8> = vec![req[i]];
    i+=1;
    tp.push(req[i]);

    i+=1;
    let mut class = vec![req[i]];
    i+=1;
    class.push(req[i]);

    let mut question: Vec<u8> = Vec::new();
    for d in domain.iter() {
        question.push(d.clone());
    }
    for d in tp.iter() {
        question.push(d.clone());
    }
    for d in class.iter() {
        question.push(d.clone());
    }

    let mut answer: Vec<u8> = Vec::new();
    for d in domain.iter() {
        answer.push(d.clone());
    }
    for d in tp {
        answer.push(d);
    }
    for d in class {
        answer.push(d);
    }
    answer.push(0x00);
    answer.push(0x00);
    answer.push(0x00);
    answer.push(0x3c);

    answer.push(0x00);
    answer.push(0x04);

    answer.push(0x08);
    answer.push(0x08);
    answer.push(0x08);
    answer.push(0x08);

    question.append(&mut answer);

    return question;

}

fn parse(req: &[u8]) -> Vec<u8> {
    let mut result = parse_header(req);
    result.append(&mut parse_question(req));
    return result;

}
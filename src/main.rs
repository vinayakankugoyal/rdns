#[allow(unused_imports)]
use std::net::UdpSocket;

fn main() {
    // You can use print statements as follows for debugging, they'll be visible when running tests.
    println!("Logs from your program will appear here!");

    let udp_socket = UdpSocket::bind("127.0.0.1:2053").expect("Failed to bind to address");
    let mut buf = [0; 512];
    
    loop {
        match udp_socket.recv_from(&mut buf) {
            Ok((size, source)) => {
                println!("Received {} bytes from {}", size, source);

                let mut response = parse_header(&buf);

                let mut qa: Vec<u8> = vec![
                    // Question
                    // Domain Name
                    0x0c, //codecrafters
                    b'c',b'o',b'd',b'e',b'c',b'r',b'a',b'f',b't',b'e',b'r',b's',
                    0x02, //io
                    b'i',b'o',
                    0x00,
                    // Type
                    0x00,0x01,
                    // Class
                    0x00,0x01,
                    // Answer
                    // Domain Name
                    0x0c, //codecrafters
                    b'c',b'o',b'd',b'e',b'c',b'r',b'a',b'f',b't',b'e',b'r',b's',
                    0x02, //io
                    b'i',b'o',
                    0x00,
                    // Type
                    0x00,0x01,
                    // Class
                    0x00,0x01,
                    // TTL
                    0x00,0x00,0x00,0x3C,
                    // RDLENGTH
                    0x00,0x04,
                    // RDATA
                    0x08,0x08,0x08,0x08
                ];

                response.append(&mut qa);

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

fn parse_header(header: &[u8]) -> Vec<u8> {
    let mut result: Vec<u8> = Vec::new();
    // Packet ID
    result.push(header[0]);
    result.push(header[1]);

    let mut qr_opcode_aa_tc_rd = header[2];
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
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
                let response = [
                    0x04,0xD2, // Packet ID
                    0x80, // QR=1,OPCODE=0000,AA=0,TC=0,RD=0
                    0x00, // RA=0,Z=000,RCODE=0000 
                    0x00,0x00, //QDCOUNT=0000000000000000
                    0x00,0x00, //ANCOUNT=0000000000000000
                    0x00,0x00, //NSCOUNT=0000000000000000
                    0x00,0x00, //ARCOUNT=0000000000000000


                ];
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

use std::env;
#[allow(unused_imports)]
use std::net::UdpSocket;

use crate::packet::DNSPacket;

mod packet;

fn main() {
    // You can use print statements as follows for debugging, they'll be visible when running tests.
    println!("Logs from your program will appear here!");

    let args: Vec<String> = env::args().collect();

    let mut command = String::from("");
    let mut resolver = String::from("1.1.1.1:53");

    if args.len() > 0 {
        command = args[1].to_string();
        resolver = args[2].to_string();
    }

    let udp_socket = UdpSocket::bind("127.0.0.1:2053").expect("Failed to bind to address");
    let mut buf = [0; 512];

    loop {
        match udp_socket.recv_from(&mut buf) {
            Ok((size, source)) => {
                let packet_bytes = &buf[0..size];
                
                match command.as_str() {
                    "--resolver" => {
                        // Only process requests from clients (not from the resolver itself, 
                        // though normally we wouldn't see resolver packets here if we wait for them explicitly)
                        if source.to_string() != resolver {
                            let input_packet = DNSPacket::from_bytes(packet_bytes);
                            
                            // Split into individual questions
                            let forwards = input_packet.as_forwards();
                            let mut all_answers = Vec::new();
                            
                            for f in forwards.iter() {
                                // Send query to resolver
                                udp_socket
                                    .send_to(&f.to_bytes(), &resolver)
                                    .expect("Failed to send to resolver");
                                
                                // Wait for response from resolver
                                let mut res_buf = [0; 512];
                                loop {
                                    match udp_socket.recv_from(&mut res_buf) {
                                        Ok((res_size, res_source)) => {
                                            if res_source.to_string() == resolver {
                                                let resolver_response = DNSPacket::from_bytes(&res_buf[0..res_size]);
                                                all_answers.extend(resolver_response.answers);
                                                break;
                                            } else {
                                                // Ignore packets from other sources while waiting for resolver
                                                // (In a real server, we would queue them or handle them concurrently)
                                                println!("Ignored packet from {} while waiting for resolver", res_source);
                                            }
                                        }
                                        Err(e) => {
                                            eprintln!("Error receiving from resolver: {}", e);
                                            break;
                                        }
                                    }
                                }
                            }
                            
                            // Construct response packet
                            let mut response_packet = input_packet;
                            response_packet.header.qr = 1; // Response
                            response_packet.header.rcode = if response_packet.header.opcode == 0 { 0 } else { 4 };
                            response_packet.header.ancount = all_answers.len() as u16;
                            response_packet.header.nscount = 0;
                            response_packet.header.arcount = 0;
                            response_packet.answers = all_answers;
                            
                            udp_socket
                                .send_to(&response_packet.to_bytes(), source)
                                .expect("Failed to send response to client");
                        }
                    }
                    _ => {
                        println!("Received {} bytes from {}", size, source);

                        let input_packet = DNSPacket::from_bytes(packet_bytes);

                        let output_packet = input_packet.with_answers();

                        let response = output_packet.to_bytes();

                        udp_socket
                            .send_to(&response, source)
                            .expect("Failed to send response");
                    }
                }
            }
            Err(e) => {
                eprintln!("Error receiving data: {}", e);
                break;
            }
        }
    }
}
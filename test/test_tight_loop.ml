let arp_c = Cstruct.of_string "\x00\x01\x08\x00\x06\x04\x00\x01\xb8\x6b\x23\x5d\x2f\x8a\x12\x1a\x02\x7b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

let ether_c = Cstruct.of_string "\xff\xff\xff\xff\xff\xff\x00\x00\x00\x00\x00\x00\x08\x00\x45\x00\x00\x28\x00\x01\x00\x00\x40\x06\x7c\xcd\x7f\x00\x00\x01\x7f\x00\x00\x01\x00\x14\x00\x50\x00\x00\x00\x00\x00\x00\x00\x00\x50\x02\x20\x00\x91\x7c\x00\x00"

let ip_c = Cstruct.of_string "\x45\x00\x00\x28\x00\x01\x00\x00\x40\x06\x7c\xcd\x7f\x00\x00\x01\x7f\x00\x00\x01\x00\x14\x00\x50\x00\x00\x00\x00\x00\x00\x00\x00\x50\x02\x20\x00\x91\x7c\x00\x00"

let tcp_c = Cstruct.of_string "\x00\x14\x00\x50\x00\x00\x00\x00\x00\x00\x00\x00\x50\x02\x20\x00\x91\x7c\x00\x00"

let udp_c = Cstruct.of_string "\x00\x35\x00\x35\x00\x08\x01\x72"

let repeats = 1_000_000

let bench f input () =
  for _ = 1 to repeats do
    f input
  done;
  Lwt.return_unit

let check_result r =
  match r with
  | Result.Ok _ -> ()
  | _ -> failwith "Decoding failed"

let tight_arp pkt = check_result (Arpv4_packet.Unmarshal.of_cstruct pkt)

let tight_ether pkt = check_result (Ethif_packet.Unmarshal.of_cstruct pkt)

let tight_ip pkt = check_result (Ipv4_packet.Unmarshal.of_cstruct pkt)

let tight_tcp pkt = check_result (Tcp.Tcp_packet.Unmarshal.of_cstruct (Ipaddr.of_string_exn "127.0.0.1") (Ipaddr.of_string_exn "127.0.0.1") pkt)

let tight_udp pkt = check_result (Udp_packet.Unmarshal.of_cstruct (Ipaddr.of_string_exn "127.0.0.1") (Ipaddr.of_string_exn "127.0.0.1") pkt)

let suite = [
    "arp", `Quick, (bench tight_arp arp_c);
    "ether", `Quick, (bench tight_ether ether_c);
    "ip", `Quick, (bench tight_ip ip_c);
    "tcp", `Quick, (bench tight_tcp tcp_c);
    "udp", `Quick, (bench tight_udp udp_c);
]

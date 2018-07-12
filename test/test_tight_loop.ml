let check_result r =
  match r with
  | Result.Ok x -> x
  | _ -> failwith "Failed"

let arp_c = Cstruct.of_string "\x00\x01\x08\x00\x06\x04\x00\x01\xb8\x6b\x23\x5d\x2f\x8a\x12\x1a\x02\x7b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

let ether_c = Cstruct.of_string "\xff\xff\xff\xff\xff\xff\x00\x00\x00\x00\x00\x00\x08\x00\x45\x00\x00\x28\x00\x01\x00\x00\x40\x06\x7c\xcd\x7f\x00\x00\x01\x7f\x00\x00\x01\x00\x14\x00\x50\x00\x00\x00\x00\x00\x00\x00\x00\x50\x02\x20\x00\x91\x7c\x00\x00"

let ip_c = Cstruct.of_string "\x45\x00\x00\x28\x00\x01\x00\x00\x40\x06\x7c\xcd\x7f\x00\x00\x01\x7f\x00\x00\x01\x00\x14\x00\x50\x00\x00\x00\x00\x00\x00\x00\x00\x50\x02\x20\x00\x91\x7c\x00\x00"

let ip_pkt = fst (check_result (Ipv4_packet.Unmarshal.of_cstruct ip_c))

let tcp_c = Cstruct.of_string "\x00\x14\x00\x50\x00\x00\x00\x00\x00\x00\x00\x00\x50\x02\x20\x00\x91\x7c\x00\x00"

let udp_c = Cstruct.of_string "\x00\x35\x00\x35\x00\x08\x01\x72"

let repeats = 1_000_000

let bench f input () =
  for _ = 1 to repeats do
    ignore (f input)
  done;
  Lwt.return_unit

let localhost = Ipaddr.of_string_exn "127.0.0.1"

let tight_arp_dec buf = check_result (Arpv4_packet.Unmarshal.of_cstruct buf)

let tight_ether_dec buf = check_result (Ethif_packet.Unmarshal.of_cstruct buf)

let ipv4_enc_buf = Cstruct.create 60
let tight_ipv4_enc pkt = check_result (Ipv4_packet.Marshal.into_cstruct 0 pkt ipv4_enc_buf)

let tight_ipv4_dec buf = check_result (Ipv4_packet.Unmarshal.of_cstruct buf)

let tight_tcp_dec buf = check_result (Tcp.Tcp_packet.Unmarshal.of_cstruct localhost localhost buf)

let tight_udp_dec buf = check_result (Udp_packet.Unmarshal.of_cstruct localhost localhost buf)

let suite = [
    "arp-dec", `Quick, (bench tight_arp_dec arp_c);
    "ether-dec", `Quick, (bench tight_ether_dec ether_c);
    "ipv4-enc", `Quick, (bench tight_ipv4_enc ip_pkt);
    "ipv4-dec", `Quick, (bench tight_ipv4_dec ip_c);
    "tcp-dec", `Quick, (bench tight_tcp_dec tcp_c);
    "udp-dec", `Quick, (bench tight_udp_dec udp_c);
]

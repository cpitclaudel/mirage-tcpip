open Ethif_wire

type t = {
  source : Macaddr.t;
  destination : Macaddr.t;
  ethertype : Ethif_wire.ethertype;
}

type error = string

let pp fmt t =
  Format.fprintf fmt "%s -> %s: %s" (Macaddr.to_string t.source)
    (Macaddr.to_string t.destination) (Ethif_wire.ethertype_to_string t.ethertype)

let equal {source; destination; ethertype} q =
  (Macaddr.compare source q.source) = 0 &&
  (Macaddr.compare destination q.destination) = 0 &&
  Ethif_wire.(compare (ethertype_to_int ethertype) (ethertype_to_int q.ethertype)) = 0

module Unmarshal = struct
  let of_cstruct_mirage frame =
    if Cstruct.len frame >= sizeof_ethernet then
      match get_ethernet_ethertype frame |> int_to_ethertype with
      | None -> Error (Printf.sprintf "unknown ethertype 0x%x in frame"
                                (get_ethernet_ethertype frame))
      | Some ethertype ->
        let payload = Cstruct.shift frame sizeof_ethernet
        and source = Macaddr.of_bytes_exn (copy_ethernet_src frame)
        and destination = Macaddr.of_bytes_exn (copy_ethernet_dst frame)
        in
        Ok ({ destination; source; ethertype;}, payload)
    else
      Error "frame too small to contain a valid ethernet header"

  let ethertype_of_fiat_type (ftype: Fiat4Mirage.fiat_ethernet_type) =
    match ftype with
    | Fiat4Mirage.ARP -> ARP
    | Fiat4Mirage.IP -> IPv4
    | Fiat4Mirage.IPV6 -> IPv6
    | Fiat4Mirage.RARP -> raise FiatUtils.Unsupported_by_mirage

  (* let fiat_ipv4_encode = FiatUtils.make_encoder Fiat4Mirage.fiat_ipv4_encode *)
  let fiat_ethernet_decode = FiatUtils.make_decoder Fiat4Mirage.fiat_ethernet_decode

  let of_cstruct_fiat frame =
    FiatUtils.log "ethif" "Parsing an ethernet frame";
    (* Printf.printf "ETHIF: %s\n%!" (FiatUtils.cstruct_to_debug_string frame); *)
    match fiat_ethernet_decode frame sizeof_ethernet with
    | Some pkt ->
       let payload = Cstruct.shift frame sizeof_ethernet in
       let source = Macaddr.of_bytes_exn (FiatUtils.bytes_of_bytestring pkt.source) in
       let destination = Macaddr.of_bytes_exn (FiatUtils.bytes_of_bytestring pkt.destination) in
       let ethertype = ethertype_of_fiat_type (Fiat4Mirage.fiat_ethernet_type_of_enum pkt.ethType) in
       Result.Ok ({ destination; source; ethertype }, payload)
    | None ->
       Result.Error (Printf.sprintf "Fiat parsing failed; packet was %s\n"
                       (FiatUtils.cstruct_to_debug_string frame))
    | exception FiatUtils.Unsupported_by_mirage ->
       Result.Error (Printf.sprintf "Ethernet packet unsupported by mirage; packet was %s\n"
                       (FiatUtils.cstruct_to_debug_string frame))

  let of_cstruct =
    if !FiatUtils.ethif_decoding_uses_fiat then of_cstruct_fiat
    else of_cstruct_mirage
end

module Marshal = struct
  open Rresult

  let check_len buf =
    if sizeof_ethernet > Cstruct.len buf then
      Error "Not enough space for an Ethernet header"
    else Ok ()

  let unsafe_fill t buf =
    set_ethernet_dst (Macaddr.to_bytes t.destination) 0 buf;
    set_ethernet_src (Macaddr.to_bytes t.source) 0 buf;
    set_ethernet_ethertype buf (ethertype_to_int t.ethertype);
    ()

  let ethertype_to_fiat_type (ftype: Ethif_wire.ethertype) =
    match ftype with
    | ARP -> Fiat4Mirage.ARP
    | IPv4 -> Fiat4Mirage.IP
    | IPv6 -> Fiat4Mirage.IPV6

  let fiat_ethernet_encode = FiatUtils.make_encoder Fiat4Mirage.fiat_ethernet_encode

  let fill_fiat (t: t) buf =
    let fiat_pkt = Fiat4Mirage.{
          source = FiatUtils.bytestring_of_bytes (Macaddr.to_bytes t.source);
          destination = FiatUtils.bytestring_of_bytes (Macaddr.to_bytes t.destination);
          ethType = fiat_ethernet_type_to_enum (ethertype_to_fiat_type t.ethertype)
                   } in
    fiat_ethernet_encode fiat_pkt buf sizeof_ethernet sizeof_ethernet

  let fill t buf =
    if !FiatUtils.ethif_encoding_uses_fiat then fill_fiat t buf
    else (check_len buf >>= fun () -> Result.Ok (unsafe_fill t buf))

  let into_cstruct t buf =
    fill t buf

  let make_cstruct t =
    let buf = Cstruct.create sizeof_ethernet in
    Cstruct.memset buf 0x00; (* can be removed in the future *)
    ignore (into_cstruct t buf);
    buf
end

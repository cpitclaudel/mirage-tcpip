type t = {
  src_port : Cstruct.uint16;
  dst_port : Cstruct.uint16;
}

let equal {src_port; dst_port} q =
  src_port = q.src_port &&
  dst_port = q.dst_port

let pp fmt t =
  Format.fprintf fmt "UDP port %d -> %d" t.src_port t.dst_port

module Unmarshal = struct

  type error = string
  open Rresult
  open Udp_wire

  let of_cstruct_mirage _src _dst buf =
    let check_header_length () =
      if Cstruct.len buf < sizeof_udp then Error "UDP header too short" else Ok ()
    in
    let check_payload_length length_from_header length_of_buffer =
      if length_from_header < sizeof_udp then
        Error "UDP header claimed a total length < the size of just the header"
      else begin
        let payload_len = length_from_header - sizeof_udp in
        if payload_len > (length_of_buffer - sizeof_udp)
        then Error (Printf.sprintf
	      "UDP header claimed a payload longer than the supplied buffer: %d vs %d."
              payload_len length_of_buffer)
        else Ok payload_len
      end
    in
    check_header_length () >>= fun () ->
    let total_length_from_header = get_udp_length buf in
    check_payload_length total_length_from_header (Cstruct.len buf) >>= fun payload_len ->
    let src_port = Udp_wire.get_udp_source_port buf in
    let dst_port = Udp_wire.get_udp_dest_port buf in
    let payload = Cstruct.sub buf Udp_wire.sizeof_udp payload_len in
    Ok ({ src_port; dst_port; }, payload)

  let fiat_udp_decode = FiatUtils.make_decoder Fiat4Mirage.fiat_udp_decode

  let of_cstruct_fiat src dst buf =
    FiatUtils.log "udp" "Parsing a UDP segment";
    match fiat_udp_decode buf
            (FiatUtils.ip_to_v4_int64w src)
            (FiatUtils.ip_to_v4_int64w dst)
            (Int64Word.of_uint (Cstruct.len buf)) with
    | Some (pkt: Fiat4Mirage.uDP_Packet) ->
       let src_port = Int64Word.to_int pkt.sourcePort0 in
       let dst_port = Int64Word.to_int pkt.destPort0 in
       Result.Ok ({ src_port; dst_port }, FiatUtils.cstruct_of_char_int64ws pkt.payload0)
    | None ->
       Result.Error (Printf.sprintf "Fiat parsing failed; packet was %s\n" (FiatUtils.cstruct_to_debug_string buf))
    | exception FiatUtils.Fiat_no_ipv6 msg ->
       Result.Error msg

  let of_cstruct =
    if !FiatUtils.udp_decoding_uses_fiat then of_cstruct_fiat
    else of_cstruct_mirage
end
module Marshal = struct
  open Rresult

  type error = string

  let unsafe_fill ~pseudoheader ~payload {src_port; dst_port} udp_buf len =
    let open Udp_wire in
    let udp_buf = Cstruct.sub udp_buf 0 sizeof_udp in
    set_udp_source_port udp_buf src_port;
    set_udp_dest_port udp_buf dst_port;
    set_udp_length udp_buf len;
    set_udp_checksum udp_buf 0;
    (* if we've been passed a buffer larger than sizeof_udp, make sure we
     * consider only the portion which will actually contain the header
     * when calculating this bit of the checksum *)
    let csum = Tcpip_checksum.ones_complement_list [ pseudoheader ; udp_buf ; payload ] in
    (* Convert zero checksum to the equivalent 0xffff, to prevent it
     * seeming like no checksum at all. From RFC768: "If the computed
     * checksum is zero, it is transmitted as all ones (the equivalent
     * in one's complement arithmetic)."  *)
    let csum = if csum = 0 then 0xffff else csum in
    set_udp_checksum udp_buf csum

  let into_cstruct ~pseudoheader ~payload t udp_buf =
    let open Udp_wire in
    let check_header_len () =
      if (Cstruct.len udp_buf) < sizeof_udp then Error "Not enough space for a UDP header"
      else Ok ()
    in
    let check_overall_len () =
      let needed = sizeof_udp in
      let provided = Cstruct.len udp_buf in
      if provided < needed then
        Error (Printf.sprintf "Not enough space for UDP header: provided %d, need %d" provided needed)
      else Ok ((Cstruct.len payload) + sizeof_udp)
    in
    check_header_len () >>= check_overall_len >>= fun len ->
    let buf = Cstruct.sub udp_buf 0 Udp_wire.sizeof_udp in
    unsafe_fill ~pseudoheader ~payload t buf len;
    Ok ()

  let make_cstruct ~pseudoheader ~payload t =
    let buf = Cstruct.create Udp_wire.sizeof_udp in
    let len = Udp_wire.sizeof_udp + Cstruct.len payload in
    unsafe_fill ~pseudoheader ~payload t buf len;
    buf
end

type t = {
  urg : bool;
  ack : bool;
  psh : bool;
  rst : bool;
  syn : bool;
  fin : bool;
  window : Cstruct.uint16;
  options : Options.t list;
  sequence : Sequence.t;
  ack_number : Sequence.t;
  src_port : Cstruct.uint16;
  dst_port : Cstruct.uint16;
}

let equal {urg; ack; psh; rst; syn; fin; window; options; sequence; ack_number;
           src_port; dst_port} q =
  src_port = q.src_port &&
  dst_port = q.dst_port &&
  window = q.window &&
  urg = q.urg && ack = q.ack && psh = q.psh && rst = q.rst && syn = q.syn && fin = q.fin &&
  Sequence.compare sequence q.sequence = 0 &&
  Sequence.compare ack_number q.ack_number = 0 &&
  List.for_all2 Options.equal options q.options

let pp fmt t =
  Format.fprintf fmt
    "TCP packet seq=%a acknum=%a ack=%b rst=%b syn=%b fin=%b win=%d options=%a"
    Sequence.pp t.sequence Sequence.pp t.ack_number
    t.ack t.rst t.syn t.fin t.window Options.pps t.options

module Unmarshal = struct
  open Rresult

  type error = string

  let of_cstruct_mirage _src _dst pkt =
    let open Tcp_wire in
    let check_len pkt =
      if Cstruct.len pkt < sizeof_tcp then
        Error "packet too short to contain a TCP packet of any size"
      else
        Ok (Tcp_wire.get_data_offset pkt)
    in
    let long_enough data_offset = if Cstruct.len pkt < data_offset then
        Error "packet too short to contain a TCP packet of the size claimed"
      else
        Ok ()
    in
    let options data_offset pkt =
      if data_offset > 20 then
        Options.unmarshal (Cstruct.sub pkt sizeof_tcp (data_offset - sizeof_tcp))
      else if data_offset < 20 then
        Error "data offset was unreasonably short; TCP header can't be valid"
      else (Ok [])
    in
    check_len pkt >>= fun data_offset ->
    long_enough data_offset >>= fun () ->
    options data_offset pkt >>= fun options ->
    let sequence = get_tcp_sequence pkt |> Sequence.of_int32 in
    let ack_number = get_tcp_ack_number pkt |> Sequence.of_int32 in
    let urg = get_urg pkt in
    let ack = get_ack pkt in
    let psh = get_psh pkt in
    let rst = get_rst pkt in
    let syn = get_syn pkt in
    let fin = get_fin pkt in
    let window = get_tcp_window pkt in
    let src_port = get_tcp_src_port pkt in
    let dst_port = get_tcp_dst_port pkt in
    let data = Cstruct.shift pkt data_offset in
    Ok ({ urg; ack; psh; rst; syn; fin; window; options;
          sequence; ack_number; src_port; dst_port }, data)

  let fiat_tcp_decode = FiatUtils.make_decoder Fiat4Mirage.fiat_tcp_decode

  let of_cstruct_fiat src dst buf =
    FiatUtils.log "tcp" "Parsing a TCP segment";
    match fiat_tcp_decode buf
            (FiatUtils.ipv4_to_bytestring src)
            (FiatUtils.ipv4_to_bytestring dst)
            (Int64Word.of_int (Cstruct.len buf)) with
    | Some (pkt: Fiat4Mirage.tCP_Packet) ->
       let sequence = pkt.seqNumber |> Int64Word.to_uint32 |> Sequence.of_int32 in
       let ack_number = pkt.ackNumber |> Int64Word.to_uint32 |> Sequence.of_int32 in
       let urg = (match pkt.urgentPointer with Some _ -> true | None -> false) in
       let ack, psh, rst, syn, fin = pkt.aCK, pkt.pSH, pkt.rST, pkt.sYN, pkt.fIN in
       let window = Int64Word.to_int pkt.windowSize in
       let src_port = Int64Word.to_int pkt.sourcePort in
       let dst_port = Int64Word.to_int pkt.destPort in
       Options.unmarshal (FiatUtils.cstruct_of_uint32_int64ws pkt.options0) >>= fun options ->
       Result.Ok ({ urg; ack; psh; rst; syn; fin; window; options;
                    sequence; ack_number; src_port; dst_port },
                  FiatUtils.cstruct_of_payload pkt.payload)
    | None ->
       Result.Error (Printf.sprintf "Fiat parsing failed; packet was %s\n"
                       (FiatUtils.cstruct_to_debug_string buf))
    | exception FiatUtils.Fiat_no_ipv6 msg ->
       Result.Error msg

  let of_cstruct =
    if !FiatUtils.tcp_decoding_uses_fiat then of_cstruct_fiat
    else of_cstruct_mirage
end
module Marshal = struct
  open Rresult
  open Tcp_wire

  type error = string

  let unsafe_fill_mirage ~pseudoheader ~payload t buf options_len =
    let pseudoheader = pseudoheader () in
    let data_off = sizeof_tcp + options_len in
    let buf = Cstruct.sub buf 0 data_off in
    set_tcp_src_port buf t.src_port;
    set_tcp_dst_port buf t.dst_port;
    set_tcp_sequence buf (Sequence.to_int32 t.sequence);
    set_tcp_ack_number buf (Sequence.to_int32 t.ack_number);
    set_data_offset buf (data_off / 4);
    set_tcp_flags buf 0;
    if t.urg then set_urg buf;
    if t.ack then set_ack buf;
    if t.rst then set_rst buf;
    if t.syn then set_syn buf;
    if t.fin then set_fin buf;
    if t.psh then set_psh buf;
    set_tcp_window buf t.window;
    set_tcp_checksum buf 0;
    set_tcp_urg_ptr buf 0;
    (* it's possible we've been passed a buffer larger than the size of the header,
     * which contains some data after the end of the header we'll write;
     * in this case, make sure we compute the checksum properly *)
    let checksum = Tcpip_checksum.ones_complement_list [pseudoheader ; buf ;
                                                        payload] in
    set_tcp_checksum buf checksum;
    ()

  let insert_options options options_frame =
    match options with
    |[] -> Ok 0
    |options ->
      try
        Ok (Options.marshal options_frame options)
      with
      (* handle the case where we ran out of room in the buffer while attempting
           to write the options *)
      | Invalid_argument s -> Error s

  let safe_fill_mirage ~pseudoheader ~payload t buf =
    let check_header_len () =
      if (Cstruct.len buf) < sizeof_tcp then Error "Not enough space for a TCP header"
      else Ok ()
    in
    let check_overall_len header_length =
      if (Cstruct.len buf) < header_length then
        Error (Printf.sprintf "Not enough space for TCP header: %d < %d"
                 (Cstruct.len buf) header_length)
      else Ok ()
    in
    let options_frame = Cstruct.shift buf sizeof_tcp in
    check_header_len () >>= fun () ->
    insert_options t.options options_frame >>= fun options_len ->
    check_overall_len (sizeof_tcp + options_len) >>= fun () ->
    let buf = Cstruct.sub buf 0 (sizeof_tcp + options_len) in
    unsafe_fill_mirage ~pseudoheader ~payload t buf options_len;
    Ok (sizeof_tcp + options_len)

  let fiat_tcp_encode src dst len =
    FiatUtils.make_encoder (fun sz pkt buf -> Fiat4Mirage.fiat_tcp_encode sz pkt src dst len buf)

  let fiat_opts_buf = Cstruct.create 40

  let fill_fiat ~src ~dst ~payload t buf =
    FiatUtils.log "tcp" "Encoding a TCP segment";
    let p = payload in
    insert_options t.options fiat_opts_buf >>= fun options_len ->
    let opts = Cstruct.set_len fiat_opts_buf options_len in
    let fiat_pkt = Fiat4Mirage.{
          sourcePort = Int64Word.of_int t.src_port;
          destPort = Int64Word.of_int t.dst_port;
          seqNumber = Int64Word.of_uint32 (Sequence.to_int32 t.sequence);
          ackNumber = Int64Word.of_uint32 (Sequence.to_int32 t.ack_number);
          nS = false; (* Not supported by Mirage *)
          cWR = false; (* Not supported by Mirage *)
          eCE = false; (* Not supported by Mirage *)
          aCK = t.ack;
          pSH = t.psh;
          rST = t.rst;
          sYN = t.syn;
          fIN = t.fin;
          windowSize = Int64Word.of_int t.window;
          urgentPointer = None; (* Not supported by Mirage *)
          options0 = FiatUtils.uint32_int64ws_of_cstruct opts;
          payload = FiatUtils.payload_of_cstruct p } in
    let header_len = Tcp_wire.sizeof_tcp + options_len in
    let total_len = header_len + Cstruct.len p in
    fiat_tcp_encode
      (FiatUtils.ipv4_to_bytestring src)
      (FiatUtils.ipv4_to_bytestring dst)
      (Int64Word.of_int total_len)
      fiat_pkt buf total_len header_len >>= fun () ->
    Result.Ok header_len

  let into_cstruct ~(src: Ipaddr.t) ~(dst: Ipaddr.t) ~pseudoheader ~payload t buf =
    if !FiatUtils.tcp_encoding_uses_fiat then
      fill_fiat ~src ~dst ~payload t buf
    else
      safe_fill_mirage ~pseudoheader ~payload t buf

  let unsafe_fill ~src ~dst ~pseudoheader ~payload t buf options_len =
    if !FiatUtils.tcp_encoding_uses_fiat then
      ignore (fill_fiat ~src ~dst ~payload t buf)
    else
      unsafe_fill_mirage ~pseudoheader ~payload t buf options_len

  let make_cstruct ~src ~dst ~pseudoheader ~payload t =
    let buf = Cstruct.create (sizeof_tcp + 40) in (* more than 40 bytes of options can't
                                                     be signalled in the length field of
                                                     the tcp header *)
    let options_buf = Cstruct.shift buf sizeof_tcp in
    let options_len = Options.marshal options_buf t.options in
    let buf = Cstruct.set_len buf (sizeof_tcp + options_len) in
    unsafe_fill ~src ~dst ~pseudoheader ~payload t buf options_len;
    buf
end

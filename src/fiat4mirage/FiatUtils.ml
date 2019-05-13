let getenv s =
  try Some (Sys.getenv s) with Not_found -> None

let verbose = ref false
let ipv4_encoding_uses_fiat = ref false
let ipv4_decoding_uses_fiat = ref false
let arpv4_encoding_uses_fiat = ref false
let arpv4_decoding_uses_fiat = ref false
let ethif_encoding_uses_fiat = ref false
let ethif_decoding_uses_fiat = ref false
let udp_encoding_uses_fiat = ref false
let udp_decoding_uses_fiat = ref false
let tcp_encoding_uses_fiat = ref false
let tcp_decoding_uses_fiat = ref false

let nmsgs = ref 0

let src = Logs.Src.create "fiat" ~doc:"Fiat4Mirage"
module Log = (val Logs.src_log src : Logs.LOG)

let log source msg =
  let threshold = 20 in
  if !nmsgs <= threshold || !verbose then (
    Log.info (fun f -> f "[fiat-%s] %s" source msg);
    if !nmsgs = threshold then
      Log.info (fun f -> f "[FIAT] Further messages silenced");
    incr nmsgs
  ) else ()

let _ =
  let params =
    let stream = open_in "/tmp/fiat4mirage.config" in
    let params = Str.split (Str.regexp " +") (input_line stream) in
    close_in stream; params
  in
  verbose := List.mem "verbose" params;
  ipv4_encoding_uses_fiat := List.mem "ipv4-encoding" params;
  ipv4_decoding_uses_fiat := List.mem "ipv4-decoding" params;
  arpv4_encoding_uses_fiat := List.mem "arpv4-encoding" params;
  arpv4_decoding_uses_fiat := List.mem "arpv4-decoding" params;
  ethif_encoding_uses_fiat := List.mem "ethif-encoding" params;
  ethif_decoding_uses_fiat := List.mem "ethif-decoding" params;
  udp_encoding_uses_fiat := List.mem "udp-encoding" params;
  udp_decoding_uses_fiat := List.mem "udp-decoding" params;
  tcp_encoding_uses_fiat := List.mem "tcp-encoding" params;
  tcp_decoding_uses_fiat := List.mem "tcp-decoding" params;
  Printf.printf "[FIAT CONFIG]\n";
  Printf.printf "  verbose:   %b\n" !verbose;
  Printf.printf "  ipv4-enc:  %b\n" !ipv4_encoding_uses_fiat;
  Printf.printf "  ipv4-dec:  %b\n" !ipv4_decoding_uses_fiat;
  Printf.printf "  arpv4-enc: %b\n" !arpv4_encoding_uses_fiat;
  Printf.printf "  arpv4-dec: %b\n" !arpv4_decoding_uses_fiat;
  Printf.printf "  ethif-enc: %b\n" !ethif_encoding_uses_fiat;
  Printf.printf "  ethif-dec: %b\n" !ethif_decoding_uses_fiat;
  Printf.printf "  udp-enc:   %b\n" !udp_encoding_uses_fiat;
  Printf.printf "  udp-dec:   %b\n" !udp_decoding_uses_fiat;
  Printf.printf "  tcp-enc:   %b\n" !tcp_encoding_uses_fiat;
  Printf.printf "  tcp-dec:   %b\n" !tcp_decoding_uses_fiat

let bytes_of_stackvector (v: Int64Word.t StackVector.t) =
   let len = v.StackVector.len in
   let bytes = Bytes.create len in
   for idx = 0 to len - 1 do
     Bytes.unsafe_set bytes idx (Int64Word.to_char (StackVector.nth' v idx))
   done;
   bytes

let stackvector_of_bytes (bytes: bytes) =
  let len = Bytes.length bytes in
  let arr = Array.make len (Int64Word.wzero 8) in
  Bytes.iteri (fun i c -> arr.(len - i - 1) <- Int64Word.of_char c) bytes;
  StackVector.of_rev_array arr

let cstruct_unsafe_get_char (buf: Cstruct.t) idx =
  Bigarray.Array1.unsafe_get buf.buffer (buf.off + idx)

let cstruct_unsafe_set_char (buf: Cstruct.t) idx c =
  Bigarray.Array1.unsafe_set buf.buffer (buf.off + idx) c

let cstruct_to_debug_string (buf: Cstruct.t) : string =
  let repr c =
    Printf.sprintf "\\x%02x" (int_of_char c) in
  let rec loop buf idx acc =
    if idx >= Cstruct.len buf then List.rev acc
    else loop buf (idx + 1) (repr (Cstruct.get_char buf idx) :: acc)
  in "\"" ^ (String.concat "" (loop buf 0 [])) ^ "\""

type bytestring = CstructBytestring.storage_t

let bytestring_to_debug_string (bs: bytestring) : string =
  cstruct_to_debug_string bs.data

(* let bytes_of_bytestring (v: bytestring) =
 *   Cstruct.to_bytes (CstructBytestring.to_cstruct v)
 *
 * let bytestring_of_bytes (bytes: bytes) =
 *   CstructBytestring.of_cstruct (Cstruct.of_bytes bytes) *)

(* let cstruct_of_char_int64ws (chars: Int64Word.t list) =
 *   let bytes = Bytes.create (List.length chars) in
 *   List.iteri (fun idx c -> Bytes.unsafe_set bytes idx (Int64Word.to_char c)) chars;
 *   Cstruct.of_bytes bytes *)

let string_of_char_int64ws (chars: Int64Word.t list) =
  let str = Bytes.create (List.length chars) in
  List.iteri (fun idx c -> Bytes.unsafe_set str idx (Int64Word.to_char c)) chars;
  Bytes.to_string str

let char_int64ws_of_string (s: string) =
  let chars = ref [] in
  for idx = String.length s - 1 downto 0 do
    let c = String.unsafe_get s idx in
    chars := Int64Word.of_char c :: !chars
  done;
  !chars

(* let char_int64ws_of_cstruct cstruct =
 *   let chars = ref [] in
 *   for idx = Cstruct.len cstruct - 1 downto 0 do
 *     let c = cstruct_unsafe_get_char cstruct idx in
 *     chars := Int64Word.of_char c :: !chars
 *   done;
 *   !chars *)

(* let bytes_of_bytestring ?(start = 0) ?(len = max_int) (bs: bytestring) =
 *   let int64ws = ArrayVector.to_array bs in
 *   let len = min len (Array.length int64ws - start) in
 *   let bytes = Bytes.create len in
 *   for idx = 0 to len - 1 do
 *     Bytes.unsafe_set bytes idx (Int64Word.to_char int64ws.(start + idx))
 *   done;
 *   bytes *)

(* let bytestring_of_bytes (bytes: bytes) =
 *   CstructBytestring.of_cstruct (Cstruct.of_bytes bytes) *)

let cstruct_blit_from_bytestring bytestring bsoff cstruct csoff len =
  Cstruct.blit (CstructBytestring.to_cstruct bytestring) bsoff cstruct csoff len

let bytestring_of_cstruct buf =
  CstructBytestring.of_cstruct buf

let cstruct_of_bytestring (bytestring: bytestring) =
  CstructBytestring.to_cstruct bytestring

let payload_of_cstruct buf =
  let b = CstructBytestring.of_cstruct buf in
  Fiat4Mirage.ExistT (CstructBytestring.length b, b)

let cstruct_of_payload (bytestring: ('a, bytestring) Fiat4Mirage.sigT) =
  CstructBytestring.to_cstruct (Fiat4Mirage.projT2 bytestring)

let cstruct_of_uint32_int64ws uint32_int64ws =
  let buf = Cstruct.create (4 * (List.length uint32_int64ws)) in
  List.iteri (fun idx ui32w64 ->
      Cstruct.BE.set_uint32 buf (4 * idx) (Int64Word.to_uint32 ui32w64))
    uint32_int64ws;
  buf

let uint32_int64ws_of_cstruct buf =
  assert (Cstruct.len buf mod 4 == 0);
  let len = Cstruct.len buf / 4 in
  let int64ws = ref [] in
  for idx = len - 1 downto 0 do
    let ui32 = Cstruct.BE.get_uint32 buf (4 * idx) in
    int64ws := (Int64Word.of_uint32 ui32) :: !int64ws
  done;
  !int64ws

let uint32_of_char_int64ws (chars: Int64Word.t list) : Int32.t =
  let open Int32 in
  match chars with
  | [x0; x1; x2; x3] ->
     add (shift_left (Int64Word.to_uint32 x0) 24)
       (add (shift_left (Int64Word.to_uint32 x1) 16)
          (add (shift_left (Int64Word.to_uint32 x2) 8)
             (Int64Word.to_uint32 x3)))
  | _ -> failwith "uint32_of_char_int64ws"

let maskff = Int64Word.Int64.logand (Int64Word.Int64.of_int 0xff)

let char_int64ws_of_uint32 ui32 =
  let w64 = Int64Word.of_uint32 ui32 in
  [maskff (Int64Word.Int64.shift_right_logical w64 24);
   maskff (Int64Word.Int64.shift_right_logical w64 16);
   maskff (Int64Word.Int64.shift_right_logical w64 8);
   maskff (Int64Word.Int64.shift_right_logical w64 0)]

let cstruct_of_uint32 ui32 =
  let buf = Cstruct.create 4 in
  Cstruct.BE.set_uint32 buf 0 ui32;
  buf

exception Fiat_parsing_failed
exception Fiat_incorrect_value
exception Unsupported_by_mirage

let make_encoder (encoder: int -> 'a -> bytestring -> bytestring option) =
  fun (pkt: 'a) (cstruct: Cstruct.t) full_len blit_len ->
  if blit_len > Cstruct.len cstruct then
    Error "Not enough space"
  else
    let needs_blit = full_len <> blit_len in
    let fiat_cstruct = if needs_blit then Cstruct.create full_len else cstruct in
    match encoder full_len pkt (CstructBytestring.of_cstruct fiat_cstruct) with
    | Some bytestring ->
       if needs_blit then
         cstruct_blit_from_bytestring bytestring 0 cstruct 0 blit_len;
       Ok ()
    | None -> Error "Fiat encoding failed"

let make_decoder (decoder: int -> bytestring -> 'a) =
  fun cstruct -> decoder (Cstruct.len cstruct) (bytestring_of_cstruct cstruct)

exception Fiat_no_ipv6 of string

let ipv4_to_bytestring ip =
  match Ipaddr.to_v4 ip with
  | Some v4 -> CstructBytestring.of_cstruct (cstruct_of_uint32 (Ipaddr.V4.to_int32 v4))
  | None -> raise (Fiat_no_ipv6 "Fiat doesn't support IPv6")

(* (* Set to `true` to raise an error if fiat value doesn't match *) *)
(* let validate_fiat_parsing = false *)

(* let get_reference parser printer reference_reader cstruct = *)
(*   (try *)
(*     let pkt = (fst (parser cstruct)) in *)
(*     printer pkt *)
(*   with Fiat_parsing_failed -> print_string "Fiat parsing failed in get_reference"); *)
(*   reference_reader cstruct *)

(* let validate_fiat_result parser printer reference_value fiat_value pkt = *)
(*   if validate_fiat_parsing then () *)
(*   else if fiat_value = reference_value then *)
(*     (print_string "Fiat correctly parsed a value in the following packet: "; *)
(*      printer pkt) *)
(*   else *)
(*     raise Fiat_incorrect_value *)

(* let get_fiat_with_fallback parser printer reference_reader fiat_reader cstruct = *)
(*   let reference_value = reference_reader cstruct in *)
(*   try *)
(*     let pkt = (fst (parser cstruct)) in *)
(*     let fiat_value = fiat_reader pkt in *)
(*     validate_fiat_result parser printer reference_value fiat_value pkt; *)
(*     fiat_value *)
(*   with *)
(*   | Fiat_parsing_failed -> print_string "Fiat parsing failed! Falling back."; reference_value *)
(*   | Fiat_incorrect_value -> failwith "Fiat parsing returned wrong value!" *)

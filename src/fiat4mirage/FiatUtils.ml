let getenv s =
  try Some (Sys.getenv s) with Not_found -> None

let verbose = ref false
let ipv4_uses_fiat = ref false
let arpv4_uses_fiat = ref false
let ethif_uses_fiat = ref false
let udp_uses_fiat = ref false
let tcp_uses_fiat = ref false

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
    let stream = open_in "config.fiat4mirage" in
    let params = Str.split (Str.regexp " +") (input_line stream) in
    close_in stream; params in
  verbose := List.mem "verbose" params;
  ipv4_uses_fiat := List.mem "ipv4" params;
  arpv4_uses_fiat := List.mem "arpv4" params;
  ethif_uses_fiat := List.mem "ethif" params;
  udp_uses_fiat := List.mem "udp" params;
  tcp_uses_fiat := List.mem "tcp" params;
  Printf.printf "[FIAT CONFIG]\n";
  Printf.printf "  verbose: %b\n" !verbose;
  Printf.printf "  ipv4:    %b\n" !ipv4_uses_fiat;
  Printf.printf "  arpv4:   %b\n" !arpv4_uses_fiat;
  Printf.printf "  ethif:   %b\n" !ethif_uses_fiat;
  Printf.printf "  udp:     %b\n" !udp_uses_fiat;
  Printf.printf "  tcp:     %b\n" !tcp_uses_fiat

(* let cstruct_of_fiat_char_list (chars: Int64.t list) =
 *   let bytes = Bytes.create (List.length chars) in
 *   List.iteri (fun idx c -> Bytes.unsafe_set bytes idx (char_of_fiat_char c)) chars;
 *   Cstruct.of_bytes bytes
 *
 * let fiat_char_list_of_cstruct cstruct =
 *   let chars = ref [] in
 *   for idx = 0 to Cstruct.len cstruct - 1 do
 *     chars := Cstruct.get_char cstruct idx :: !chars
 *   done;
 *   List.rev_map fiat_char_of_char !chars *)

let bytestring_of_cstruct cstruct =
  let int64ws = Array.make (Cstruct.len cstruct) Int64Word.w0 in
  for idx = 0 to Cstruct.len cstruct - 1 do
    let c = Cstruct.get_char cstruct idx in
    Array.unsafe_set int64ws idx (Int64Word.of_char c)
  done;
  ArrayVector.of_array int64ws

let cstruct_of_bytestring (bytestring: Int64Word.t ArrayVector.storage_t) =
  let int64ws = ArrayVector.to_array bytestring in
  let bytes = Bytes.create (Array.length int64ws) in
  for idx = 0 to Array.length int64ws - 1 do
    Bytes.unsafe_set bytes idx (Int64Word.to_char int64ws.(idx))
  done;
  Cstruct.of_bytes bytes

let string_of_chars chars =
  let str = Bytes.create (List.length chars) in
  List.iteri (fun idx c -> Bytes.set str idx c) chars;
  Bytes.to_string str

let cstruct_of_uint32s uint32s =
  let buf = Cstruct.create (4 * (List.length uint32s)) in
  List.iteri (fun idx ui32 -> Cstruct.BE.set_uint32 buf (4 * idx) ui32) uint32s;
  buf

let string_of_fiat_chars chars =
  string_of_chars (List.map Int64Word.to_char chars)

let to_char i64 = char_of_int (Int64.to_int i64)
let of_char c = Int64.of_int (int_of_char c)

let uint32_of_fiat_chars chars =
  match chars with
  | [x0; x1; x2; x3] ->
     (* CPC simplify this *)
     Int64.to_int32
       (List.fold_left Int64.add Int64.zero
                       (List.map (fun (x, s) -> Int64.shift_left x (8 * s))
                                 [(x0, 3); (x1, 2); (x2, 1); (x3, 0)]))
  | _ -> failwith "uint32_of_fiat_chars"

exception Fiat_parsing_failed
exception Fiat_incorrect_value
exception Unsupported_by_mirage

let make_decoder (f: int -> Int64Word.t ArrayVector.storage_t -> 'a) =
  fun cstruct -> f (Cstruct.len cstruct) (bytestring_of_cstruct cstruct)

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

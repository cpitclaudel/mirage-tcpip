open Lwt.Infix

let time_reduction_factor = 60.

module Fast_clock = struct

  let last_read = ref (Clock.time ())

  (* from mirage/types/V1.mli module type CLOCK *)
  type tm =
    { tm_sec: int;               (** Seconds 0..60 *)
      tm_min: int;               (** Minutes 0..59 *)
      tm_hour: int;              (** Hours 0..23 *)
      tm_mday: int;              (** Day of month 1..31 *)
      tm_mon: int;               (** Month of year 0..11 *)
      tm_year: int;              (** Year - 1900 *)
      tm_wday: int;              (** Day of week (Sunday is 0) *)
      tm_yday: int;              (** Day of year 0..365 *)
      tm_isdst: bool;            (** Daylight time savings in effect *)
    }

  let gmtime time = 
    let tm = Clock.gmtime time in
    { 
      tm_sec = tm.Clock.tm_sec;
      tm_min = tm.Clock.tm_min;
      tm_hour = tm.Clock.tm_hour;
      tm_mday = tm.Clock.tm_mday;
      tm_mon = tm.Clock.tm_mon;
      tm_year = tm.Clock.tm_year;
      tm_wday = tm.Clock.tm_wday;
      tm_yday = tm.Clock.tm_yday;
      tm_isdst = tm.Clock.tm_isdst;
    }

  let time () = 
    let this_time = Clock.time () in
    let clock_diff = ((this_time -. !last_read) *. time_reduction_factor) in
    last_read := this_time;
    this_time +. clock_diff

end
module Fast_time = struct
  type 'a io = 'a Lwt.t
  let sleep time = OS.Time.sleep (time /. time_reduction_factor)
end

module B = Basic_backend.Make
module V = Vnetif.Make(B)
module E = Ethif.Make(V)
module A = Arpv4.Make(E)(Fast_clock)(Fast_time)

type arp_stack = {
  backend : B.t;
  netif: V.t;
  ethif: E.t;
  arp: A.t;
}

let first_ip = Ipaddr.V4.of_string_exn "192.168.3.1"
let second_ip = Ipaddr.V4.of_string_exn "192.168.3.10"
let sample_mac = Macaddr.of_string_exn "10:9a:dd:c0:ff:ee"

let packet = (module Arpv4_packet : Alcotest.TESTABLE with type t = Arpv4_packet.t)
let ip =
  let module M = struct
    type t = Ipaddr.V4.t
    let pp = Ipaddr.V4.pp_hum
    let equal p q = (Ipaddr.V4.compare p q) = 0
  end in
  (module M : Alcotest.TESTABLE with type t = M.t)

let macaddr =
  let module M = struct
    type t = Macaddr.t
    let pp fmt t = Format.fprintf fmt "%s" (Macaddr.to_string t)
    let equal p q = (Macaddr.compare p q) = 0
  end in
  (module M : Alcotest.TESTABLE with type t = M.t)

let check_header ~message expected actual =
  Alcotest.(check packet) message expected actual

let or_error = Common.or_error
let fail = Alcotest.fail

let timeout ~time t =
  let msg = Printf.sprintf "Timed out: didn't complete in %f seconds" time in
  Lwt.pick [ t; OS.Time.sleep time >>= fun () -> fail msg; ]

let check_response expected buf =
  match Arpv4_packet.Unmarshal.of_cstruct buf with
  | Result.Error s -> Alcotest.fail (Arpv4_packet.Unmarshal.string_of_error s)
  | Result.Ok actual ->
    Alcotest.(check packet) "parsed packet comparison" expected actual

let check_ethif_response expected buf =
  match Ethif_packet.Unmarshal.of_cstruct buf with
  | Result.Error s -> Alcotest.fail s
  | Result.Ok ({ethertype; _}, arp) ->
    match ethertype with
    | Ethif_wire.ARP -> check_response expected arp
    | _ -> Alcotest.fail "Ethernet packet with non-ARP ethertype"

let garp src_mac src_ip =
  let open Arpv4_packet in
  {
    op = Arpv4_wire.Reply;
    sha = src_mac;
    tha = Macaddr.broadcast;
    spa = src_ip;
    tpa = Ipaddr.V4.any;
  }

let fail_on_receipt netif buf = 
  fail "received traffic when none was expected"

let single_check netif expected =
  V.listen netif (fun buf ->
      match Ethif_packet.Unmarshal.of_cstruct buf with
      | Result.Error _ -> failwith "sad face"
      | Result.Ok (_, payload) ->
        check_response expected payload; V.disconnect netif)

let wrap_arp arp =
  let open Arpv4_packet in
  let e = 
    { Ethif_packet.source = arp.sha;
      destination = arp.tha;
      ethertype = Ethif_wire.ARP;
    } in
  let p = Ethif_packet.Marshal.make_cstruct e in
  Format.printf "%a" Ethif_packet.pp e;
  Cstruct.hexdump p;
  p

let arp_reply ~from_netif ~to_netif ~from_ip ~to_ip =
  let a = 
    { Arpv4_packet.op = Arpv4_wire.Reply; 
      sha = (V.mac from_netif); 
      tha = (V.mac to_netif);
      spa = from_ip;
      tpa = to_ip} 
  in
  Cstruct.concat [wrap_arp a; Arpv4_packet.Marshal.make_cstruct a]

let arp_request ~from_netif ~to_mac ~from_ip ~to_ip =
  let a =
    { Arpv4_packet.op = Arpv4_wire.Request; 
      sha = (V.mac from_netif); 
      tha = to_mac;
      spa = from_ip;
      tpa = to_ip} 
  in
  Cstruct.concat [wrap_arp a; Arpv4_packet.Marshal.make_cstruct a]

let get_arp ?(backend = B.create ~use_async_readers:true 
                ~yield:(fun() -> Lwt_main.yield ()) ()) () =
  or_error "backend" V.connect backend >>= fun netif ->
  or_error "ethif" E.connect netif >>= fun ethif ->
  or_error "arp" A.connect ethif >>= fun arp ->
  Lwt.return { backend; netif; ethif; arp }

(* we almost always want two stacks on the same backend *)
let two_arp () =
  get_arp () >>= fun first ->
  get_arp ~backend:first.backend () >>= fun second ->
  Lwt.return (first, second)

(* ...but sometimes we want three *)
let three_arp () =
  get_arp () >>= fun first ->
  get_arp ~backend:first.backend () >>= fun second ->
  get_arp ~backend:first.backend () >>= fun third ->
  Lwt.return (first, second, third)

let query_or_die ~arp ~ip ~expected_mac = 
  A.query arp ip >>= function
  | `Timeout ->
    let pp_ip = Ipaddr.V4.to_string ip in
    Format.printf "Timeout querying %s." pp_ip;
    A.to_repr arp >>= fun repr ->
    A.pp Format.std_formatter repr;
    fail "ARP query failed when success was mandatory";
    Lwt.return_unit
  | `Ok mac -> 
    Alcotest.(check macaddr) "mismatch for expected query value" expected_mac mac;
    Lwt.return_unit

let set_and_check listener claimant ip =
  A.set_ips claimant.arp [ ip ] >>= fun () ->
  query_or_die listener ip (V.mac claimant.netif)

let start_arp_listener stack () =
  let noop = (fun buf -> Lwt.return_unit) in
  E.input ~arpv4:(A.input stack.arp) ~ipv4:noop ~ipv6:noop stack.ethif

let output_then_disconnect ~speak:speak_netif ~disconnect:listen_netif bufs =
  Lwt.join (List.map (V.write speak_netif) bufs) >>= fun () ->
  Lwt_unix.sleep 0.1 >>= fun () ->
  V.disconnect listen_netif

let not_in_cache ~listen probe arp ip =
  Lwt.pick [
    single_check listen probe;
    OS.Time.sleep 0.1 >>= fun () ->
    A.query arp ip >>= function
    | `Ok mac -> fail "entry in cache when it shouldn't be"
    | `Timeout -> Lwt.return_unit
  ]

let set_ip_sends_garp () =
  two_arp () >>= fun (speak, listen) ->
  let emit_garp =
    OS.Time.sleep 0.1 >>= fun () ->
    A.set_ips speak.arp [ first_ip ] >>= fun () ->
    Alcotest.(check (list ip)) "garp emitted when setting ip" [ first_ip ] (A.get_ips speak.arp);
    Lwt.return_unit
  in
  let expected_garp = garp (V.mac speak.netif) first_ip in
  timeout ~time:0.5 (
  Lwt.join [
    single_check listen.netif expected_garp;
    emit_garp;
  ]) >>= fun () ->
  (* now make sure we have consistency when setting *)
  A.set_ips speak.arp [] >>= fun () ->
  Alcotest.(check (list ip)) "list of bound IPs on initialization" [] (A.get_ips speak.arp);
  A.set_ips speak.arp [ first_ip; second_ip ] >>= fun () ->
  Alcotest.(check (list ip)) "list of bound IPs after setting two IPs"
    [ first_ip; second_ip ] (A.get_ips speak.arp);
  Lwt.return_unit

let add_get_remove_ips () =
  get_arp () >>= fun stack ->
  let check str expected =
    Alcotest.(check (list ip)) "set ips with duplicate elements result in deduplication"
      expected (A.get_ips stack.arp)
  in
  check "bound ips is an empty list on startup" [];
  A.set_ips stack.arp [ first_ip; first_ip ] >>= fun () ->
  let ips = A.get_ips stack.arp in
  check "set ips with duplicate elements result in deduplication" [first_ip];
  A.remove_ip stack.arp first_ip >>= fun () ->
  check "ip list is empty after removing only ip" [];
  A.remove_ip stack.arp first_ip >>= fun () ->
  check "ip list is empty after removing from empty list" [];
  A.add_ip stack.arp first_ip >>= fun () ->
  check "first ip is the only member of the set of bound ips" [first_ip];
  A.add_ip stack.arp first_ip >>= fun () ->
  check "adding ips is idempotent" [first_ip];
  Lwt.return_unit

let input_single_garp () =
  two_arp () >>= fun (listen, speak) ->
  (* set the IP on speak_arp, which should cause a GARP to be emitted which
     listen_arp will hear and cache. *)
  let one_and_done buf =
    let arpbuf = Cstruct.shift buf 14 in
    A.input listen.arp arpbuf >>= fun () ->
    V.disconnect listen.netif 
  in
  timeout ~time:0.5 (
  Lwt.join [
    V.listen listen.netif one_and_done;
    OS.Time.sleep 0.1 >>= fun () ->
    A.set_ips speak.arp [ first_ip ];
  ])
  >>= fun () ->
  (* try a lookup of the IP set by speak.arp, and fail if this causes listen_arp
     to block or send an ARP query -- listen_arp should answer immediately from
     the cache.  An attempt to resolve via query will result in a timeout, since
     speak.arp has no listener running and therefore won't answer any arp
     who-has requests. *)
  timeout ~time:0.5 (query_or_die listen.arp first_ip (V.mac speak.netif))

let input_single_unicast () =
  two_arp () >>= fun (listen, speak) ->
  (* contrive to make a reply packet for the listener to hear *)
  let for_listener = arp_reply 
     ~from_netif:speak.netif ~to_netif:listen.netif ~from_ip:first_ip ~to_ip:second_ip
  in
  let listener = start_arp_listener listen () in
  timeout ~time:0.5 (
  Lwt.choose [
    V.listen listen.netif listener;
    OS.Time.sleep 0.1 >>= fun () ->
    V.write speak.netif for_listener >>= fun () ->
    query_or_die listen.arp first_ip (V.mac speak.netif)
  ])

let input_resolves_wait () =
  two_arp () >>= fun (listen, speak) ->
  (* contrive to make a reply packet for the listener to hear *)
  let for_listener = arp_reply ~from_netif:speak.netif ~to_netif:listen.netif
                         ~from_ip:first_ip ~to_ip:second_ip in
  (* initiate query when the cache is empty.  On resolution, fail for a timeout
     and test the MAC if resolution was successful, then disconnect the
     listening interface to ensure the test terminates.  
     Fail with a timeout message if the whole thing takes more than 5s. *)
  let listener = start_arp_listener listen () in
  let query_then_disconnect = 
    query_or_die listen.arp first_ip (V.mac speak.netif) >>= fun () ->
    V.disconnect listen.netif
  in
  timeout ~time:5.0 (
    Lwt.join [
      V.listen listen.netif listener;
      query_then_disconnect;
      OS.Time.sleep 0.1 >>= fun () -> E.write speak.ethif for_listener;
    ]
  )

let unreachable_times_out () =
  get_arp () >>= fun speak ->
  A.query speak.arp first_ip >>= function
  | `Ok mac -> fail "query claimed success when impossible"
  | `Timeout -> Lwt.return_unit

let input_replaces_old () =
  three_arp () >>= fun (listen, claimant_1, claimant_2) ->
  let listener = start_arp_listener listen () in
  timeout ~time:2.0 (
    Lwt.join [
      V.listen listen.netif listener;
      OS.Time.sleep 0.1 >>= fun () ->
      set_and_check listen.arp claimant_1 first_ip >>= fun () ->
      set_and_check listen.arp claimant_2 first_ip >>= fun () ->
      V.disconnect listen.netif
    ])

let entries_expire () =
  two_arp () >>= fun (listen, speak) ->
  A.set_ips listen.arp [ second_ip ] >>= fun () ->
  (* here's what we expect listener to emit once its cache entry has expired *)
  let expected_arp_query =
    Arpv4_packet.({op = Arpv4_wire.Request;
                   sha = (V.mac listen.netif); tha = Macaddr.broadcast;
                   spa = second_ip; tpa = first_ip})
  in
  Lwt.async (fun () -> 
      V.listen listen.netif (start_arp_listener listen ()));
  let test =
    OS.Time.sleep 0.1 >>= fun () ->
    set_and_check listen.arp speak first_ip >>= fun () ->
    OS.Time.sleep 1.0 >>= fun () ->
    (* asking now should generate a query *)
    not_in_cache ~listen:speak.netif expected_arp_query listen.arp first_ip;
  in
  timeout ~time:5.0 test

(* RFC isn't strict on how many times to try, so we'll just say any number
   greater than 1 is fine *)
let query_retries () =
  two_arp () >>= fun (listen, speak) ->
  let expected_query = Arpv4_packet.({sha = (V.mac speak.netif);
                                      tha = Macaddr.broadcast;
                                      spa = Ipaddr.V4.any;
                                      tpa = first_ip;
                                      op  = Arpv4_wire.Request;})
  in
  let how_many = ref 0 in
  let rec listener buf =
    check_ethif_response expected_query buf;
    if !how_many = 0 then begin
      how_many := !how_many + 1;
      Lwt.return_unit
    end else V.disconnect listen.netif
  in
  let ask () = 
    A.query speak.arp first_ip >>= function
    | `Timeout -> fail "Received `Timeout before >1 query";
      Lwt.return_unit
    | `Ok mac -> fail "got result from query, erroneously";
      Lwt.return_unit
  in
  Lwt.pick [
    V.listen listen.netif listener;
    OS.Time.sleep 0.1 >>= ask;
    OS.Time.sleep 6.0 >>= fun () -> fail "query didn't succeed or fail within 6s"
  ]

(* requests for us elicit a reply *)
let requests_are_responded_to () =
  let (answerer_ip, inquirer_ip) = (first_ip, second_ip) in
  two_arp () >>= fun (inquirer, answerer) ->
  (* neither has a listener set up when we set IPs, so no GARPs in the cache *)
  A.add_ip answerer.arp answerer_ip >>= fun () ->
  A.add_ip inquirer.arp inquirer_ip >>= fun () ->
  let request = arp_request ~from_netif:inquirer.netif ~to_mac:Macaddr.broadcast
      ~from_ip:inquirer_ip ~to_ip:answerer_ip
  in
  let expected_reply =
    { Arpv4_packet.op = Arpv4_wire.Reply;
      sha = (V.mac answerer.netif); tha = (V.mac inquirer.netif);
      spa = answerer_ip; tpa = inquirer_ip}
  in
  let listener close_netif buf =
    check_ethif_response expected_reply buf;
    V.disconnect close_netif
  in
  let arp_listener =
      V.listen answerer.netif (start_arp_listener answerer ())
  in
  timeout ~time:1.0 (
    Lwt.join [
      (* listen for responses and check them against an expected result *)
      V.listen inquirer.netif (listener inquirer.netif);
      (* start the usual ARP listener, which should respond to requests *)
      arp_listener;
      (* send a request for the ARP listener to respond to *)
      OS.Time.sleep 0.1 >>= fun () -> V.write inquirer.netif request
      >>= fun () -> OS.Time.sleep 0.1 >>= fun () -> V.disconnect answerer.netif
    ];
  )

let requests_not_us () =
  let (answerer_ip, inquirer_ip) = (first_ip, second_ip) in
  two_arp () >>= fun (answerer, inquirer) ->
  A.add_ip answerer.arp answerer_ip >>= fun () ->
  A.add_ip inquirer.arp inquirer_ip >>= fun () ->
  let ask ip =
    Arpv4_packet.Marshal.make_cstruct @@
    { Arpv4_packet.op = Arpv4_wire.Request;
      sha = (V.mac inquirer.netif); tha = Macaddr.broadcast;
      spa = inquirer_ip; tpa = ip }
  in
  let requests = List.map ask [ inquirer_ip; Ipaddr.V4.any;
                                Ipaddr.V4.of_string_exn "255.255.255.255" ] in
  let make_requests = Lwt_list.iter_s (V.write inquirer.netif) requests in
  let disconnect_listeners () = 
    Lwt_list.iter_s (V.disconnect) [answerer.netif; inquirer.netif]
  in
  Lwt.join [
    V.listen answerer.netif (start_arp_listener answerer ());
    V.listen inquirer.netif (fail_on_receipt inquirer.netif);
    make_requests >>= fun () -> OS.Time.sleep 0.1 >>= disconnect_listeners
  ]

let nonsense_requests () =
  let (answerer_ip, inquirer_ip) = (first_ip, second_ip) in
  three_arp () >>= fun (answerer, inquirer, checker) ->
  A.set_ips answerer.arp [ answerer_ip ] >>= fun () ->
  let request number =
    let buf = Arpv4_packet.Marshal.make_cstruct @@
    { op = Arpv4_wire.Request; sha = (V.mac inquirer.netif); tha = Macaddr.broadcast;
      spa = inquirer_ip; tpa = answerer_ip } in
    Arpv4_wire.set_arp_op buf number;
    let eth_header = { Ethif_packet.source = (V.mac inquirer.netif);
                       destination = Macaddr.broadcast; 
                       ethertype = Ethif_wire.ARP;
                       } in
    Cstruct.concat [ Ethif_packet.Marshal.make_cstruct eth_header; buf ]
  in
  let requests = List.map request [0; 3; -1; 255; 256; 257; 65536] in
  let make_requests = Lwt_list.iter_s (fun l ->
      V.write inquirer.netif l) requests in
  let expected_probe = { Arpv4_packet.op = Arpv4_wire.Request;
                         sha = V.mac answerer.netif;
                         spa = answerer_ip;
                         tha = Macaddr.broadcast;
                         tpa = inquirer_ip; }
  in
  Lwt.async (fun () -> 
      V.listen answerer.netif (start_arp_listener answerer ()));
  timeout ~time:1.0 (
    Lwt.join [
      V.listen inquirer.netif (fail_on_receipt inquirer.netif);
      make_requests >>= fun () ->
      V.disconnect inquirer.netif >>= fun () ->
      (* not sufficient to just check to see whether we've replied; it's equally
         possible that we erroneously make a cache entry.  Make sure querying
         inquirer_ip results in an outgoing request. *)
      not_in_cache ~listen:checker.netif expected_probe answerer.arp inquirer_ip
    ] )

let packet () =
  let first_mac  = Macaddr.of_string_exn "10:9a:dd:01:23:45" in
  let second_mac = Macaddr.of_string_exn "00:16:3e:ab:cd:ef" in
  let example_request = Arpv4_packet.({op = Arpv4_wire.Request;
                               sha = first_mac;
                               tha = second_mac;
                               spa = first_ip;
                               tpa = second_ip;
                                      }) in
  let marshalled = Arpv4_packet.Marshal.make_cstruct example_request in
  match Arpv4_packet.Unmarshal.of_cstruct marshalled with
  | Result.Error _ -> Alcotest.fail "couldn't unmarshal something we made ourselves"
  | Result.Ok unmarshalled ->
    Alcotest.(check packet) "serialize/deserialize" example_request unmarshalled;
    Lwt.return_unit

let suite =
  [
    "conversions neither lose nor gain information", `Quick, packet;
    "nonsense requests are ignored", `Quick, nonsense_requests;
    "requests are responded to", `Quick, requests_are_responded_to;
    "irrelevant requests are ignored", `Quick, requests_not_us;
    "set_ip sets ip, sends GARP", `Quick, set_ip_sends_garp;
    "add_ip, get_ip and remove_ip as advertised", `Quick, add_get_remove_ips;
    "GARPs are heard and cached", `Quick, input_single_garp;
    "unsolicited unicast replies are heard and cached", `Quick, input_single_unicast;
    "solicited unicast replies resolve pending threads", `Quick, input_resolves_wait;
    "entries are replaced with new information", `Quick, input_replaces_old;
    "unreachable IPs time out", `Quick, unreachable_times_out;
    "queries are tried repeatedly before timing out", `Quick, query_retries;
    "entries expire", `Quick, entries_expire;
  ]

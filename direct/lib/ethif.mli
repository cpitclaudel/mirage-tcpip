(*
 * Copyright (c) 2010-2011 Anil Madhavapeddy <anil@recoil.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 *)

(** Module Ethif is used to represent an ethernet protocol interface,
    using the underlying OS.Netif *)

open Nettypes

(** {1 Types} *)

(** Type for an ethernet protocol interface. It contains a OS.Netif.t
    "raw" interface, as well as IPv4 and ARP callbacks to perform IP
    or ARP operations on this interface. *)
type t

type packet =
| Input of Cstruct.t       (** always read as a whole chunk *)
| Output of Cstruct.t list (** written as a list of fragments *)

(** {2 Values} *)

(** [create netif] creates a value of type t out of a [netif] value,
    and calls [listen] on the result. It returns a tuple composed of a
    value of type t, and the result of the [listen] function that has
    been called on it. *)
val create : OS.Netif.t -> t * unit Lwt.t

(** Functions to set up callback for processing an IPv4 packet. By
    default, [create] ignores all received packets, so use [attach] to
    start doing something useful with the packet you receive. [detach]
    will replace the callback installed with [attach] by the default
    callback that does nothing. *)

val attach : t -> [< `IPv4 of Cstruct.t -> unit Lwt.t ] -> unit
val detach : t -> [< `IPv4 ] -> unit

(** Accessors for t values *)

val mac       : t -> Nettypes.ethernet_mac
val get_netif : t -> OS.Netif.t


(** [set_promiscuous ethif cb] will install [cb] as a callback to be
    called every time a packet is received *)
val set_promiscuous : t -> (packet -> unit Lwt.t) -> unit

(** [disable_promiscuous ethif] removes the callback associated with
    promiscuous mode in [ethif] *)
val disable_promiscuous : t -> unit

(** [default_process ethif frame] is called by function [input]
    whenever promiscuous mode is disabled (e.g. when no promiscuous
    callback function has been set) *)
val default_process : t -> Cstruct.t -> unit Lwt.t

(** [input ethif frame] processes the incoming data from [frame]
    coming from [ethif]. It either call [default_process] if the
    promiscuous mode is disabled, otherwise call the promiscuous
    callback function *)
val input : t -> Cstruct.t -> unit Lwt.t

(** [listen ethif] will loop on interface [ethif] waiting for incoming
    frames, and will use the [input] function to process them. *)
val listen : t -> unit Lwt.t


(** Functions related to the ARP protocol, and applied to the arp
    value contained inside [t]. Please refer to the documentation of
    module [Arp] for more information. *)

val add_ip : t -> Nettypes.ipv4_addr -> unit Lwt.t
val remove_ip : t -> Nettypes.ipv4_addr -> unit Lwt.t
val query_arp : t -> Nettypes.ipv4_addr -> Nettypes.ethernet_mac Lwt.t


(** Low-level functions to interact with the value of type [Netif.t]
    embedded into [t]. Please refer to the documentation of module
    [OS.Netif] for more information. *)

val get_frame : t -> Cstruct.t Lwt.t
val write : t -> Cstruct.t -> unit Lwt.t
val writev : t -> Cstruct.t list -> unit Lwt.t


val sizeof_ethernet : int
val set_ethernet_dst : string -> int -> Cstruct.t -> unit
val set_ethernet_src : string -> int -> Cstruct.t -> unit
val set_ethernet_ethertype : Cstruct.t -> int -> unit



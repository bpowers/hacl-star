module Hacl.Impl.Shorthash.SipHash24

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.HyperStack.ST
open FStar.Buffer

open C.Loops

open Hacl.Spec.Endianness
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32
open Hacl.UInt64
open FStar.UInt64


(* Definition of aliases for modules *)
module ST = FStar.HyperStack.ST
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module Spec = Spec.Shorthash.SipHash24


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint32_ht = Hacl.UInt32.t
private let uint64_ht = Hacl.UInt64.t

private let uint32_p = Buffer.buffer uint32_ht
private let uint8_p  = Buffer.buffer uint8_ht


(* Definitions of aliases for functions *)
[@"substitute"]
private let u8_to_h8 = Hacl.Cast.uint8_to_sint8
[@"substitute"]
private let u32_to_h32 = Hacl.Cast.uint32_to_sint32
[@"substitute"]
private let u32_to_h64 = Hacl.Cast.uint32_to_sint64
[@"substitute"]
private let h32_to_h8  = Hacl.Cast.sint32_to_sint8
[@"substitute"]
private let h32_to_h64 = Hacl.Cast.sint32_to_sint64
[@"substitute"]
private let u64_to_h64 = Hacl.Cast.uint64_to_sint64


//
// SipHash24
//


#reset-options "--max_fuel 0  --z3rlimit 20"

val siphash24:
  key0    :uint64_t ->
  key1    :uint64_t ->
  data    :uint8_p  {length data < pow2 32} ->
  datalen :uint64_t {v datalen = length data} ->
  Stack uint64_t
        (requires (fun h -> live h data))
        (ensures  (fun h0 r h1 -> live h1 data /\ live h0 data
	                     /\ (as_seq h0 data == as_seq h1 data) // data is unmodified
                             /\ (r == Spec.siphash24 key0 key1 (as_seq h0 data)))) // result matches spec

#reset-options "--max_fuel 0  --z3rlimit 25"

let siphash24 key0 key1 data datalen =

  (**) let hinit = ST.get() in

  (* Push a new memory frame *)
  (**) push_frame ();
  (**) let h0 = ST.get() in

  (* Pop the memory frame *)
  (**) pop_frame ();

  (**) let hfin = ST.get() in
  (**) (FStar.UInt64.uint_to_t 0)

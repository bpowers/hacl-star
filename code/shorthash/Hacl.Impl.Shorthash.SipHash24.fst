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

type buffer   = Buffer.buffer uint64_t
type sipState = b:Buffer.buffer uint64_t{Buffer.length b = 4}


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


val get_unaligned:
  buf     :buffer ->
  len     :uint64_t{len = (FStar.UInt64.uint_to_t (Buffer.length buf))} ->
  datalen :uint64_t{(U64.v datalen) >= (U64.v len)} ->
  Stack (uint64_t)
    (requires (fun h -> True))
    (ensures (fun h0 r h1 -> True))
let get_unaligned buf len datalen = (FStar.UInt64.uint_to_t 0)


val siphash_init:
  v       :sipState ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 r h1 -> True))
let siphash_init v = ()


val siphash_inner:
  v  :sipState ->
  mi :uint64_t ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 r h1 -> True))
let siphash_inner v mi = ()


val siphash_round:
  v  :sipState ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 r h1 -> True))
let siphash_round v = ()


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

  // allocate v = buffer uint64, len 4
  // init v

  // calculate # of aligned rounds

  // for 0 aligned_round_count (fun h i -> True) aligned_body

  // final_off = (datalen / 8) * 8
  // final_mi = get_unaligned(msg[final_off:], data_len - final_off, datalen)
  // siphash_inner(&v, final_mi)

  // v[2] ^= 0xff

  // for 0 4 (fun h i -> True) siphash_round(&v)

  // result = v[0] ^ v[1] ^ v[2] ^ v[3]

  (* Pop the memory frame *)
  (**) pop_frame ();

  (**) let hfin = ST.get() in
  (**) (FStar.UInt64.uint_to_t 0)

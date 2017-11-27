module Hacl.Shorthash.SipHash24

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt32
open FStar.UInt64

module ST = FStar.HyperStack.ST
module Spec = Spec.Shorthash.SipHash24
module SipHash = Hacl.Impl.Shorthash.SipHash24


(* Definition of base types *)
private let uint8_ht   = Hacl.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t
private let uint8_p  = Buffer.buffer uint8_ht


//
// SipHash24
//

#reset-options "--max_fuel 0 --z3rlimit 25"

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

#reset-options "--max_fuel 0 --z3rlimit 10"

let siphash24 key0 key1 data datalen = SipHash.siphash24 key0 key1 data datalen

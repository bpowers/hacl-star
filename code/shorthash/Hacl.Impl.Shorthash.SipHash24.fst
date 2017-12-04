module Hacl.Impl.Shorthash.SipHash24

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
open FStar.Buffer

open C.Loops

open FStar.Endianness
open Hacl.Endianness
open Hacl.UInt64
open FStar.UInt64

(* Definition of aliases for modules *)
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H64 = FStar.UInt64

module Spec = Spec.Shorthash.SipHash24

(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint32_ht = Hacl.UInt32.t
private let uint64_ht = Hacl.UInt64.t

private let uint8_p  = Buffer.buffer uint8_ht
private let uint64_p  = Buffer.buffer uint64_ht

type sipState = b:uint64_p{Buffer.length b = 4}

let u32 = UInt32.uint_to_t
let u64 = UInt64.uint_to_t


//
// SipHash24
//


val siphash_init:
  v       :sipState ->
  key0    :uint64_t ->
  key1    :uint64_t ->
  Stack unit
    (requires (fun h -> live h v))
    (ensures (fun h0 r h1 -> live h1 v /\ modifies_1 v h0 h1))
let siphash_init v key0 key1 =
  v.(0ul) <- key0 ^^ 0x736f6d6570736575uL;
  v.(1ul) <- key1 ^^ 0x646f72616e646f6duL;
  v.(2ul) <- key0 ^^ 0x6c7967656e657261uL;
  v.(3ul) <- key1 ^^ 0x7465646279746573uL

// from chacha20 impl
inline_for_extraction
private let rotate_left (a:uint64_t) (s:uint32_t{0 < U32.v s && U32.v s < 64}) : Tot uint64_t =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(64ul -^ s)))

inline_for_extraction
let op_Less_Less_Less = rotate_left

#reset-options "--max_fuel 10  --z3rlimit 25"


val siphash_round:
  v  :sipState ->
  Stack unit
    (requires (fun h -> live h v))
    (ensures (fun h0 r h1 -> live h1 v /\ modifies_1 v h0 h1))
let siphash_round v =
  let siphash_round_a (v:sipState) :
    Stack unit
      (requires (fun h -> live h v))
      (ensures (fun h0 r h1 -> live h1 v /\ modifies_1 v h0 h1))
    = (
    v.(0ul) <- v.(0ul) +%^ v.(1ul);
    v.(2ul) <- v.(2ul) +%^ v.(3ul);
    v.(1ul) <- v.(1ul) <<< 13ul;
    v.(3ul) <- v.(3ul) <<< 16ul)
  in
  siphash_round_a v;
  let siphash_round_b (v:sipState) :
    Stack unit
      (requires (fun h -> live h v))
      (ensures (fun h0 r h1 -> live h1 v /\ modifies_1 v h0 h1))
    = (
    v.(1ul) <- v.(1ul) ^^ v.(0ul);
    v.(3ul) <- v.(3ul) ^^ v.(2ul);

    v.(0ul) <- v.(0ul) <<< 32ul;

    v.(2ul) <- v.(2ul) +%^ v.(1ul);
    v.(0ul) <- v.(0ul) +%^ v.(3ul))
  in
  siphash_round_b v;
  let siphash_round_c (v:sipState) :
    Stack unit
      (requires (fun h -> live h v))
      (ensures (fun h0 r h1 -> live h1 v /\ modifies_1 v h0 h1))
    = (
    v.(1ul) <- v.(1ul) <<< 17ul;
    v.(3ul) <- v.(3ul) <<< 21ul;

    v.(1ul) <- v.(1ul) ^^ v.(2ul);
    v.(3ul) <- v.(3ul) ^^ v.(0ul))
  in
  siphash_round_c v;

  v.(2ul) <- v.(2ul) <<< 32ul


inline_for_extraction
val siphash_inner:
  v  :sipState ->
  mi :uint64_t ->
  Stack unit
    (requires (fun h -> live h v))
    (ensures (fun h0 r h1 -> live h1 v /\ modifies_1 v h0 h1))
let siphash_inner v mi =
  v.(3ul) <- v.(3ul) ^^ mi;
  siphash_round v;
  v.(0ul) <- v.(0ul) ^^ mi

#reset-options "--max_fuel 0  --z3rlimit 20"

// datalen needs to be representable as a 32-bit unsigned int
val siphash24:
  key0    :uint64_t ->
  key1    :uint64_t ->
  data    :uint8_p ->
  datalen :uint32_t {U32.v datalen = length data} ->
  Stack uint64_t
        (requires (fun h -> live h data))
        (ensures  (fun h0 r h1 -> live h1 data /\ live h0 data
	                     /\ modifies_0 h0 h1 // data is unmodified
	))
                             // /\ (r == Spec.siphash24 key0 key1 (as_seq h0 data)))) // result matches spec

val get_unaligned:
  buf     :uint8_p ->
  len     :uint32_t{U32.v len = (Buffer.length buf) /\ U32.v len < 8} ->
  datalen :uint32_t{U32.v datalen >= U32.v len} ->
  Stack (uint64_t)
    (requires (fun h -> live h buf))
    (ensures (fun h0 r h1 -> live h1 buf /\ modifies_0 h0 h1))
let get_unaligned buf len datalen =
  (**) push_frame ();
  let mi: uint64_p = Buffer.create 0uL 1ul in
  (**) let h0 = ST.get() in
  let body (i:uint32_t {U32.v 0ul <= U32.v i /\ i `U32.lt` len}) :
    Stack unit
      (requires (fun h -> live h buf /\ live h mi))
      (ensures (fun h0 r h1 -> live h1 buf /\ live h1 mi /\ modifies_1 mi h0 h1))
    = (
    let n = buf.(i) in
    mi.(0ul) <- (FStar.Int.Cast.uint8_to_uint64 n) <<^ (i `U32.mul` 8ul))
  in
  for 0ul len (fun h i -> live h buf /\ live h mi /\ modifies_1 mi h0 h) body;
  let result: uint64_t = mi.(0ul) +%^ (FStar.Int.Cast.uint32_to_uint64 (datalen `U32.rem` 256ul) <<^ 56ul) in
  (**) pop_frame ();
  result


#reset-options "--max_fuel 0  --z3rlimit 25"

let siphash24 key0 key1 data datalen =

  (**) let hinit = ST.get() in

  (**) push_frame ();
  (**) let h0 = ST.get() in

  let v = Buffer.create 0uL 4ul in

  siphash_init v key0 key1;

  (**) let h1 = ST.get() in

  let aligned_rounds = datalen `U32.div` 8ul in

  let aligned_body (i:uint32_t {U32.v 0ul <= U32.v i /\ i `U32.lt` aligned_rounds}) :
    Stack unit
      (requires (fun h -> live h v /\ live h data))
      (ensures (fun h0 r h1 -> live h1 v /\ live h1 data /\ modifies_1 v h0 h1))
    = (
      let off = i `U32.mul_mod` 8ul in
      let mi = hload64_le (Buffer.sub data off 8ul) in
      siphash_inner v mi
    )
  in
  for 0ul aligned_rounds (fun h i -> live h v /\ live h data /\ modifies_1 v h1 h) aligned_body;

  (**) let h2 = ST.get() in

  let final_off = (datalen `U32.div` 8ul) `U32.mul_mod` 8ul in
  let slice_len = datalen `U32.sub` final_off in
  let final_mi = get_unaligned (Buffer.sub data final_off slice_len) slice_len datalen in

  siphash_inner v final_mi;

  v.(2ul) <- v.(2ul) ^^ 0xffuL;

  (**) let h3 = ST.get() in

  let finalized_body (i:uint32_t {U32.v 0ul <= U32.v i /\ i `U32.lt` 4ul}) :
    Stack unit
      (requires (fun h -> live h v))
      (ensures (fun h0 r h1 -> live h1 v /\ modifies_1 v h0 h1))
    =
      siphash_round v
  in
  for 0ul 4ul (fun h i -> live h v /\ modifies_1 v h3 h) finalized_body;

  let result = v.(0ul) ^^ v.(1ul) ^^ v.(2ul) ^^ v.(3ul) in

  (* Pop the memory frame *)
  (**) pop_frame ();

  (**) let hfin = ST.get() in
  result

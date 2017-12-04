module Hacl.Impl.Shorthash.SipHash24

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
open FStar.Buffer

open C.Loops

// open Hacl.Spec.Endianness
open FStar.Endianness
open Hacl.Endianness
// open Hacl.Cast
// open Hacl.UInt8
// open Hacl.UInt32
// open FStar.UInt32
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


val get_unaligned:
  buf     :uint64_p ->
  len     :uint64_t{v len = (Buffer.length buf)} ->
  datalen :uint64_t{v datalen >= v len} ->
  Stack (uint64_t)
    (requires (fun h -> live h buf))
    (ensures (fun h0 r h1 -> live h1 buf /\ modifies_0 h0 h1))
let get_unaligned buf len datalen = 0uL


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
[@ "c_inline"]
private let rotate_left (a:uint64_t) (s:uint32_t{0 < U32.v s && U32.v s < 64}) : Tot uint64_t =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(64ul -^ s)))

#reset-options "--max_fuel 10  --z3rlimit 25"

val siphash_round:
  v  :sipState ->
  Stack unit
    (requires (fun h -> live h v))
    (ensures (fun h0 r h1 -> live h1 v /\ modifies_1 v h0 h1))
let siphash_round v =
  (**) let h0 = ST.get() in
  let op_Less_Less_Less = rotate_left in
  let v0 = v.(0ul) in
  let v1 = v.(1ul) in
  let v2 = v.(2ul) in
  let v3 = v.(3ul) in
  v.(0ul) <- v0 +%^ v1;
  let v0 = v.(0ul) in
  v.(2ul) <- v2 +%^ v3;
  let v2 = v.(2ul) in
  v.(1ul) <- v1 <<< 13ul;
  let v1 = v.(1ul) in
  v.(3ul) <- v3 <<< 16ul;
  let v3 = v.(3ul) in

  (**) let h1 = ST.get() in
  (**) assert(modifies_1 v h0 h1);

  v.(1ul) <- v1 ^^ v0;
  let v1 = v.(1ul) in
  v.(3ul) <- v3 ^^ v2;
  let v3 = v.(3ul) in

  v.(0ul) <- v0 <<< 32ul;
  let v0 = v.(0ul) in

  (**) let h2 = ST.get() in
  (**) assert(modifies_1 v h1 h2);

  v.(2ul) <- v2 +%^ v1;
  let v2 = v.(2ul) in
  v.(0ul) <- v0 +%^ v3;
  let v0 = v.(0ul) in

  v.(1ul) <- v1 <<< 17ul;
  let v1 = v.(1ul) in
  v.(3ul) <- v3 <<< 21ul;
  let v3 = v.(3ul) in

  (**) let h3 = ST.get() in
  (**) assert(modifies_1 v h2 h3);

  v.(1ul) <- v1 ^^ v2;
  let v1 = v.(1ul) in
  v.(3ul) <- v3 ^^ v0;
  let v3 = v.(3ul) in

  v.(2ul) <- v2 <<< 32ul


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
  data    :uint8_p  {length data < pow2 32} ->
  datalen :uint32_t {U32.v datalen = length data} ->
  Stack uint64_t
        (requires (fun h -> live h data))
        (ensures  (fun h0 r h1 -> live h1 data /\ live h0 data
	                     /\ modifies_0 h0 h1 // data is unmodified
	))
                             // /\ (r == Spec.siphash24 key0 key1 (as_seq h0 data)))) // result matches spec

#reset-options "--max_fuel 0  --z3rlimit 25"

let siphash24 key0 key1 data datalen =

  (**) let hinit = ST.get() in

  (* Push a new memory frame *)
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
      let mi = hload64_le (Buffer.sub data i 8ul) in
      siphash_inner v mi
    )
  in
  for 0ul aligned_rounds (fun h i -> live h v /\ live h data /\ modifies_1 v h1 h) aligned_body;

  (**) let h2 = ST.get() in

  // final_off = (datalen / 8) * 8
  // final_mi = get_unaligned(msg[final_off:], data_len - final_off, datalen)
  // siphash_inner(&v, final_mi)

  // v[2] ^= 0xff

  // for 0 4 (fun h i -> True) siphash_round(&v)

  let result = v.(0ul) ^^ v.(1ul) ^^ v.(2ul) ^^ v.(3ul) in

  (* Pop the memory frame *)
  (**) pop_frame ();

  (**) let hfin = ST.get() in
  result

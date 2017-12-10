module Spec.Shorthash.SipHash24

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.UInt64

module List = FStar.List.Tot

open Spec.Loops
open Spec.Lib

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

let u8 = UInt8.uint_to_t
let u32 = UInt32.uint_to_t
let u64 = UInt64.uint_to_t

#set-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"

let rotate_left (a:UInt64.t) (s:UInt32.t {0 < U32.v s /\ U32.v s<64}) : Tot UInt64.t =
  ((a <<^ s) |^ (a >>^ (64ul `U32.sub` s)))

let op_Less_Less_Less (a:UInt64.t) (s:UInt32.t {0 < U32.v s /\ U32.v s<64}) = rotate_left a s


#set-options "--max_fuel 0 --z3rlimit 10"

(* State is 4 64-bit integers *)
let size_state = 4

(* Base types *)
type bytes = m:seq UInt8.t
type state = m:seq UInt64.t{Seq.length m = size_state}
type off   = o:nat{o < 4}


val to_state:
  v0: UInt64.t ->
  v1: UInt64.t ->
  v2: UInt64.t ->
  v3: UInt64.t ->
  Tot (s:state{length s = 4 /\ index s 0 == v0 /\ index s 1 == v1 /\ index s 2 == v2 /\ index s 3 == v3})
let to_state v0 v1 v2 v3 =
  let s = create 4 v0 in
  let s = s.[1] <- v1 in
  let s = s.[2] <- v2 in
  let s = s.[3] <- v3 in
  s


val siphash_init:
  key0 :UInt64.t ->
  key1 :UInt64.t ->
  Tot (s:state{length s = 4
             /\ index s 0 == key0 ^^ 0x736f6d6570736575uL
	     /\ index s 1 == key1 ^^ 0x646f72616e646f6duL
	     /\ index s 2 == key0 ^^ 0x6c7967656e657261uL
	     /\ index s 3 == key1 ^^ 0x7465646279746573uL})
let siphash_init key0 key1 =
  let v0 = key0 ^^ 0x736f6d6570736575uL in
  let v1 = key1 ^^ 0x646f72616e646f6duL in
  let v2 = key0 ^^ 0x6c7967656e657261uL in
  let v3 = key1 ^^ 0x7465646279746573uL in
  to_state v0 v1 v2 v3


#reset-options "--max_fuel 0 --z3rlimit 10"

val half_round:
  v :state ->
  a :off ->
  b :off ->
  c :off ->
  d :off ->
  s :U32.t{0 < U32.v s /\ U32.v s < 64} ->
  t :U32.t{0 < U32.v t /\ U32.v t < 64} ->
  Tot (state)
let half_round v a b c d s t =
  let v = v.[a] <- v.[a] +%^ v.[b] in
  let v = v.[c] <- v.[c] +%^ v.[d] in
  let v = v.[b] <- (v.[b] <<< s) ^^ v.[a] in
  let v = v.[d] <- (v.[d] <<< t) ^^ v.[c] in
  let v = v.[a] <- v.[a] <<< 32ul in
  v


#reset-options "--max_fuel 0 --z3rlimit 10"

val full_round:
  v :state ->
  Tot (state)
let full_round v =
  let v = half_round v 0 1 2 3 13ul 16ul in
  let v = half_round v 2 1 0 3 17ul 21ul in
  v

val double_round:
  v : state ->
  Tot (state)
let double_round v =
  full_round (full_round v)

#reset-options "--max_fuel 0 --z3rlimit 10"

val siphash_inner :
  v        :state ->
  mi       :UInt64.t -> // should be mod 8 == 0
  Tot (state)
let siphash_inner v mi =
  let v = v.[3] <- v.[3] ^^ mi in
  let v = double_round v in
  let v = v.[0] <- v.[0] ^^ mi in
  v


#reset-options "--max_fuel 0 --z3rlimit 10"

val siphash_aligned :
  v        :state ->
  data     :bytes -> // should be mod 8 == 0
  Tot (state) (decreases (Seq.length data))
let rec siphash_aligned v data =
  if Seq.length data < 8 then
    v
  else
    let mi = uint64_from_le (Seq.slice data 0 8) in
    let data = Seq.slice data 8 (Seq.length data)  in
    let v = siphash_inner v mi in

    siphash_aligned v data

#reset-options "--max_fuel 0 --z3rlimit 10"

val get_unaligned':
  data :bytes{Seq.length data < 8} ->
  len  :nat ->
  i    :nat ->
  mi   :UInt64.t ->
  Tot (UInt64.t) (decreases ((Seq.length data) - i))
let rec get_unaligned' data len i mi =
  if i >= (Seq.length data) then
    mi +%^ (((u64 (UInt.to_uint_t 64 len)) %^ 256uL) <<^ 56ul)
  else (
    assert(i < Seq.length data);
    let b = Seq.index data i in
    let bl = Seq.upd (Seq.create 8 (u8 0)) 0 b in
    let b64: UInt64.t = uint64_from_le bl in
    let mi = mi +%^ (b64 <<^ (u32 (UInt.to_uint_t 32 (i * 8)))) in
    get_unaligned' data len (i+1) mi)

val get_unaligned:
  data :bytes{Seq.length data < 8} ->
  len  :nat ->
  Tot (UInt64.t)
let get_unaligned data len = get_unaligned' data len 0 0uL


#reset-options "--max_fuel 0 --z3rlimit 10"

val siphash_unaligned :
  v        :state ->
  data     :bytes ->
  Tot (state)
let siphash_unaligned v data =
  let off = ((Seq.length data) / 8) * 8 in
  let remaining = Seq.slice data off (Seq.length data) in
  let mi = get_unaligned remaining (Seq.length remaining) in
  siphash_inner v mi


#reset-options "--max_fuel 0 --z3rlimit 10"

val siphash_finalize :
  v        :state ->
  Tot (state)
let siphash_finalize v =
  let v = v.[2] <- v.[2] ^^ 0xffuL in
  double_round (double_round v)


#reset-options "--max_fuel 0 --z3rlimit 10"

val siphash24:
  key0     :UInt64.t ->
  key1     :UInt64.t ->
  data     :bytes ->
  Tot (h:UInt64.t)
let siphash24 key0 key1 data =
  let state = siphash_init key0 key1 in
  let state = siphash_aligned state data in
  let state = siphash_unaligned state data in
  let state = siphash_finalize state in
  state.[0] ^^ state.[1] ^^ state.[2] ^^ state.[3]


//
// Test 1
//

let test_key0 = 0x0706050403020100uL
let test_key1 = 0x0F0E0D0C0B0A0908uL

let test_data0: bytes = Seq.seq_of_list []
let test_expected0 = 0x726FDB47DD0E0E31uL

let test_data3: bytes = Seq.seq_of_list [0uy; 1uy; 2uy]
let test_expected3 = 9612764727700323885uL


//
// Main
//

val test: unit -> Tot (bool)
let test () =
  (test_expected0 = (siphash24 test_key0 test_key1 test_data0)) &&
  (test_expected3 = (siphash24 test_key0 test_key1 test_data3))

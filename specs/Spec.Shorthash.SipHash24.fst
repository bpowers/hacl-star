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

let rotate_right (a:UInt64.t) (s:UInt32.t {0 < U32.v s /\ U32.v s<64}) : Tot UInt64.t =
  ((a >>^ s) |^ (a <<^ (64ul `U32.sub` s)))

let op_Less_Less_Less (a:UInt64.t) (s:UInt32.t {0 < U32.v s /\ U32.v s<64}) = rotate_left a s
let op_Greater_Greater_Greater (a:UInt64.t) (s:UInt32.t {0 < U32.v s /\ U32.v s<32}) = rotate_right a s


#set-options "--max_fuel 0 --z3rlimit 10"

(* State is 4 64-bit integers *)
let size_state = 4

(* Base types *)
type bytes = m:seq UInt8.t

type lstate = m:list UInt64.t{List.length m = size_state}
type state = m:seq UInt64.t{Seq.length m = size_state}


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

val sip_round:
  v :state ->
  Tot (new_state:state)
let sip_round v =
  let v0 = Seq.index v 0 in
  let v1 = Seq.index v 1 in
  let v2 = Seq.index v 2 in
  let v3 = Seq.index v 3 in

  let v0 = v0 +%^ v1 in
  let v2 = v2 +%^ v3 in

  let v1 = v1 <<< 13ul in
  let v3 = v3 <<< 16ul in

  let v1 = v1 ^^ v0 in
  let v3 = v3 ^^ v2 in

  let v0 = v0 <<< 32ul in

  let v2 = v2 +%^ v1 in
  let v0 = v0 +%^ v3 in

  let v1 = v1 <<< 17ul in
  let v3 = v3 <<< 21ul in

  let v1 = v1 ^^ v2 in
  let v3 = v3 ^^ v0 in

  let v2 = v2 <<< 32ul in

  to_state v0 v1 v2 v3


#reset-options "--max_fuel 10 --z3rlimit 10"

val siphash_rounds :
  v      :state ->
  rounds :nat ->
  Tot (state) (decreases rounds)
let rec siphash_rounds v rounds =
  match rounds with
  | 0 -> v
  | _ -> siphash_rounds (sip_round v) (rounds - 1)


#reset-options "--max_fuel 0 --z3rlimit 10"

val siphash_inner :
  v        :state ->
  mi       :UInt64.t -> // should be mod 8 == 0
  c_rounds :nat ->
  Tot (state)
let siphash_inner v mi c_rounds =
  let v0 = Seq.index v 0 in
  let v1 = Seq.index v 1 in
  let v2 = Seq.index v 2 in
  let v3 = Seq.index v 3 in

  let v3 = v3 ^^ mi in

  let v = to_state v0 v1 v2 v3 in
  let v = siphash_rounds v c_rounds in

  let v0 = Seq.index v 0 in
  let v1 = Seq.index v 1 in
  let v2 = Seq.index v 2 in
  let v3 = Seq.index v 3 in

  let v0 = v0 ^^ mi in

  to_state v0 v1 v2 v3


#reset-options "--max_fuel 0 --z3rlimit 10"

val siphash_aligned :
  v        :state ->
  data     :bytes -> // should be mod 8 == 0
  c_rounds :nat ->
  Tot (state) (decreases (Seq.length data))
let rec siphash_aligned v data c_rounds =
  if Seq.length data < 8 then
    v
  else
    let mi = uint64_from_le (Seq.slice data 0 8) in
    let data = Seq.slice data 8 (Seq.length data)  in
    let v = siphash_inner v mi c_rounds in

    siphash_aligned v data c_rounds

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
  data     :bytes -> // should be mod 8 == 0
  c_rounds :nat ->
  Tot (state)
let siphash_unaligned v data c_rounds =
  let off = ((Seq.length data) / 8) * 8 in
  assert(off <= Seq.length data);
  let remaining = Seq.slice data off (Seq.length data) in
  let mi = get_unaligned remaining (Seq.length remaining) in
  siphash_inner v mi c_rounds


#reset-options "--max_fuel 0 --z3rlimit 10"

val siphash_finalize :
  v        :state ->
  d_rounds :nat ->
  Tot (state)
let siphash_finalize v d_rounds =
  let v0 = Seq.index v 0 in
  let v1 = Seq.index v 1 in
  let v2 = Seq.index v 2 in
  let v3 = Seq.index v 3 in

  let v2 = v2 ^^ 0xffuL in
  let v = to_state v0 v1 v2 v3 in

  siphash_rounds v d_rounds


#reset-options "--max_fuel 0 --z3rlimit 10"

val siphash:
  key0     :UInt64.t ->
  key1     :UInt64.t ->
  data     :bytes ->
  c_rounds :nat ->
  d_rounds :nat ->
  Tot (h:UInt64.t)
let siphash key0 key1 data c_rounds d_rounds =
  let state = siphash_init key0 key1 in
  let state = siphash_aligned state data c_rounds in
  let state = siphash_unaligned state data c_rounds in
  let state = siphash_finalize state d_rounds in

  let v0 = Seq.index state 0 in
  let v1 = Seq.index state 1 in
  let v2 = Seq.index state 2 in
  let v3 = Seq.index state 3 in

  v0 ^^ v1 ^^ v2 ^^ v3

#reset-options "--max_fuel 0 --z3rlimit 25"

val siphash24:
  key0     :UInt64.t ->
  key1     :UInt64.t ->
  data     :bytes ->
  Tot (h:UInt64.t)
let siphash24 key0 key1 data =
  siphash key0 key1 data 2 4

//
// Test 1
//

let test_key0 = 0x0706050403020100uL
let test_key1 = 0x0F0E0D0C0B0A0908uL

let test_data0: bytes = Seq.seq_of_list []
let test_expected0 = 0x726FDB47DD0E0E31uL

//
// Main
//

val test: unit -> Tot (bool)
let test () =
  (test_expected0 = (siphash24 test_key0 test_key1 test_data0))
  // assert_norm(List.Tot.length test_key1 = 20);
  // assert_norm(List.Tot.length test_data1 = 8);
  // assert_norm(List.Tot.length test_expected1 = 32);
  // assert_norm(List.Tot.length test_key2 = 4);
  // assert_norm(List.Tot.length test_data2 = 28);
  // assert_norm(List.Tot.length test_expected2 = 32);
  // assert_norm(List.Tot.length test_key3 = 20);
  // assert_norm(List.Tot.length test_data3 = 50);
  // assert_norm(List.Tot.length test_expected3 = 32);
  // assert_norm(List.Tot.length test_key4 = 25);
  // assert_norm(List.Tot.length test_data4 = 50);
  // assert_norm(List.Tot.length test_expected4 = 32);
  // assert_norm(List.Tot.length test_key5 = 20);
  // assert_norm(List.Tot.length test_data5 = 20);
  // assert_norm(List.Tot.length test_expected5 = 16);
  // assert_norm(List.Tot.length test_key6 = 131);
  // assert_norm(List.Tot.length test_data6 = 54);
  // assert_norm(List.Tot.length test_expected6 = 32);
  // assert_norm(List.Tot.length test_key7 = 131);
  // assert_norm(List.Tot.length test_data7 = 152);
  // assert_norm(List.Tot.length test_expected7 = 32);
  // let test_key1 = createL test_key1 in
  // let test_data1 = createL test_data1 in
  // let test_expected1 = createL test_expected1 in
  // let test_key2 = createL test_key2 in
  // let test_data2 = createL test_data2 in
  // let test_expected2 = createL test_expected2 in
  // let test_key3 = createL test_key3 in
  // let test_data3 = createL test_data3 in
  // let test_expected3 = createL test_expected3 in
  // let test_key4 = createL test_key4 in
  // let test_data4 = createL test_data4 in
  // let test_expected4 = createL test_expected4 in
  // let test_key5 = createL test_key5 in
  // let test_data5 = createL test_data5 in
  // let test_expected5 = createL test_expected5 in
  // let test_key6 = createL test_key6 in
  // let test_data6 = createL test_data6 in
  // let test_expected6 = createL test_expected6 in
  // let test_key7 = createL test_key7 in
  // let test_data7 = createL test_data7 in
  // let test_expected7 = createL test_expected7 in

  // (hmac test_key1 test_data1 = test_expected1) &&
  // (hmac test_key2 test_data2 = test_expected2) &&
  // (hmac test_key3 test_data3 = test_expected3) &&
  // (hmac test_key4 test_data4 = test_expected4) &&
  // (let hmac_truncated5 = Seq.slice (hmac test_key5 test_data5) 0 16 in
  // (hmac_truncated5 = test_expected5)) &&
  // (hmac test_key6 test_data6 = test_expected6) &&
  // (hmac test_key7 test_data7 = test_expected7)


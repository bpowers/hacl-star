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
  data     :bytes ->
  Tot (state) (decreases (length data))
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
  len  :nat -> // length of original data passed to siphash24
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
  let mi = get_unaligned remaining (Seq.length data) in
  siphash_inner v mi


#reset-options "--max_fuel 0 --z3rlimit 10"

val siphash_finalize :
  v        :state ->
  Tot (UInt64.t)
let siphash_finalize v =
  let v = v.[2] <- v.[2] ^^ 0xffuL in
  let v = double_round (double_round v) in
  v.[0] ^^ v.[1] ^^ v.[2] ^^ v.[3]


#reset-options "--max_fuel 0 --z3rlimit 10"

val siphash24:
  key0     :UInt64.t ->
  key1     :UInt64.t ->
  data     :bytes ->
  Tot (UInt64.t)
let siphash24 key0 key1 data =
  let state = siphash_init key0 key1 in
  let state = siphash_aligned state data in
  let state = siphash_unaligned state data in
  siphash_finalize state


//
// Test 1
//

val test_input:
  i:UInt8.t -> 
  Tot (bytes) (decreases (U8.v i))
let rec test_input i =
  let open FStar.UInt8 in
  if i =^ 0uy then
    create 0 0uy
  else (
    let m = i -^ 1uy in
    append (test_input m) (create 1 m)
  )

let test_key0 = 0x0706050403020100uL
let test_key1 = 0x0F0E0D0C0B0A0908uL

let test_data0: bytes = seq_of_list []
let test_expected0 = 0x726FDB47DD0E0E31uL

let test_data1: bytes = seq_of_list [0uy]

let test_data3: bytes = seq_of_list [0uy; 1uy; 2uy]
let test_expected3 = 9612764727700323885uL

let expected_output : (l:seq UInt64.t) = seq_of_list [
  0x726FDB47DD0E0E31uL; 0x74F839C593DC67FDuL; 0x0D6C8009D9A94F5AuL;
  0x85676696D7FB7E2DuL; 0xCF2794E0277187B7uL; 0x18765564CD99A68DuL;
  0xCBC9466E58FEE3CEuL; 0xAB0200F58B01D137uL; 0x93F5F5799A932462uL;
  0x9E0082DF0BA9E4B0uL; 0x7A5DBBC594DDB9F3uL; 0xF4B32F46226BADA7uL;
  0x751E8FBC860EE5FBuL; 0x14EA5627C0843D90uL; 0xF723CA908E7AF2EEuL;
  0xA129CA6149BE45E5uL; 0x3F2ACC7F57C29BDBuL; 0x699AE9F52CBE4794uL;
  0x4BC1B3F0968DD39CuL; 0xBB6DC91DA77961BDuL; 0xBED65CF21AA2EE98uL;
  0xD0F2CBB02E3B67C7uL; 0x93536795E3A33E88uL; 0xA80C038CCD5CCEC8uL;
  0xB8AD50C6F649AF94uL; 0xBCE192DE8A85B8EAuL; 0x17D835B85BBB15F3uL;
  0x2F2E6163076BCFADuL; 0xDE4DAAACA71DC9A5uL; 0xA6A2506687956571uL;
  0xAD87A3535C49EF28uL; 0x32D892FAD841C342uL; 0x7127512F72F27CCEuL;
  0xA7F32346F95978E3uL; 0x12E0B01ABB051238uL; 0x15E034D40FA197AEuL;
  0x314DFFBE0815A3B4uL; 0x027990F029623981uL; 0xCADCD4E59EF40C4DuL;
  0x9ABFD8766A33735CuL; 0x0E3EA96B5304A7D0uL; 0xAD0C42D6FC585992uL;
  0x187306C89BC215A9uL; 0xD4A60ABCF3792B95uL; 0xF935451DE4F21DF2uL;
  0xA9538F0419755787uL; 0xDB9ACDDFF56CA510uL; 0xD06C98CD5C0975EBuL;
  0xE612A3CB9ECBA951uL; 0xC766E62CFCADAF96uL; 0xEE64435A9752FE72uL;
  0xA192D576B245165AuL; 0x0A8787BF8ECB74B2uL; 0x81B3E73D20B49B6FuL;
  0x7FA8220BA3B2ECEAuL; 0x245731C13CA42499uL; 0xB78DBFAF3A8D83BDuL;
  0xEA1AD565322A1A0BuL; 0x60E61C23A3795013uL; 0x6606D7E446282B93uL;
  0x6CA4ECB15C5F91E1uL; 0x9F626DA15C9625F3uL; 0xE51B38608EF25F57uL;
  0x958A324CEB064572uL
]


//
// Main
//

val test_all:
  i:UInt8.t{0 <= (U8.v i) /\ (U8.v i) <= 64} ->
  Tot (bool) (decreases (64 - (U8.v i)))
let rec test_all i =
  let open FStar.UInt8 in
  if i =^ 64uy then
    true
  else (
    let ii = U8.v i in
    assert(ii < 64);
    let j = i +^ 1uy in
    if ii >= length expected_output then
      false
    else (
      let expected = expected_output.[(U8.v i)] in
      let actual = siphash24 test_key0 test_key1 (test_input i) in
      (expected = actual) && test_all j
    )
  )

val test: unit -> Tot (bool)
let test () =
  (test_data0 = test_input 0uy) &&
  (test_data1 = test_input 1uy) &&
  (test_data3 = test_input 3uy) &&
  (test_expected0 = (siphash24 test_key0 test_key1 test_data0)) &&
  (test_expected3 = (siphash24 test_key0 test_key1 test_data3)) &&
  test_all 0uy

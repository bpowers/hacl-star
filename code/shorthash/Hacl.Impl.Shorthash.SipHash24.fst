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
module HS = FStar.HyperStack

module Spec = Spec.Shorthash.SipHash24

(* Definition of base types *)
private let uint8_ht  = Hacl.UInt8.t
private let uint32_ht = Hacl.UInt32.t
private let uint64_ht = Hacl.UInt64.t

private let uint8_p  = Buffer.buffer uint8_ht
private let uint64_p  = Buffer.buffer uint64_ht

type sip_state = b:uint64_p{Buffer.length b = 4}
type sip_off = b:uint32_ht{U32.v b < 4}


//
// SipHash24
//

#reset-options "--max_fuel 0  --z3rlimit 200"

inline_for_extraction
val hupd_4: buf:sip_state ->
  v0:uint64_ht ->
  v1:uint64_ht ->
  v2:uint64_ht ->
  v3:uint64_ht ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                                  /\ (let s = as_seq h1 buf in
                                     Seq.index s 0 == v0
                                   /\ Seq.index s 1 == v1
                                   /\ Seq.index s 2 == v2
                                   /\ Seq.index s 3 == v3)))
inline_for_extraction
let hupd_4 buf v0 v1 v2 v3 =
  buf.(0ul) <- v0;
  buf.(1ul) <- v1;
  buf.(2ul) <- v2;
  buf.(3ul) <- v3

val siphash_init:
  v       :sip_state ->
  key0    :uint64_ht ->
  key1    :uint64_ht ->
  Stack unit
    (requires (fun h -> live h v))
    (ensures (fun h0 r h1 -> live h1 v /\ modifies_1 v h0 h1
                        /\ (let spec_v = Spec.siphash_init key0 key1 in
                           let impl_v = as_seq h1 v in
                           impl_v == spec_v)))
let siphash_init v key0 key1 =
  hupd_4 v
    (key0 ^^ 0x736f6d6570736575uL)
    (key1 ^^ 0x646f72616e646f6duL)
    (key0 ^^ 0x6c7967656e657261uL)
    (key1 ^^ 0x7465646279746573uL);
  (**) let h1 = ST.get () in
  (**) let spec_v = Spec.siphash_init key0 key1 in
  (**) let impl_v = as_seq h1 v in
  (**) Seq.lemma_eq_intro impl_v spec_v


// val init_correct: Lemma (ensures (let seq_v = Hacl.Spec.Endianness.reveal_h64s (as_seq h1 v) in
//                  seq_v = (Spec.siphash_init key0 key1)))

// from chacha20 impl -- why does this have to be > 0?
inline_for_extraction
private let rotate_left (a:uint64_ht) (s:uint32_ht{0 < U32.v s /\ U32.v s < 64}) : Tot uint64_ht =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(64ul -^ s)))

inline_for_extraction
let op_Less_Less_Less = rotate_left

#reset-options "--max_fuel 0  --z3rlimit 200"


inline_for_extraction
val half_round:
  v :sip_state ->
  a :sip_off ->
  b :sip_off ->
  c :sip_off ->
  d :sip_off ->
  s :uint32_ht{0 < U32.v s /\ U32.v s < 64} ->
  t :uint32_ht{0 < U32.v t /\ U32.v t < 64} ->
  Stack unit
    (requires (fun h -> live h v))
    (ensures  (fun h0 _ h1 -> live h1 v /\ modifies_1 v h0 h1
                         /\ (let spec_v = Spec.half_round (as_seq h0 v)
			                   (U32.v a) (U32.v b) (U32.v c) (U32.v d) s t in
                            let impl_v = as_seq h1 v in
                            impl_v == spec_v)))
inline_for_extraction
let half_round v a b c d s t =
  v.(a) <- v.(a) +%^ v.(b);
  v.(c) <- v.(c) +%^ v.(d);
  v.(b) <- (v.(b) <<< s) ^^ v.(a);
  v.(d) <- (v.(d) <<< t) ^^ v.(c);
  v.(a) <- v.(a) <<< 32ul


#reset-options "--max_fuel 0  --z3rlimit 200"

inline_for_extraction
val full_round:
  v  :sip_state ->
  Stack unit
    (requires (fun h -> live h v))
    (ensures (fun h0 _ h1 -> live h1 v /\ modifies_1 v h0 h1 /\
                          (let spec_v = Spec.full_round (as_seq h0 v) in
                           let impl_v = as_seq h1 v in
                           impl_v = spec_v)))
inline_for_extraction
let full_round v =
  half_round v 0ul 1ul 2ul 3ul 13ul 16ul;
  half_round v 2ul 1ul 0ul 3ul 17ul 21ul

inline_for_extraction
val double_round:
  v :sip_state ->
  Stack unit
    (requires (fun h -> live h v))
    (ensures (fun h0 _ h1 -> live h1 v /\ modifies_1 v h0 h1 /\
                          (let spec_v = Spec.double_round (as_seq h0 v) in
                           let impl_v = as_seq h1 v in
                           impl_v = spec_v)))
inline_for_extraction
let double_round v =
  full_round v;
  full_round v

#reset-options "--max_fuel 0  --z3rlimit 200"

inline_for_extraction
val siphash_inner:
  v  :sip_state ->
  mi :uint64_ht ->
  Stack unit
    (requires (fun h -> live h v))
    (ensures (fun h0 r h1 -> live h1 v /\ modifies_1 v h0 h1 /\
                          (let spec_v = Spec.siphash_inner (as_seq h0 v) mi in
                           let impl_v = as_seq h1 v in
                           impl_v == spec_v)))
let siphash_inner v mi =
  v.(3ul) <- v.(3ul) ^^ mi;
  double_round v;
  v.(0ul) <- v.(0ul) ^^ mi


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

let lemma_modifies_0_is_modifies_1 (#a:Type) (h:HyperStack.mem) (b:buffer a{live h b}) : Lemma
  (modifies_1 b h h) =
  lemma_modifies_sub_1 h h b


#reset-options "--initial_fuel 0 --max_fuel 4  --z3rlimit 200"


inline_for_extraction
val siphash_aligned:
  v :sip_state ->
  data    :uint8_p ->
  datalen :uint32_ht {U32.v datalen = length data} ->
  Stack unit
    (requires (fun h -> live h v /\ live h data))
    (ensures  (fun h0 _ h1 -> live h1 v /\ live h1 data /\ modifies_1 v h0 h1
                         /\ True))
inline_for_extraction
let siphash_aligned v data datalen =
  (**) let h0 = ST.get() in

  let aligned_rounds = datalen `U32.div` 8ul in

  (**) let inv (h1:HS.mem) (i:nat) : Type0 =
         i <= (length data)/8 /\ (i `Prims.op_Multiply` 8 <= U32.v datalen)
       /\ live h1 v /\ live h1 data /\ modifies_1 v h0 h1
       /\ (let (ilen:nat{ilen <= U32.v datalen}) = i `Prims.op_Multiply` 8 in
          let arg_v = as_seq h0 v in
          let data_v = as_seq h0 data in
          let sliced_data = Seq.slice data_v 0 ilen in
          let spec_v = Spec.siphash_aligned arg_v sliced_data in
          let impl_v = as_seq h1 v in
	  Seq.lemma_len_slice data_v 0 ilen;
	  Seq.length sliced_data <= length data
        /\ impl_v == spec_v)
          // (i == 0 ==> Seq.length sliced_data == 0 /\ arg_v == spec_v)) // /\ (i <> 0 ==> True)) // impl_v == spec_v))
       in

  let aligned_body (i:uint32_ht {U32.v 0ul <= U32.v i /\ i `U32.lt` aligned_rounds}) :
    Stack unit
      (requires (fun h -> inv h (U32.v i)))
      (ensures  (fun h0 _ h1 -> inv h1 (U32.v i + 1)))
    = (
      let off = i `U32.mul` 8ul in
      let mi = hload64_le (Buffer.sub data off 8ul) in
      siphash_inner v mi
    )
  in
  (**) lemma_modifies_0_is_modifies_1 h0 v;
  for 0ul aligned_rounds inv aligned_body;
  (**) let h1 = ST.get() in ()


#reset-options "--max_fuel 0  --z3rlimit 20"

inline_for_extraction
val get_unaligned:
  buf     :uint8_p ->
  len     :uint32_ht{U32.v len = (Buffer.length buf) /\ U32.v len < 8} ->
  datalen :uint32_ht{U32.v datalen >= U32.v len} ->
  Stack (uint64_ht)
    (requires (fun h -> live h buf))
    (ensures (fun h0 r h1 -> live h1 buf /\ modifies_0 h0 h1)) // /\
                          // (let spec_r = Spec.get_unaligned (as_seq h0 buf) (U32.v datalen) in
			  //  r == spec_r)))
inline_for_extraction
let get_unaligned buf len datalen =
  (**) push_frame ();
  let mi: uint64_p = Buffer.create 0uL 1ul in
  (**) let h0 = ST.get() in
  let body (i:uint32_ht {U32.v 0ul <= U32.v i /\ i `U32.lt` len}) :
    Stack unit
      (requires (fun h -> live h buf /\ live h mi))
      (ensures (fun h0 r h1 -> live h1 buf /\ live h1 mi /\ modifies_1 mi h0 h1))
    = (
    let n = buf.(i) in
    mi.(0ul) <- (FStar.Int.Cast.uint8_to_uint64 n) <<^ (i `U32.mul` 8ul))
  in
  for 0ul len (fun h i -> live h buf /\ live h mi /\ modifies_1 mi h0 h) body;
  let result: uint64_ht = mi.(0ul) +%^ (FStar.Int.Cast.uint32_to_uint64 (datalen `U32.rem` 256ul) <<^ 56ul) in
  (**) pop_frame ();
  result


inline_for_extraction
val siphash_unaligned:
  v :sip_state ->
  data    :uint8_p ->
  datalen :uint32_ht {U32.v datalen = length data} ->
  Stack unit
    (requires (fun h -> live h v /\ live h data))
    (ensures (fun h0 _ h1 -> live h1 v /\ live h1 data /\ modifies_1 v h0 h1 /\
                          (let spec_v = Spec.siphash_unaligned (as_seq h0 v) (as_seq h0 data) in
                           let impl_v = as_seq h1 v in
                           impl_v = spec_v)))
inline_for_extraction
let siphash_unaligned v data datalen =
  let final_off = (datalen `U32.div` 8ul) `U32.mul_mod` 8ul in
  let slice_len = datalen `U32.sub` final_off in
  let final_mi = get_unaligned (Buffer.sub data final_off slice_len) slice_len datalen in

  siphash_inner v final_mi;

  v.(2ul) <- v.(2ul) ^^ 0xffuL



inline_for_extraction
val siphash_finalize:
  v :sip_state ->
  Stack unit
    (requires (fun h -> live h v))
    (ensures (fun h0 _ h1 -> live h1 v /\ modifies_1 v h0 h1 /\
                          (let spec_v = Spec.siphash_finalize (as_seq h0 v) in
                           let impl_v = as_seq h1 v in
                           impl_v = spec_v)))
inline_for_extraction
let siphash_finalize v =
  v.(2ul) <- v.(2ul) ^^ 0xffuL;
  double_round v;
  double_round v;
  v.(0ul) ^^ v.(1ul) ^^ v.(2ul) ^^ v.(3ul)


#reset-options "--max_fuel 0  --z3rlimit 25"

// datalen needs to be representable as a 32-bit unsigned int
val siphash24:
  key0    :uint64_ht ->
  key1    :uint64_ht ->
  data    :uint8_p ->
  datalen :uint32_ht {U32.v datalen = length data} ->
  Stack uint64_ht
        (requires (fun h -> live h data))
        (ensures  (fun h0 r h1 -> live h1 data /\ live h0 data
                             /\ modifies_0 h0 h1 // data is unmodified
                             /\ (r == Spec.siphash24 key0 key1 (as_seq h0 data)))) // result matches spec
let siphash24 key0 key1 data datalen =

  (**) push_frame ();
  (**) let h0 = ST.get() in

  let v = Buffer.create 0uL 4ul in

  siphash_init v key0 key1;
  siphash_aligned v data datalen;
  siphash_unaligned v data datalen;
  let result = siphash_finalize v in

  (**) pop_frame ();

  result

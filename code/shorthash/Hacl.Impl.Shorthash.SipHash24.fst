module Hacl.Impl.Shorthash.SipHash24

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
open FStar.Buffer

open C.Loops

open FStar.Seq

open FStar.Int.Cast
open FStar.Endianness
open Hacl.Endianness
open Hacl.UInt64
open FStar.UInt64

open Hacl.Hash.Lib.LoadStore

(* Definition of aliases for modules *)
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H64 = FStar.UInt64
module HS = FStar.HyperStack

module Spec = Spec.Shorthash.SipHash24

let op_Multiply = Prims.op_Multiply

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

// inline_for_extraction
val full_round:
  v  :sip_state ->
  Stack unit
    (requires (fun h -> live h v))
    (ensures (fun h0 _ h1 -> live h1 v /\ modifies_1 v h0 h1 /\
                          (let spec_v = Spec.full_round (as_seq h0 v) in
                           let impl_v = as_seq h1 v in
                           impl_v = spec_v)))
// inline_for_extraction
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


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let lemma_modifies_0_is_modifies_1 (#a:Type) (h:HyperStack.mem) (b:buffer a{live h b}) : Lemma
  (modifies_1 b h h) =
  lemma_modifies_sub_1 h h b

let lemma_transitive (#t: eqtype) (a:t) (b:t) (c:t) : Lemma
  (requires a = b /\ b = c)
  (ensures a = c)
  = ()

// let lemma_aligned_0 (v:Spec.state) (data:seq UInt64.t): 
//   Lemma
//     (requires True)
//     (ensures (Seq.length data == 0 ==> (Spec.siphash_aligned' v data == v)))
//     [SMTPat (Spec.siphash_aligned' v data)] =
//   assert_norm(Seq.length data == 0 ==> (Spec.siphash_aligned' v data == v))


#reset-options "--max_fuel 2  --z3rlimit 100"

let lemma_aligned_0 (v:Spec.state) (data:seq UInt64.t) :
  Lemma
    (requires Seq.length data == 0)
    (ensures (Spec.siphash_aligned' v data == v))
    [SMTPat (Spec.siphash_aligned' v data)] =
  assert_norm(Spec.siphash_aligned' v data == v)

val siphash_aligned':
  v :sip_state ->
  data    :uint64_p ->
  datalen :uint32_ht{U32.v datalen = Buffer.length data} ->
  Stack unit
    (requires (fun h       -> live h v /\ live h data /\ disjoint v data))
    (ensures  (fun h0 _ h1 -> live h1 v /\ live h1 data /\ modifies_1 v h0 h1
                         /\ (let arg_v = as_seq h0 v in
                            let data_v = as_seq h0 data in
                            let spec_v = Spec.siphash_aligned' arg_v data_v in
                            let impl_v = as_seq h1 v in
                            impl_v == spec_v)))
let rec siphash_aligned' v data datalen =
  (**) let h0 = ST.get() in

  if datalen = 0ul then (
    ();
    (**) assert(U32.v datalen == 0);
    (**) assert(Seq.length (as_seq h0 data) == 0);
    (**) lemma_aligned_0 (as_seq h0 v) (as_seq h0 data);
    (**) lemma_modifies_0_is_modifies_1 h0 v;
    (**) assert((as_seq h0 v) == Spec.siphash_aligned' (as_seq h0 v) (as_seq h0 data))
  ) else (
    (**) assert(U32.v datalen > 0);

    let mi = data.(0ul) in
    siphash_inner v mi;

    (**) let h1 = ST.get() in

    let datalen' = datalen `U32.sub` 1ul in
    let data' = Buffer.sub data 1ul datalen' in

    (**) let h2 = ST.get() in
    (**) assert(Buffer.modifies_1 v h0 h1);
    (**) Buffer.no_upd_lemma_1 h0 h1 v data;
    (**) Buffer.no_upd_lemma_0 h1 h2 data;
    (**) assert((as_seq h0 data) = (as_seq h2 data));
    (**) assert(as_seq h2 data' == Seq.slice (as_seq h2 data) 1 (U32.v datalen));
    (**) assert(Seq.length (as_seq h2 data') == U32.v datalen');

    siphash_aligned' v data' datalen';

    (**) let h3 = ST.get() in
    (**) Buffer.no_upd_lemma_1 h2 h3 v data;
    (**) assert((as_seq h2 data) = (as_seq h3 data));
    (**) let arg_v = as_seq h0 v in
    (**) let data_v = as_seq h0 data in
    (**) let impl_v = as_seq h3 v in
    (**) assert(mi == Seq.index data_v 0);
    (**) assert(as_seq h1 v == Spec.siphash_inner (as_seq h0 v) mi);
    (**) assert(as_seq h1 v == as_seq h2 v);
    (**) assert(as_seq h2 data' == Seq.slice data_v 1 (Seq.length data_v));
    (**) assert(as_seq h3 v == Spec.siphash_aligned' (as_seq h2 v) (Seq.slice data_v 1 (Seq.length data_v)))
  )


val siphash_aligned:
  v :sip_state ->
  data    :uint8_p ->
  datalen :uint32_ht{U32.v datalen = Buffer.length data} ->
  Stack unit
    (requires (fun h -> live h v /\ live h data))
    (ensures  (fun h0 _ h1 -> live h1 v /\ live h1 data /\ modifies_1 v h0 h1
                         /\ (let arg_v = as_seq h0 v in
                            let data_v = as_seq h0 data in
                            let spec_v = Spec.siphash_aligned arg_v data_v in
                            let impl_v = as_seq h1 v in
                            impl_v == spec_v)))
let siphash_aligned v data datalen =
  (**) let hinit = ST.get() in

  (**) push_frame();
  (**) let h0 = ST.get() in

  let len_w = datalen `U32.div` 8ul in
  let trunc_len = len_w `U32.mul` 8ul in
  let data_w = Buffer.create 0uL len_w in
  (**) let h1 = ST.get() in
  (**) no_upd_lemma_0 h0 h1 v;
  (**) no_upd_lemma_0 h0 h1 data;

  uint64s_from_le_bytes data_w (Buffer.sub data 0ul trunc_len) len_w;
  (**) let h2 = ST.get() in
  (**) assert(Buffer.modifies_1 data_w h1 h2);
  (**) Buffer.no_upd_lemma_1 h1 h2 data_w v;
  (**) assert((as_seq h0 v) = (as_seq h2 v));

  siphash_aligned' v data_w len_w;
  (**) let h3 = ST.get() in

  (**) pop_frame();
  (**) let hfin = ST.get() in

  (**) let spec_w = Spec.Lib.uint64s_from_le (U32.v len_w) (Seq.slice (as_seq h0 data) 0 (U32.v trunc_len)) in
  (**) assert(as_seq h2 data_w == spec_w);
  (**) assert(as_seq h3 v == Spec.siphash_aligned' (as_seq h0 v) spec_w);
  (**) assert(as_seq h3 v == Spec.siphash_aligned (as_seq h0 v) (as_seq h0 data));
  (**) modifies_popped_1 v hinit h0 h3 hfin


#reset-options "--max_fuel 0  --z3rlimit 50"

val lemma_accumulate_0:
  mi   :uint64_ht ->
  data :bytes{Seq.length data < 8} ->
  i    :uint32_ht{U32.v i < 8} ->
  n    :nat{n <= 7 /\ (U32.v i) + (Seq.length data) == n} ->
  Lemma
    (requires True)
    (ensures (Seq.length data == 0 ==> Spec.accumulate_unaligned mi data i n == mi))
    [SMTPat (Spec.accumulate_unaligned mi data i n)]
let lemma_accumulate_0 mi data i n =
  assert_norm(Seq.length data == 0 ==> Spec.accumulate_unaligned mi data i n == mi)

val lemma_accumulate_1:
  mi   :uint64_ht ->
  mi'  :uint64_ht ->
  data :bytes{Seq.length data < 8 /\ Seq.length data > 0} ->
  i    :uint32_ht{U32.v i < 8} ->
  n    :nat{n <= 7 /\ (U32.v i) + (Seq.length data) == n} ->
  Lemma
    (requires mi' == mi +%^ (uint8_to_uint64 (Seq.index data 0) <<^ (i `U32.mul` 8ul)))
    (ensures (Spec.accumulate_unaligned mi data i n == Spec.accumulate_unaligned mi' (Seq.slice data 1 (Seq.length data)) (i `U32.add` 1ul) n))
    (decreases (Seq.length data))
let rec lemma_accumulate_1 mi mi' data i n =
  match Seq.length data with
  | 1 -> assert_norm(Spec.accumulate_unaligned mi data i n == Spec.accumulate_unaligned mi' (Seq.slice data 1 (Seq.length data)) (i `U32.add` 1ul) n)
  | _ -> let j = i `U32.add` 1ul in
        let data' = (Seq.slice data 1 (Seq.length data)) in
        let mi'' = mi' +%^ (uint8_to_uint64 (Seq.index data' 0) <<^ (j `U32.mul` 8ul)) in // Spec.accumulate_unaligned mi' (Seq.slice data 1 (Seq.length data)) j n in
	assert(n == U32.v j + Seq.length data');
	if Seq.length data = 0 then
	  lemma_accumulate_0 mi' data' j n
        else
          lemma_accumulate_1 mi' mi'' data' j n;
	  admit() // assert(mi' = Spec.accumulate_unaligned mi'' data' j n)


let as_uint64 (h:HS.mem) (mi:uint64_p{Buffer.length mi == 1}) =
  Seq.index (as_seq h mi) 0


val accumulate_unaligned:
  mi      :uint64_ht ->
  buf     :uint8_p ->
  i       :uint32_ht{U32.v i < 8} ->
  len     :uint32_ht{U32.v len = (Buffer.length buf) /\ U32.v len < 8} ->
  Stack (uint64_ht)
    (requires (fun h -> live h buf /\ U32.v i + U32.v len < 8))
    (ensures (fun h0 r h1 -> live h1 buf /\ modifies_0 h0 h1
                        /\ U32.v i + U32.v len < 8
                        /\ (let (n:nat{n <= 7 /\ (U32.v i) + (Buffer.length buf) == n}) = (U32.v len + U32.v i) in
                           let spec_r = Spec.accumulate_unaligned mi (as_seq h0 buf) i n in
			   True))) // r == spec_r)))
let rec accumulate_unaligned mi buf i len =
  (**) let h0 = ST.get() in

  if len = 0ul then (
    (**) let n = U32.v len + U32.v i in
    (**) assert(U32.v len == 0);
    (**) assert(Seq.length (as_seq h0 buf) == 0);
    (**) lemma_accumulate_0 mi (as_seq h0 buf) 0ul (U32.v len);
    (**) lemma_modifies_0_is_modifies_1 h0 buf;
    (**) assert(mi == Spec.accumulate_unaligned mi (as_seq h0 buf) i n);
    mi
  ) else (
    (**) assert(U32.v len > 0);
    (**) assert(Seq.length (as_seq h0 buf) < 8);
    let num8 = buf.(0ul) in // needed to work around impure escape
    let num = uint8_to_uint64 num8 in
    let mi' = mi +%^ (num <<^ (i `U32.mul` 8ul)) in
    let len' = (len `U32.sub` 1ul) in
    let buf' = Buffer.sub buf 1ul len' in
    (**) assert(mi' == mi +%^ (uint8_to_uint64 (Seq.index (as_seq h0 buf) 0) <<^ (i `U32.mul` 8ul)));
    let mi'' = accumulate_unaligned mi' buf' (i `U32.add` 1ul) len' in
    (**) let h1 = ST.get() in
    (**) let n = U32.v len + U32.v i in
    (**) assert(modifies_0 h0 h1);
    // (**) assert(mi'' == Spec.accumulate_unaligned mi' (as_seq h0 buf') (i `U32.add` 1ul) n);
    mi''
  )


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
  let mi = accumulate_unaligned 0uL buf 0ul len in
  mi +%^ (((uint32_to_uint64 datalen) %^ 256uL) <<^ 56ul)

#reset-options "--max_fuel 0  --z3rlimit 50"

val siphash_unaligned:
  v :sip_state ->
  data    :uint8_p ->
  datalen :uint32_ht {U32.v datalen = Buffer.length data} ->
  Stack unit
    (requires (fun h -> live h v /\ live h data /\ disjoint v data))
    (ensures (fun h0 _ h1 -> live h1 v /\ live h1 data /\ modifies_1 v h0 h1 /\
                          (let spec_v = Spec.siphash_unaligned (as_seq h0 v) (as_seq h0 data) in
                           let impl_v = as_seq h1 v in
                           True))) // impl_v = spec_v)))
let siphash_unaligned v data datalen =
  (**) push_frame ();
  let final_off = (datalen `U32.div` 8ul) `U32.mul` 8ul in
  let slice_len = datalen `U32.sub` final_off in
  let remaining = Buffer.sub data final_off slice_len in
  let final_mi = get_unaligned remaining slice_len datalen in

  siphash_inner v final_mi;

  (**) pop_frame ()


val siphash_finalize:
  v :sip_state ->
  Stack uint64_ht
    (requires (fun h -> live h v))
    (ensures (fun h0 _ h1 -> live h1 v /\ modifies_1 v h0 h1 /\
                          (let spec_r = Spec.siphash_finalize (as_seq h0 v) in
                           True))) // impl_v == spec_v)))
let siphash_finalize v =
  (**) push_frame ();
  v.(2ul) <- v.(2ul) ^^ 0xffuL;
  double_round v;
  double_round v;
  let result = v.(0ul) ^^ v.(1ul) ^^ v.(2ul) ^^ v.(3ul) in
  (**) pop_frame ();
  result


#reset-options "--max_fuel 0  --z3rlimit 25"

// datalen needs to be representable as a 32-bit unsigned int
inline_for_extraction
val siphash24:
  key0    :uint64_ht ->
  key1    :uint64_ht ->
  data    :uint8_p ->
  datalen :uint32_ht{U32.v datalen = Buffer.length data} ->
  Stack uint64_ht
        (requires (fun h -> live h data))
        (ensures  (fun h0 r h1 -> live h1 data /\ live h0 data
                             /\ modifies_0 h0 h1 // data is unmodified
                             )) // /\ (r == Spec.siphash24 key0 key1 (as_seq h0 data)))) // result matches spec
inline_for_extraction
let siphash24 key0 key1 data datalen =
  (**) push_frame ();
  let v = Buffer.create 0uL 4ul in
  siphash_init v key0 key1;
  siphash_aligned v data datalen;
  siphash_unaligned v data datalen;
  let result = siphash_finalize v in
  (**) pop_frame ();
  result

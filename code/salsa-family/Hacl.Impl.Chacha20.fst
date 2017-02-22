module Hacl.Impl.Chacha20

open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open Hacl.Endianness
open Spec.Chacha20
open Combinators

module Spec = Spec.Chacha20

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type state = b:Buffer.buffer h32{length b = 16}

private inline_for_extraction let op_Less_Less_Less (a:h32) (s:u32{U32.v s <= 32}) : Tot h32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(32ul -^ s)))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

private val lemma_uint32s_from_le_bytes: h:mem -> output:buffer H32.t{live h output} ->
  h':mem -> input:uint8_p{live h' input} ->
  len:U32.t{length output = U32.v len /\ 4 * U32.v len = length input /\ U32.v len > 0} ->
  Lemma
    (requires (Seq.index (as_seq h output) 0 = Spec.Lib.uint32_from_le (as_seq h' (Buffer.sub input 0ul 4ul))
      /\ as_seq h (Buffer.offset output 1ul) == Spec.Lib.uint32s_from_le (UInt32.v len - 1) (as_seq h' (Buffer.offset input 4ul))))
    (ensures (as_seq h output == Spec.Lib.uint32s_from_le (U32.v len) (as_seq h' input)))
let lemma_uint32s_from_le_bytes h output h' input len =
  Spec.Lib.lemma_uint32s_from_le_def_1 (U32.v len) (as_seq h' input);
  Seq.lemma_eq_intro (as_seq h' (Buffer.sub input 0ul 4ul)) (Seq.slice (as_seq h' input) 0 4);
  Seq.lemma_eq_intro (as_seq h' (Buffer.offset input 4ul)) (Seq.slice (as_seq h' input) 4 (length input));
  Seq.lemma_eq_intro (as_seq h (Buffer.offset output 1ul)) (Seq.slice (as_seq h output) 1 (length output));
  cut (Seq.index (Spec.Lib.uint32s_from_le (U32.v len) (as_seq h' input)) 0 == Spec.Lib.uint32_from_le (Seq.slice (as_seq h' input) 0 4));
  Seq.lemma_eq_intro (as_seq h output) (Spec.Lib.uint32s_from_le (U32.v len) (as_seq h' input))


private val lemma_uint32s_from_le_bytes': h:mem -> h':mem -> output:buffer H32.t{live h output /\ live h' output /\ length output > 0} -> Lemma
  (requires (modifies_1 (Buffer.offset output 1ul) h h'))
  (ensures (Seq.index (as_seq h output) 0 == Seq.index (as_seq h' output) 0))
private let lemma_uint32s_from_le_bytes' h h' output =
  let output' = Buffer.sub output 0ul 1ul in
  let output'' = Buffer.offset output 1ul in
  no_upd_lemma_1 h h' output'' output';
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 1) (as_seq h output');
  Seq.lemma_eq_intro (Seq.append (as_seq h' output') (as_seq h' output'')) (as_seq h' output)


val uint32s_from_le_bytes:
  output:buffer H32.t ->
  input:uint8_p{disjoint output input} ->
  len:U32.t{length output = U32.v len /\ 4 * U32.v len = length input} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h0 input /\ modifies_1 output h0 h1 /\
      as_seq h1 output == Spec.Lib.uint32s_from_le (U32.v len) (as_seq h0 input)))
let rec uint32s_from_le_bytes output input len =
  let h0 = ST.get() in
  if U32.(len =^ 0ul) then (
    Spec.Lib.lemma_uint32s_from_le_def_0 0 (as_seq h0 input);
    Seq.lemma_eq_intro (as_seq h0 output) Seq.createEmpty
  )
  else (
    cut (U32.v len > 0);
    output.(0ul) <- hload32_le (Buffer.sub input 0ul 4ul);
    let h = ST.get() in
    let output' = Buffer.offset output 1ul in
    let input'  = Buffer.offset input 4ul in
    uint32s_from_le_bytes output' input' U32.(len -^ 1ul);
    let h1 = ST.get() in
    lemma_uint32s_from_le_bytes' h h1 output;
    lemma_uint32s_from_le_bytes h1 output h0 input len
  )


private val lemma_uint32s_to_le_bytes: h:mem -> output:uint8_p{live h output} ->
  h':mem -> input:buffer H32.t{live h' input} ->
  len:U32.t{length input = U32.v len /\ 4 * U32.v len = length output /\ U32.v len > 0} ->
  Lemma
    (requires (Seq.slice (as_seq h output) 0 4 = Spec.Lib.uint32_to_le (Seq.index (as_seq h' input) 0)
      /\ as_seq h (Buffer.offset output 4ul) == Spec.Lib.uint32s_to_le (UInt32.v len - 1) (as_seq h' (Buffer.offset input 1ul))))
    (ensures (as_seq h output == Spec.Lib.uint32s_to_le (U32.v len) (as_seq h' input)))
let lemma_uint32s_to_le_bytes h output h' input len =
  Spec.Lib.lemma_uint32s_to_le_def_1 (U32.v len) (as_seq h' input);
  Seq.lemma_eq_intro (as_seq h (Buffer.sub output 0ul 4ul)) (Seq.slice (as_seq h output) 0 4);
  Seq.lemma_eq_intro (as_seq h (Buffer.offset output 4ul)) (Seq.slice (as_seq h output) 4 (length output));
  Seq.lemma_eq_intro (as_seq h' (Buffer.offset input 1ul)) (Seq.slice (as_seq h' input) 1 (length input));
  Seq.lemma_eq_intro (Seq.slice (Spec.Lib.uint32s_to_le (U32.v len) (as_seq h' input)) 0 4)
                     (Spec.Lib.uint32_to_le (Seq.index (as_seq h' input) 0));
  Seq.lemma_eq_intro (as_seq h output) (Spec.Lib.uint32s_to_le (U32.v len) (as_seq h' input))


private val lemma_uint32s_to_le_bytes': h:mem -> h':mem -> output:uint8_p{live h output /\ live h' output /\ length output >= 4} -> Lemma
  (requires (modifies_1 (Buffer.offset output 4ul) h h'))
  (ensures (Seq.slice (as_seq h output) 0 4 == Seq.slice (as_seq h' output) 0 4))
private let lemma_uint32s_to_le_bytes' h h' output =
  let output' = Buffer.sub output 0ul 4ul in
  let output'' = Buffer.offset output 4ul in
  no_upd_lemma_1 h h' output'' output';
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 4) (as_seq h output')


val uint32s_to_le_bytes:
  output:uint8_p ->
  input:buffer H32.t{disjoint output input} ->
  len:U32.t{length input = U32.v len /\ 4 * U32.v len = length output} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h0 input /\ modifies_1 output h0 h1 /\
      as_seq h1 output == Spec.Lib.uint32s_to_le (U32.v len) (as_seq h0 input)))
let rec uint32s_to_le_bytes output input len =
  let h0 = ST.get() in
  if U32.(len =^ 0ul) then (
    Spec.Lib.lemma_uint32s_to_le_def_0 0 (as_seq h0 input);
    Seq.lemma_eq_intro (as_seq h0 output) Seq.createEmpty
  )
  else (
    cut (U32.v len > 0);
    let hd = input.(0ul) in
    hstore32_le (Buffer.sub output 0ul 4ul) hd;
    let h = ST.get() in
    FStar.Endianness.lemma_little_endian_inj (Seq.slice (as_seq h output) 0 4)
                                             (Spec.Lib.uint32_to_le hd);
    cut (Seq.slice (as_seq h output) 0 4 == Spec.Lib.uint32_to_le hd);
    let output' = Buffer.offset output 4ul in
    let input'  = Buffer.offset input 1ul in
    uint32s_to_le_bytes output' input' U32.(len -^ 1ul);
    let h1 = ST.get() in
    lemma_uint32s_to_le_bytes' h h1 output;
    lemma_uint32s_to_le_bytes h1 output h0 input len
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

val constant_setup_:
  c:Buffer.buffer H32.t{length c = 4} ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1
      /\ (let s = as_seq h1 c in
         v (Seq.index s 0) = 0x61707865 /\
         v (Seq.index s 1) = 0x3320646e /\
         v (Seq.index s 2) = 0x79622d32 /\
         v (Seq.index s 3) = 0x6b206574)))
let constant_setup_ st =
  st.(0ul)  <- (uint32_to_sint32 0x61707865ul);
  st.(1ul)  <- (uint32_to_sint32 0x3320646eul);
  st.(2ul)  <- (uint32_to_sint32 0x79622d32ul);
  st.(3ul)  <- (uint32_to_sint32 0x6b206574ul)


val constant_setup:
  c:Buffer.buffer H32.t{length c = 4} ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1
      /\ as_seq h1 c == Seq.createL constants))
let constant_setup st =
  constant_setup_ st;
  let h = ST.get() in
  assert_norm (Seq.length (Seq.createL constants) = 4);
  assert_norm(let s = (Seq.createL constants) in Seq.index s 0 = 0x61707865ul);
  assert_norm(let s = (Seq.createL constants) in Seq.index s 1 = 0x3320646eul);
  assert_norm(let s = (Seq.createL constants) in Seq.index s 2 = 0x79622d32ul);
  assert_norm(let s = (Seq.createL constants) in Seq.index s 3 = 0x6b206574ul);
  Seq.lemma_eq_intro (as_seq h st) (Seq.createL constants)


val keysetup:
  st:Buffer.buffer H32.t{length st = 8} ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  Stack unit
    (requires (fun h -> live h st /\ live h k))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h0 k /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = as_seq h1 st in
         let k = as_seq h0 k in
         s == Spec.Lib.uint32s_from_le 8 k)))
let keysetup st k =
  uint32s_from_le_bytes st k 8ul


val ivsetup:
  st:buffer H32.t{length st = 3} ->
  iv:uint8_p{length iv = 12 /\ disjoint st iv} ->
  Stack unit
    (requires (fun h -> live h st /\ live h iv))
    (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 iv
      /\ (let s = as_seq h1 st in
         let iv = as_seq h0 iv in
         s == Spec.Lib.uint32s_from_le 3 iv)
    ))
let ivsetup st iv =
  uint32s_from_le_bytes st iv 3ul

val ctrsetup:
  st:buffer H32.t{length st = 1} ->
  ctr:U32.t ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1
      /\ (let s = as_seq h1 st in
         s == Spec.Lib.singleton (uint32_to_sint32 ctr))
    ))
let ctrsetup st ctr =
  st.(0ul) <- uint32_to_sint32 ctr;
  let h = ST.get() in
  Seq.lemma_eq_intro (Spec.Lib.singleton (uint32_to_sint32 ctr)) (as_seq h st)


private val lemma_setup: h:mem -> st:state{live h st} -> Lemma
  (as_seq h st == FStar.Seq.(as_seq h (Buffer.sub st 0ul 4ul) @| as_seq h (Buffer.sub st 4ul 8ul)
                           @| as_seq h (Buffer.sub st 12ul 1ul) @| as_seq h (Buffer.sub st 13ul 3ul)))
private let lemma_setup h st =
  let s = as_seq h st in
  Seq.lemma_eq_intro (Seq.slice s 0 4) (as_seq h (Buffer.sub st 0ul 4ul));
  Seq.lemma_eq_intro (Seq.slice s 4 12) (as_seq h (Buffer.sub st 4ul 8ul));
  Seq.lemma_eq_intro (Seq.slice s 12 13) (as_seq h (Buffer.sub st 12ul 1ul));
  Seq.lemma_eq_intro (Seq.slice s 13 16) (as_seq h (Buffer.sub st 13ul 3ul));
  Seq.lemma_eq_intro s (FStar.Seq.(slice s 0 4 @| slice s 4 12 @| slice s 12 13 @| slice s 13 16))


val setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  c:U32.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = as_seq h1 st in
         let k = as_seq h0 k in
         let n = as_seq h0 n in
         s == setup k n (U32.v c))))
let setup st k n c =
  let h0 = ST.get() in
  let stcst = Buffer.sub st 0ul 4ul in
  let stk   = Buffer.sub st 4ul 8ul in
  let stc   = Buffer.sub st 12ul 1ul in
  let stn   = Buffer.sub st 13ul 3ul in
  constant_setup stcst;
  let h1 = ST.get() in
  keysetup stk k;
  let h2 = ST.get() in
  ctrsetup stc c;
  let h3 = ST.get() in
  ivsetup stn n;
  let h4 = ST.get() in
  no_upd_lemma_1 h0 h1 stcst stk;
  no_upd_lemma_1 h0 h1 stcst stn;
  no_upd_lemma_1 h0 h1 stcst stc;
  no_upd_lemma_1 h1 h2 stk stcst;
  no_upd_lemma_1 h1 h2 stk stn;
  no_upd_lemma_1 h1 h2 stk stc;
  no_upd_lemma_1 h2 h3 stc stcst;
  no_upd_lemma_1 h2 h3 stc stk;
  no_upd_lemma_1 h2 h3 stc stn;
  no_upd_lemma_1 h3 h4 stn stcst;
  no_upd_lemma_1 h3 h4 stn stk;
  no_upd_lemma_1 h3 h4 stn stc;
  lemma_setup h4 st


let idx = a:U32.t{U32.v a < 16}

val line:
  st:state ->
  a:idx -> b:idx -> d:idx -> s:U32.t{v s < 32} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 st
      /\ as_seq h1 st == line (U32.v a) (U32.v b) (U32.v d) s (as_seq h0 st)))
let line st a b d s =
  let sa = st.(a) in let sb = st.(b) in
  st.(a) <- sa +%^ sb;
  let sd = st.(d) in let sa = st.(a) in
  st.(d) <- (sd ^^ sa) <<< s


val quarter_round:
  st:state ->
  a:idx -> b:idx -> c:idx -> d:idx ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = as_seq h0 st in let s' = as_seq h1 st in
         s' == quarter_round (U32.v a) (U32.v b) (U32.v c) (U32.v d) s)))
let quarter_round st a b c d =
  line st a b d 16ul;
  line st c d b 12ul;
  line st a b d 8ul ;
  line st c d b 7ul


val column_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = as_seq h0 st in let s' = as_seq h1 st in
         s' == column_round s)))
let column_round st =
  quarter_round st 0ul 4ul 8ul  12ul;
  quarter_round st 1ul 5ul 9ul  13ul;
  quarter_round st 2ul 6ul 10ul 14ul;
  quarter_round st 3ul 7ul 11ul 15ul


val diagonal_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = as_seq h0 st in let s' = as_seq h1 st in
         s' == diagonal_round s)))
let diagonal_round st =
  quarter_round st 0ul 5ul 10ul 15ul;
  quarter_round st 1ul 6ul 11ul 12ul;
  quarter_round st 2ul 7ul 8ul  13ul;
  quarter_round st 3ul 4ul 9ul  14ul


val double_round:
  st:buffer H32.t{length st = 16} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = as_seq h0 st in let s' = as_seq h1 st in
         s' == double_round s)))
let double_round st =
    column_round st;
    diagonal_round st


unfold let double_round' (b:Seq.seq H32.t{Seq.length b = 16}) : Tot (b':Seq.seq H32.t{Seq.length b' = Seq.length b /\ b' == Spec.Chacha20.double_round b}) = Spec.Chacha20.double_round b


#reset-options "--initial_fuel 0 --max_fuel 1 --z3rlimit 100"

val rounds:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = as_seq h0 st in let s' = as_seq h1 st in
         s' == rounds s)))
let rounds st =
  Combinators.iter #H32.t #16 #double_round' 10ul double_round st 16ul


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val sum_states:
  st:state ->
  st':state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h1 st /\ live h0 st' /\ modifies_1 st h0 h1
      /\ (let s1 = as_seq h1 st in let s = as_seq h0 st in let s' = as_seq h0 st' in
         s1 == Combinators.seq_map2 (fun x y -> H32.(x +%^ y)) s s')))
let sum_states st st' =
  Combinators.inplace_map2 (fun x y -> H32.(x +%^ y)) st st' 16ul


val copy_state:
  st:state ->
  st':state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures (fun h0 _ h1 -> live h1 st /\ live h0 st' /\ modifies_1 st h0 h1
      /\ (let s = as_seq h0 st' in let s' = as_seq h1 st in s' == s)))
let copy_state st st' =
  Buffer.blit st' 0ul st 0ul 16ul;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h st) (Seq.slice (as_seq h st) 0 16);
  Seq.lemma_eq_intro (as_seq h st') (Seq.slice (as_seq h st') 0 16);
  Seq.lemma_eq_intro (as_seq h st) (as_seq h st')


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


type log_t_ = | MkLog: k:Spec.key -> n:Spec.nonce -> (* c:Spec.counter -> *) log_t_
type log_t = Ghost.erased log_t_


val lemma_setup_inj:
  k:Spec.key -> n:Spec.nonce -> c:Spec.counter ->
  k':Spec.key -> n':Spec.nonce -> c':Spec.counter -> Lemma
  (requires (Spec.setup k n c == Spec.setup k' n' c'))
  (ensures (k == k' /\ n == n' /\ c == c'))
let lemma_setup_inj k n c k' n' c' =
  let s = Spec.setup k n c in let s' = Spec.setup k' n' c' in
  Seq.lemma_eq_intro (Seq.slice s 4 12) (Seq.slice s' 4 12);
  Seq.lemma_eq_intro (Seq.slice s 12 13) (Seq.slice s' 12 13);
  Seq.lemma_eq_intro (Seq.slice s 13 16) (Seq.slice s' 13 16);
  Seq.lemma_eq_intro (Seq.slice s 4 12) (Spec.Lib.uint32s_from_le 8 k);
  Seq.lemma_eq_intro (Seq.slice s' 4 12) (Spec.Lib.uint32s_from_le 8 k');
  Seq.lemma_eq_intro (Seq.slice s 13 16) (Spec.Lib.uint32s_from_le 3 n);
  Seq.lemma_eq_intro (Seq.slice s' 13 16) (Spec.Lib.uint32s_from_le 3 n');
  Seq.lemma_eq_intro (Seq.slice s 12 13) (Spec.Lib.singleton (uint32_to_sint32 (U32.uint_to_t c)));
  Seq.lemma_eq_intro (Seq.slice s' 12 13) (Spec.Lib.singleton (uint32_to_sint32 (U32.uint_to_t c')));
  cut (c == U32.v (Seq.index (Seq.slice s 12 13) 0));
  cut (c' == U32.v (Seq.index (Seq.slice s' 12 13) 0));
  Spec.Lib.lemma_uint32s_from_le_inj 8 k k';
  Spec.Lib.lemma_uint32s_from_le_inj 3 n n'


(* Invariant on the state recording which block was computed last *)
let invariant (log:log_t) (h:mem) (st:state) : GTot Type0 =
  live h st /\ (let log = Ghost.reveal log in let s   = as_seq h st in
    match log with | MkLog key nonce -> s == Spec.setup key nonce (H32.v (Seq.index s 12)))


private val lemma_invariant:
  st:Spec.state ->
  k:Spec.key -> n:Spec.nonce -> c:H32.t -> c':H32.t -> Lemma
    (requires (st == Spec.setup k n (H32.v c)))
    (ensures (Seq.upd st 12 c' == Spec.setup k n (H32.v c')))
let lemma_invariant s k n c c' =
  let s' = Seq.upd s 12 c' in
  Seq.lemma_eq_intro (Seq.slice s 4 12) (Seq.slice s' 4 12);
  Seq.lemma_eq_intro (Seq.slice s 13 16) (Seq.slice s' 13 16);
  Seq.lemma_eq_intro (Seq.slice s 4 12) (Spec.Lib.uint32s_from_le 8 k);
  Seq.lemma_eq_intro (Seq.slice s' 4 12) (Spec.Lib.uint32s_from_le 8 k);
  Seq.lemma_eq_intro (Seq.slice s 13 16) (Spec.Lib.uint32s_from_le 3 n);
  Seq.lemma_eq_intro (Seq.slice s' 13 16) (Spec.Lib.uint32s_from_le 3 n);
  cut (c == (Seq.index (Seq.slice s 12 13) 0));
  cut (c' == (Seq.index (Seq.slice s' 12 13) 0));
  Spec.Lib.lemma_uint32s_from_le_inj 8 k k;
  Spec.Lib.lemma_uint32s_from_le_inj 3 n n;
  Seq.lemma_eq_intro s' (Spec.setup k n (H32.v c'))


private val lemma_state_counter:
  k:Spec.key -> n:Spec.nonce -> c:Spec.counter ->
  Lemma (v (Seq.index (Spec.setup k n (c)) 12) == c)
let lemma_state_counter k n c = ()


val chacha20_block:
  log:log_t ->
  stream_block:uint8_p{length stream_block = 64} ->
  st:state{disjoint st stream_block} ->
  ctr:UInt32.t ->
  Stack log_t
    (requires (fun h -> live h stream_block /\ invariant log h st))
    (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ invariant log h0 st
      /\ invariant updated_log h1 st /\ modifies_2 stream_block st h0 h1
      /\ (let block = as_seq h1 stream_block in
         match Ghost.reveal log, Ghost.reveal updated_log with
         | MkLog k n, MkLog k' n' ->
             block == chacha20_block k n (U32.v ctr) /\ k == k' /\ n == n')))
let chacha20_block log stream_block st ctr =
  let h0 = ST.get() in
  push_frame();
  let h_0 = ST.get() in
  let st' = Buffer.create (uint32_to_sint32 0ul) 16ul in
  let h_1 = ST.get() in
  st.(12ul) <- uint32_to_sint32 ctr;
  let h_2 = ST.get() in
  lemma_invariant (as_seq h0 st) (Ghost.reveal log).k (Ghost.reveal log).n (get h0 st 12) (ctr);
  copy_state st' st;
  rounds st';
  sum_states st' st;
  let h_3 = ST.get() in
  uint32s_to_le_bytes stream_block st' 16ul;
  let h_4 = ST.get() in
  let h = ST.get() in
  cut (as_seq h stream_block == chacha20_block (Ghost.reveal log).k (Ghost.reveal log).n (H32.v ctr));
  cut (modifies_3_2 stream_block st h_0 h);
  pop_frame();
  Ghost.elift1 (fun l -> match l with | MkLog k n -> MkLog k n) log


val alloc:
  unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> ~(live h0 st) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip))
let alloc () =
  create (uint32_to_sint32 0ul) 16ul


val init:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  Stack log_t
    (requires (fun h -> live h k /\ live h n /\ live h st))
    (ensures  (fun h0 log h1 -> live h1 st /\ live h0 k /\ live h0 n /\ modifies_1 st h0 h1
      /\ invariant log h1 st))
let init st k n =
  setup st k n 0ul;
  let h = ST.get() in
  Ghost.elift2 (fun k n -> MkLog k n) (Ghost.hide (as_seq h k)) (Ghost.hide (as_seq h n))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_1:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len <= 64 /\ U32.v len > 0} ->
  h:mem -> st:state{live h st} ->
  k:Spec.key -> n:Spec.nonce -> ctr:U32.t{U32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (U32.v ctr) (as_seq hi input)
     == Combinators.seq_map2 (fun x y -> FStar.UInt8.(x ^^ y))
                             (as_seq hi input)
                             (Seq.slice (Spec.chacha20_block k n (U32.v ctr)) 0 (U32.v len)))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_1 ho output hi input len h st k n ctr = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_2:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len > 64} ->
  h:mem -> st:state{live h st} ->
  k:Spec.key -> n:Spec.nonce -> ctr:U32.t{U32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (U32.v ctr) (as_seq hi input)
     == (let b, plain = Seq.split (as_seq hi input) 64 in
         let mask = Spec.chacha20_block k n (U32.v ctr) in
         let eb = Combinators.seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) b mask in
         let cipher = Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (U32.v ctr + 1) plain in
         Seq.append eb cipher))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_2 ho output hi input len h st k n ctr = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_0:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len = 0} ->
  h:mem -> st:state{live h st} ->
  k:Spec.key -> n:Spec.nonce -> ctr:U32.t{U32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (U32.v ctr) (as_seq hi input)
     == as_seq ho output)
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_0 ho output hi input len h st k n ctr =
  Seq.lemma_eq_intro (as_seq ho output) Seq.createEmpty


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val update_last:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len <= 64 /\ U32.v len > 0} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = as_seq h1 output in
         let plain = as_seq h0 plain in
         match Ghost.reveal log with | MkLog k n ->
         o == Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (U32.v ctr) plain)))
let update_last output plain len log st ctr =
  let h0 = ST.get() in
  push_frame();
  let block = create (uint8_to_sint8 0uy) 64ul in
  let l = chacha20_block log block st ctr in
  let mask = Buffer.sub block 0ul len in
  Combinators.map2 (fun x y -> H8.(x ^^ y)) output plain mask len;
  let h1 = ST.get() in
  lemma_chacha20_counter_mode_1 h1 output h0 plain len h0 st
    (Ghost.reveal log).k (Ghost.reveal log).n ctr;
  pop_frame();
  l


val update:
  output:uint8_p{length output = 64} ->
  plain:uint8_p{disjoint output plain /\ length plain = 64} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:U32.t{U32.v ctr + 1 < pow2 32} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = as_seq h1 output in
         let plain = as_seq h0 plain in
         match Ghost.reveal log with | MkLog k n ->
         o == Combinators.seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) plain (chacha20_cipher k n (U32.v ctr)))))
let update output plain log st ctr =
  let h0 = ST.get() in
  push_frame();
  let block = create (uint8_to_sint8 0uy) 64ul in
  let l = chacha20_block log block st ctr in
  Combinators.map2 (fun x y -> H8.(x ^^ y)) output plain block 64ul;
  pop_frame();
  l


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 300"

#set-options "--lax"

val chacha20_counter_mode:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = as_seq h1 output in
         let plain = as_seq h0 plain in
         match Ghost.reveal log with | MkLog k n ->
         o == Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (U32.v ctr) plain)))
let rec chacha20_counter_mode output plain len log st ctr =
  let h0 = ST.get() in
  if U32.(len =^ 0ul) then ()
  else if U32.(len <=^ 64ul) then (
    let _ = update_last output plain len log st ctr in ()
  ) else (
    let b  = Buffer.sub plain 0ul 64ul in
    let b' = Buffer.sub plain 64ul U32.(len -^ 64ul) in
    let o  = Buffer.sub output 0ul 64ul in
    let o' = Buffer.sub output 64ul U32.(len -^ 64ul) in
    let log' = update o b log st ctr in
    let l = chacha20_counter_mode o' b' U32.(len -^ 64ul) log' st U32.(ctr +^ 1ul) in
    let h = ST.get() in
    lemma_chacha20_counter_mode_2 h output h0 plain len h0 st (Ghost.reveal log).k (Ghost.reveal log).n ctr
  )
module Hacl.Test.Shorthash.SipHash24

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Buffer

module SipHash = Hacl.Shorthash.SipHash24


val test_1: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_1 () =

  (* Push a new memory frame *)
  (**) push_frame();

  let test_key0 = 0x0706050403020100uL in
  let test_key1 = 0x0F0E0D0C0B0A0908uL in

  let test_data0 = Buffer.create 0uy 0ul in
  let expected: Buffer.buffer FStar.UInt64.t = Buffer.createL [0x726FDB47DD0E0E31uL] in

  let result = SipHash.siphash24 test_key0 test_key1  test_data0 0ul in
  let actual: Buffer.buffer FStar.UInt64.t = Buffer.createL [result] in

  // (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 0") expected actual 8ul;

  (* Pop the memory frame *)
  (**) pop_frame()


val main: unit -> ST FStar.Int32.t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =

  (* Run test vectors *)
  test_1 ();
  // test_2 ();
  // test_3 ();
  // test_4 ();
  // test_5 ();
  // test_6 ();
  // test_7 ();

  (* Exit the program *)
  C.exit_success

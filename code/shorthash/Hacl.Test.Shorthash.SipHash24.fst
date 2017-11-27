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

  // let output_len = size_hash in
  // let output = FStar.Buffer.create 0uy output_len in

  // let key_len = 3ul in
  // let key = FStar.Buffer.createL [
  //     0x61uy; 0x62uy; 0x63uy;
  //   ] in

  // let key_len = 20ul in
  // let key = FStar.Buffer.create 0x0buy key_len in

  // let data_len = 8ul in
  // let data = FStar.Buffer.createL [
  //     0x48uy; 0x69uy; 0x20uy; 0x54uy; 0x68uy; 0x65uy; 0x72uy; 0x65uy
  //   ] in

  // let expected = FStar.Buffer.createL [
  //     0xb0uy; 0x34uy; 0x4cuy; 0x61uy; 0xd8uy; 0xdbuy; 0x38uy; 0x53uy;
  //     0x5cuy; 0xa8uy; 0xafuy; 0xceuy; 0xafuy; 0x0buy; 0xf1uy; 0x2buy;
  //     0x88uy; 0x1duy; 0xc2uy; 0x00uy; 0xc9uy; 0x83uy; 0x3duy; 0xa7uy;
  //     0x26uy; 0xe9uy; 0x37uy; 0x6cuy; 0x2euy; 0x32uy; 0xcfuy; 0xf7uy
  //   ] in

  // (* Call the hash function *)
  // // HMAC.hmac output key key_len data data_len;

  // (* Display the result *)
  // TestLib.compare_and_print (C.string_of_literal "Test 1") expected output Hash.size_hash;

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

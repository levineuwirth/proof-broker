(** Round-trip the three reference IR fixtures from [examples/] through
    the OCaml IR types and back to JSON; assert the result is structurally
    equal (object-key-order-insensitive) to the input.

    This is the foundational half of the Phase-0 FFI spike per delta.md
    §2.1: the C-FFI shim and Lean side follow in a subsequent session. *)

let examples_dir =
  (* dune runtest invokes us from sdk/_build/default/test/, so resolve
     relative to that. The dune file declares the examples as deps. *)
  Filename.concat (Sys.getcwd ()) "../../../../examples"

let load_json path = Yojson.Safe.from_file path

let json_testable =
  let pp fmt j = Format.fprintf fmt "%s" (Yojson.Safe.pretty_to_string j) in
  Alcotest.testable pp Proof_broker.Codec.json_equal

let round_trip name () =
  let path = Filename.concat examples_dir (name ^ ".json") in
  let original = load_json path in
  let ir = Proof_broker.Codec.of_json original in
  let again = Proof_broker.Codec.to_json ir in
  Alcotest.(check json_testable)
    (Printf.sprintf "%s.json round-trips through OCaml IR" name)
    original
    again

let parse_only name () =
  (* Sanity: of_json accepts the file without raising. Catches structural
     decode errors that round-trip might hide if to_json also produces
     them by accident. *)
  let path = Filename.concat examples_dir (name ^ ".json") in
  let _ir = Proof_broker.Codec.of_json (load_json path) in
  ()

let () =
  let fixtures = [
    "example1-lia-typeclass";
    "example2-function-composition";
    "example3-quotient-zmod";
  ] in
  let parse_cases =
    List.map (fun n -> Alcotest.test_case ("parse " ^ n) `Quick (parse_only n)) fixtures
  in
  let round_trip_cases =
    List.map (fun n -> Alcotest.test_case ("round-trip " ^ n) `Quick (round_trip n)) fixtures
  in
  Alcotest.run "proof_broker IR codec" [
    "parse", parse_cases;
    "round_trip", round_trip_cases;
  ]

(** OCaml side of the canonical-hash byte-equivalence harness.

    For every fixture in [tests/cross_canonical/], compute
    [Hash.canonical_sha256] and assert it equals the value pinned in
    [tests/cross_canonical/expected.json]. The Python side
    ([tools/test_canonical_hash.py]) does the same against the same
    sidecar. Both agreeing = OCaml's [Yojson.Safe.to_string +
    Codec.normalize] and Python's [json.dumps + _canonicalize] are
    producing byte-identical output, which is the locked invariant
    every cross-document hash check downstream depends on.

    Test failure here means OCaml drifted from the sidecar.
    [tools/test_canonical_hash.py] failing means Python did. If both
    drift but agree with each other against the sidecar, the harness
    surfaces it as TWO failing tests against expected.json — never
    a silent same-pass on a divergent format. *)

open Proof_broker

(* The dune build tree puts test_canonical_hash.exe at
   [_build/default/sdk/test/test_canonical_hash.exe], from which the
   repo root is four levels up. Mirrors test_round_trip.ml's path. *)
let cross_dir =
  Filename.concat (Sys.getcwd ()) "../../../../tests/cross_canonical"

let read_file path =
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let expected_table () : (string * string) list =
  let path = Filename.concat cross_dir "expected.json" in
  match Yojson.Safe.from_file path with
  | `Assoc pairs ->
    List.filter_map (fun (k, v) ->
      if String.length k > 0 && k.[0] = '_' then None
      else match v with `String s -> Some (k, s) | _ -> None
    ) pairs
  | _ -> failwith "expected.json is not a top-level object"

let test_fixture (fixture, expected_sha) () =
  let path = Filename.concat cross_dir fixture in
  let j = Yojson.Safe.from_file path in
  let actual = Hash.canonical_sha256 j in
  Alcotest.(check string)
    (Printf.sprintf "canonical_sha256 for %s" fixture)
    expected_sha actual

let () =
  let cases =
    List.map (fun (fixture, sha) ->
      Alcotest.test_case fixture `Quick (test_fixture (fixture, sha)))
      (expected_table ())
  in
  Alcotest.run "canonical_hash" [
    "byte-equivalence vs tests/cross_canonical/expected.json", cases;
  ]

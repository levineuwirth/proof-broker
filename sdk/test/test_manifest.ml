(** Unit tests for [Manifest], [Capability_match], and [Registry].

    Coverage:
    * Manifest codec round-trips the cvc5 fixture without loss.
    * Capability matching: the four reason cases each fire on a
      minimally-distinguishing IR.
    * The cvc5 manifest matches example1 (LIA goal) and rejects
      example3 (quotient construction).
    * Registry directory load picks up `manifest-*.json`, skips
      everything else, and reports duplicates as errors. *)

open Proof_broker

(* --- Fixture helpers -------------------------------------------------- *)

let fixture_dir () =
  Filename.concat (Sys.getcwd ()) "../../../../examples"

let load_json path =
  In_channel.with_open_text path In_channel.input_all
  |> Yojson.Safe.from_string

let cvc5_manifest () : Manifest.t =
  Manifest.of_json (load_json (Filename.concat (fixture_dir ()) "manifest-cvc5.json"))

let load_ir name : Ir.t =
  Codec.of_json (load_json (Filename.concat (fixture_dir ()) name))

(* --- Manifest codec --------------------------------------------------- *)

let test_codec_round_trip_cvc5 () =
  let original = load_json
    (Filename.concat (fixture_dir ()) "manifest-cvc5.json") in
  let m = Manifest.of_json original in
  let re = Manifest.to_json m in
  Alcotest.(check string) "round-trip stable after normalize"
    (Yojson.Safe.to_string (Codec.normalize original))
    (Yojson.Safe.to_string (Codec.normalize re));
  Alcotest.(check string) "adapter is cvc5" "cvc5" m.adapter;
  Alcotest.(check (list string)) "logic_fragments preserved"
    [ "LIA"; "LRA"; "BV"; "UF"; "UFLIA"; "UFLRA"; "ARRAY" ]
    m.logic_fragments;
  Alcotest.(check (list int)) "tiers_produced preserved"
    [ 0; 1; 3 ] m.tiers_produced

let test_decode_rejects_missing_required () =
  let bad = `Assoc [ "manifest_version", `String "1.0" ] in
  Alcotest.(check bool) "missing required field raises"
    true
    (try ignore (Manifest.of_json bad); false
     with Codec.Decode_error _ -> true)

(* --- IR builders for the matching tests ------------------------------ *)

let trivial_logic ?(order = "first_order") ?(fragment = "LIA") () : Ir.logic_classification = {
  order;
  features_used = [];
  first_order_fragment = fragment;
  decidable_theory = None;
}

let make_ir
      ?(order = "first_order")
      ?(fragment = "LIA")
      ?(type_meta : (string * Yojson.Safe.t) list = [])
      ?(type_vars : string list = [])
      () : Ir.t =
  {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = trivial_logic ~order ~fragment ();
    goal = { shell = Var { name = "p" }; payloads = None };
    context = {
      type_vars; free_vars = []; hypotheses = []; library_slice = None;
    };
    type_metadata = type_meta;
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

(* --- Capability_match tests ------------------------------------------ *)

let test_match_on_lia_ir () =
  (* CVC5 supports LIA, primitive constructions, first-order. A
     bare LIA goal with no type metadata should match. *)
  let ir = make_ir ~fragment:"LIA" () in
  match Capability_match.check ir (cvc5_manifest ()) with
  | Match -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Match, got %s"
                     (Capability_match.reason_kind other))

let test_order_too_high () =
  let ir = make_ir ~order:"higher_order" ~fragment:"LIA" () in
  match Capability_match.check ir (cvc5_manifest ()) with
  | Order_too_high _ -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Order_too_high, got %s"
                     (Capability_match.reason_kind other))

let test_logic_out_of_fragment () =
  (* "EUF" is not in the cvc5 manifest's logic_fragments. *)
  let ir = make_ir ~fragment:"EUF" () in
  match Capability_match.check ir (cvc5_manifest ()) with
  | Logic_out_of_fragment _ -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Logic_out_of_fragment, got %s"
                     (Capability_match.reason_kind other))

let test_fragment_none_skips_check () =
  (* When the source declined to classify (fragment="none"), the
     fragment check should not fire. The construction check should
     decide. With no type metadata and no type vars, only "primitive"
     is needed; cvc5 supports that, so the result is Match. *)
  let ir = make_ir ~fragment:"none" () in
  match Capability_match.check ir (cvc5_manifest ()) with
  | Match -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Match, got %s"
                     (Capability_match.reason_kind other))

let test_type_construction_not_supported () =
  (* CVC5 does not support quotient construction. *)
  let qmeta : string * Yojson.Safe.t = "Q", `Assoc [
    "kind", `String "type_constructor_application";
    "constructor", `Assoc [
      "name", `String "Q";
      "construction_kind", `String "quotient";
      "underlying_type", `String "U";
      "equivalence_relation", `Assoc [
        "shell", Codec.shell_to_json
          (Lambda { binders = [ { var = "a"; ty = "U" }; { var = "b"; ty = "U" } ];
                    body = App { symbol = "R"; type_args = [];
                                 args = [ Var { name = "a" }; Var { name = "b" } ] } });
        "equivalence_proof", `String "R.equiv";
      ];
      "elimination_principle", `String "Q.ind";
      "equality_principle", `String "Q.sound";
    ];
    "arguments", `List [];
  ] in
  let ir = make_ir ~type_meta:[ qmeta ] () in
  match Capability_match.check ir (cvc5_manifest ()) with
  | Type_construction_not_supported { detail } ->
    (* Detail should mention "quotient" since that's the offender. *)
    let r = Str.regexp_string "quotient" in
    Alcotest.(check bool) "detail mentions quotient"
      true (try ignore (Str.search_forward r detail 0); true
            with Not_found -> false)
  | other ->
    Alcotest.fail (Printf.sprintf
      "expected Type_construction_not_supported, got %s"
      (Capability_match.reason_kind other))

let test_type_var_requires_specialization_kind () =
  (* CVC5 declares "type_variable_via_specialization" so an IR with
     type_vars should match. *)
  let ir = make_ir ~type_vars:[ "α" ] () in
  match Capability_match.check ir (cvc5_manifest ()) with
  | Match -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Match, got %s"
                     (Capability_match.reason_kind other))

let test_type_var_rejected_when_kind_absent () =
  (* Strip "type_variable_via_specialization" from a copy of the
     cvc5 manifest; now an IR with type_vars should reject. *)
  let m = cvc5_manifest () in
  let m' : Manifest.t = { m with
    type_constructions =
      List.filter (fun s -> s <> "type_variable_via_specialization")
        m.type_constructions
  } in
  let ir = make_ir ~type_vars:[ "α" ] () in
  match Capability_match.check ir m' with
  | Type_construction_not_supported _ -> ()
  | other ->
    Alcotest.fail (Printf.sprintf
      "expected Type_construction_not_supported, got %s"
      (Capability_match.reason_kind other))

(* --- example1 / example3 fixtures ------------------------------------ *)

let test_select_partitions_example1_and_example3 () =
  let m = cvc5_manifest () in
  let ir1 = load_ir "example1-lia-typeclass.json" in
  let ir3 = load_ir "example3-quotient-zmod.json" in
  let matches1, rej1 = Capability_match.select [ m ] ir1 in
  Alcotest.(check int) "example1 matches cvc5" 1 (List.length matches1);
  Alcotest.(check int) "no rejections on example1" 0 (List.length rej1);
  let matches3, rej3 = Capability_match.select [ m ] ir3 in
  Alcotest.(check int) "example3 does not match cvc5"
    0 (List.length matches3);
  Alcotest.(check int) "1 rejection on example3" 1 (List.length rej3);
  let _, reason = List.hd rej3 in
  Alcotest.(check string) "rejection is type_construction"
    "type_construction_not_supported" (Capability_match.reason_kind reason)

(* --- Registry tests --------------------------------------------------- *)

let test_registry_loads_cvc5 () =
  let dir = fixture_dir () in
  let r, errors = Registry.load_dir dir in
  Alcotest.(check (list string)) "no load errors" [] errors;
  Alcotest.(check bool) "cvc5 is loaded"
    true (Option.is_some (Registry.find "cvc5" r));
  Alcotest.(check bool) "cvc4 is loaded"
    true (Option.is_some (Registry.find "cvc4" r))

let test_registry_skips_non_manifest_files () =
  (* Pass the [examples] directory which contains other JSON files
     (example1-, cert-, rewrite-trace-); only [manifest-...json]
     should be loaded. *)
  let dir = fixture_dir () in
  let r, errors = Registry.load_dir dir in
  Alcotest.(check (list string)) "no spurious errors from non-manifests"
    [] errors;
  Alcotest.(check bool) "non-manifest files not loaded"
    true (Option.is_none (Registry.find "example1-lia-typeclass" r))

let test_registry_rejects_duplicate_adapter () =
  let m = cvc5_manifest () in
  match Registry.of_list [ m; m ] with
  | Ok _ -> Alcotest.fail "expected duplicate-adapter error"
  | Error msg ->
    let r = Str.regexp_string "duplicate" in
    Alcotest.(check bool) "error mentions duplicate"
      true (try ignore (Str.search_forward r msg 0); true
            with Not_found -> false)

let () =
  Alcotest.run "manifest" [
    "codec", [
      Alcotest.test_case "cvc5 round-trip" `Quick test_codec_round_trip_cvc5;
      Alcotest.test_case "missing required field"
        `Quick test_decode_rejects_missing_required;
    ];
    "match", [
      Alcotest.test_case "LIA IR matches cvc5"
        `Quick test_match_on_lia_ir;
      Alcotest.test_case "higher-order IR rejected"
        `Quick test_order_too_high;
      Alcotest.test_case "EUF fragment rejected"
        `Quick test_logic_out_of_fragment;
      Alcotest.test_case "fragment=none skips fragment check"
        `Quick test_fragment_none_skips_check;
      Alcotest.test_case "quotient construction rejected"
        `Quick test_type_construction_not_supported;
      Alcotest.test_case "type vars allowed via specialization"
        `Quick test_type_var_requires_specialization_kind;
      Alcotest.test_case "type vars rejected without specialization kind"
        `Quick test_type_var_rejected_when_kind_absent;
    ];
    "fixture", [
      Alcotest.test_case "example1 matches, example3 rejects"
        `Quick test_select_partitions_example1_and_example3;
    ];
    "registry", [
      Alcotest.test_case "loads cvc5 from examples dir"
        `Quick test_registry_loads_cvc5;
      Alcotest.test_case "skips non-manifest files"
        `Quick test_registry_skips_non_manifest_files;
      Alcotest.test_case "rejects duplicate adapter"
        `Quick test_registry_rejects_duplicate_adapter;
    ];
  ]

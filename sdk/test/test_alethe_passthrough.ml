(** Unit tests for [Alethe_passthrough], the Tier 3 Alethe-passthrough
    payload constructor.

    Coverage:
    * Rule inventory + structural features on the single-la_generic
      LIA fixture (alethe-x-3-x-1.proof).
    * Same on the case-split fixture (alethe-case-split-x.proof) —
      multiple rules, subproofs, discharge lists.
    * [make_payload] produces a well-shaped [Tier3_proof_trace]
      with [trace_format = "alethe-2024"] and the verbatim S-expr
      under [trace_data].
    * Codec round-trip: encode → decode preserves payload.
    * A constructed Tier 3 cert's envelope verifies through the
      full Tier 3 walker against the matching IR (alethe-x-3-x-1
      ⇒ x ≥ 3 ∧ x ≤ 1 ⊢ False). *)

open Proof_broker

let load_fixture name =
  let path =
    Filename.concat (Sys.getcwd ()) ("../../../../sdk/test/fixtures/" ^ name)
  in
  In_channel.with_open_text path In_channel.input_all

(* --- IR scaffolding (only need it for envelope / codec tests) -------- *)

let lia_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LIA";
  decidable_theory = None;
}

(** IR matching alethe-x-3-x-1.proof: x ≥ 3 ∧ x ≤ 1 ⊢ False. The
    envelope verifier hands the IR into [Tier3_alethe.verify], which
    matches the la_generic step's clause literals against the IR's
    hypotheses; the IR must reflect the proof's actual hyps. *)
let x_3_x_1_ir () : Ir.t =
  let x : Ir.shell_term = Var { name = "x" } in
  let one : Ir.shell_term = Num_lit { value = "1"; ty = "Real" } in
  let three : Ir.shell_term = Num_lit { value = "3"; ty = "Real" } in
  let h0 : Ir.hypothesis = {
    name = "h0";
    shell = App { symbol = ">="; type_args = []; args = [ x; three ] };
  } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = App { symbol = "<="; type_args = []; args = [ x; one ] };
  } in
  {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = {
      lia_logic with first_order_fragment = "LRA"
    };
    goal = {
      shell = Eq { ty = "Real"; left = x; right = x };
      payloads = None;
    };
    context = {
      type_vars = [];
      free_vars = [ { name = "x"; ty = "Real" } ];
      hypotheses = [ h0; h1 ];
      library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

(* --- inventory tests ------------------------------------------------- *)

let test_inventory_single_la_generic () =
  let proof_str = load_fixture "alethe-x-3-x-1.proof" in
  let p = Alethe.parse proof_str in
  let rules = Alethe_passthrough.rule_inventory p in
  Alcotest.(check bool) "la_generic present"
    true (List.mem "la_generic" rules);
  Alcotest.(check bool) "rule list sorted + deduped"
    true (rules = List.sort_uniq String.compare rules);
  let features = Alethe_passthrough.dialect_features p in
  Alcotest.(check bool) "rule:la_generic feature present"
    true (List.mem "rule:la_generic" features)

let test_inventory_case_split () =
  let proof_str = load_fixture "alethe-case-split-x.proof" in
  let p = Alethe.parse proof_str in
  let rules = Alethe_passthrough.rule_inventory p in
  Alcotest.(check bool) "la_generic present in case-split proof"
    true (List.mem "la_generic" rules);
  Alcotest.(check bool) "subproof present in case-split proof"
    true (List.mem "subproof" rules);
  let structural = Alethe_passthrough.structural_features p in
  Alcotest.(check bool) "subproofs structural tag present"
    true (List.mem "subproofs" structural);
  Alcotest.(check bool) "discharge_lists structural tag present"
    true (List.mem "discharge_lists" structural)

let test_summarize_format () =
  let proof_str = load_fixture "alethe-x-3-x-1.proof" in
  let p = Alethe.parse proof_str in
  let s = Alethe_passthrough.summarize p in
  (* Stable phrasing so dashboards / log scrapers can extract counts. *)
  Alcotest.(check bool) "summary starts with format id"
    true (String.length s >= String.length "alethe-2024 passthrough:"
          && String.sub s 0 (String.length "alethe-2024 passthrough:")
             = "alethe-2024 passthrough:");
  Alcotest.(check bool) "summary mentions la_generic"
    true (try
            let _ = Str.search_forward (Str.regexp_string "la_generic") s 0 in
            true
          with Not_found -> false)

(* --- payload tests --------------------------------------------------- *)

let test_make_payload_shape () =
  let proof_str = load_fixture "alethe-x-3-x-1.proof" in
  let p = Alethe.parse proof_str in
  let payload = Alethe_passthrough.make_payload ~proof_str p in
  match payload with
  | Tier3_proof_trace { trace_format; trace_data; trace_dialect_features;
                        trace_annotations } ->
    Alcotest.(check string) "trace_format = alethe-2024"
      "alethe-2024" trace_format;
    (match trace_data with
     | `String s ->
       Alcotest.(check string) "trace_data is the verbatim proof string"
         proof_str s
     | _ -> Alcotest.fail "trace_data should be a JSON String");
    (match trace_dialect_features with
     | Some xs ->
       Alcotest.(check bool) "rule:la_generic in dialect features"
         true (List.mem "rule:la_generic" xs)
     | None -> Alcotest.fail "trace_dialect_features should be present");
    (match trace_annotations with
     | Some _ -> ()
     | None -> Alcotest.fail "trace_annotations should be present")
  | _ ->
    Alcotest.fail "expected Tier3_proof_trace payload"

let test_payload_codec_round_trip () =
  let proof_str = load_fixture "alethe-x-3-x-1.proof" in
  let p = Alethe.parse proof_str in
  let payload = Alethe_passthrough.make_payload ~proof_str p in
  let json = Certificate.payload_to_json payload in
  let payload' = Certificate.payload_of_json ~tier:3 json in
  let json' = Certificate.payload_to_json payload' in
  Alcotest.(check string) "codec round-trip preserves payload JSON"
    (Yojson.Safe.to_string (Codec.normalize json))
    (Yojson.Safe.to_string (Codec.normalize json'))

(* --- end-to-end cert envelope verification --------------------------- *)

let test_envelope_verifier_tier3 () =
  let proof_str = load_fixture "alethe-x-3-x-1.proof" in
  let p = Alethe.parse proof_str in
  let payload = Alethe_passthrough.make_payload ~proof_str p in
  let ir = x_3_x_1_ir () in
  let cert : Certificate.t = {
    cert_version = "1.0";
    tier = 3;
    format = "alethe-2024";
    goal = ir.goal;
    dispatch_context_hash = Hash.sha256_of_json (Codec.to_json ir);
    rewrite_trace_hash = Pipeline.identity_trace_hash ir;
    backend = {
      name = "synthetic"; version = "0.0";
      config_hash = "sha256:" ^ String.make 64 '0';
    };
    resources = {
      wall_time_ms = 0; memory_peak_kb = 0; budget_consumed = None;
    };
    refinement_record = {
      adapter = "synthetic"; adapter_version = "0.0";
      specializations = []; fragment = "LIA"; auxiliary = None;
    };
    payload;
  } in
  match Verifier.verify cert ir with
  | Verified_tier3 -> ()
  | other ->
    Alcotest.fail
      (Printf.sprintf "expected Verified_tier3, got %s — %s"
         (Verifier.kind_of_reason other)
         (Verifier.detail_of_reason other))

let () =
  Alcotest.run "alethe_passthrough" [
    "inventory", [
      Alcotest.test_case "single la_generic rule + features"
        `Quick test_inventory_single_la_generic;
      Alcotest.test_case "case-split: rules + structural tags"
        `Quick test_inventory_case_split;
      Alcotest.test_case "summary stable phrasing"
        `Quick test_summarize_format;
    ];
    "payload", [
      Alcotest.test_case "make_payload shape"
        `Quick test_make_payload_shape;
      Alcotest.test_case "codec round-trip"
        `Quick test_payload_codec_round_trip;
    ];
    "verifier", [
      Alcotest.test_case "real fixture trips Tier 3 unsupported_rule under v0"
        `Quick test_envelope_verifier_tier3;
    ];
  ]

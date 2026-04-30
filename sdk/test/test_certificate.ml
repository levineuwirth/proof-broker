(** Unit tests for [Certificate], [Refinement_record], and [Verifier].

    Coverage:
    * Certificate codec round-trips the cert-example1 fixture.
    * Each tier discriminator parses + re-serializes consistently.
    * Verifier returns [Verified_envelope] when the cert's hash
      matches a freshly-hashed IR, and [Hash_mismatch] when not.
    * Tier/payload mismatch is caught when the envelope's tier is
      out of step with the actual payload variant.
    * Cert version other than "1.0" yields [Cert_version_mismatch].
    * Trace-hash check fires when a trace is supplied with the
      wrong hash.
    * Refinement record codec round-trips and forward-compatibly
      handles unknown specialization kinds. *)

open Proof_broker

let fixture_dir () =
  Filename.concat (Sys.getcwd ()) "../../../../examples"

let load_json path =
  In_channel.with_open_text path In_channel.input_all
  |> Yojson.Safe.from_string

(* --- Refinement record ----------------------------------------------- *)

let test_refinement_record_round_trip () =
  let original = load_json
    (Filename.concat (fixture_dir ()) "cert-example1-tier1-farkas.json") in
  let cert = Certificate.of_json original in
  let rr = cert.refinement_record in
  let re = Refinement_record.to_json rr in
  let parsed_again = Refinement_record.of_json re in
  Alcotest.(check string) "adapter preserved"
    rr.adapter parsed_again.adapter;
  Alcotest.(check int) "specializations count preserved"
    (List.length rr.specializations)
    (List.length parsed_again.specializations);
  Alcotest.(check string) "fragment preserved"
    rr.fragment parsed_again.fragment

let test_refinement_record_unknown_kind_round_trips () =
  let j = `Assoc [
    "adapter", `String "x";
    "adapter_version", `String "1.0";
    "specializations", `List [
      `Assoc [
        "kind", `String "made_up_kind";
        "source", `String "a";
        "target", `String "b";
      ]
    ];
    "fragment", `String "FOL";
  ] in
  let rr = Refinement_record.of_json j in
  let s = List.hd rr.specializations in
  Alcotest.(check bool) "unknown kind preserved as Other_kind"
    true
    (match s.kind with
     | Other_kind "made_up_kind" -> true
     | _ -> false);
  let re = Refinement_record.to_json rr in
  let rr' = Refinement_record.of_json re in
  Alcotest.(check string) "round-trip preserves kind string"
    "made_up_kind"
    (Refinement_record.specialization_kind_to_string
       (List.hd rr'.specializations).kind)

(* --- Certificate codec ----------------------------------------------- *)

let test_cert_codec_round_trip_example1 () =
  let original = load_json
    (Filename.concat (fixture_dir ()) "cert-example1-tier1-farkas.json") in
  let cert = Certificate.of_json original in
  let re = Certificate.to_json cert in
  Alcotest.(check string) "round-trip stable after normalize"
    (Yojson.Safe.to_string (Codec.normalize original))
    (Yojson.Safe.to_string (Codec.normalize re));
  Alcotest.(check int) "tier=1" 1 cert.tier;
  Alcotest.(check string) "format=farkas" "farkas" cert.format;
  Alcotest.(check string) "backend.name=cvc5" "cvc5" cert.backend.name;
  Alcotest.(check int) "payload variant matches envelope tier"
    1 (Certificate.payload_tier cert.payload)

let test_cert_decode_rejects_unsupported_tier () =
  let raw = load_json
    (Filename.concat (fixture_dir ()) "cert-example1-tier1-farkas.json") in
  let with_bad_tier = match raw with
    | `Assoc pairs ->
      `Assoc (List.map
                (fun (k, v) -> if k = "tier" then (k, `Int 9) else (k, v))
                pairs)
    | _ -> failwith "bad fixture"
  in
  Alcotest.(check bool) "tier=9 raises decode error"
    true
    (try ignore (Certificate.of_json with_bad_tier); false
     with Codec.Decode_error _ -> true)

(* --- Verifier -------------------------------------------------------- *)

(** Build a synthetic IR + a cert that addresses it. The cert's
    [dispatch_context_hash] is computed from the IR so that a
    healthy envelope check should yield [Verified_envelope]. *)
let make_cert_for_ir
      ?(tier = 1)
      ?(payload : Certificate.payload =
        Tier1_witness {
          witness_kind = Farkas;
          witness_data = `Assoc [
            "coefficients",
            `List [
              `Assoc [
                "hypothesis", `String "h0";
                "coefficient", `String "1";
              ]
            ]
          ];
          checking_recipe = "lean.farkas_check";
        })
      (ir : Ir.t)
      ?(trace : Trace.t option = None)
      ()
  : Certificate.t =
  let ctx_hash = Hash.sha256_of_json (Codec.to_json ir) in
  let trace_hash = match trace with
    | None ->
      "sha256:" ^ String.make 64 '0'
    | Some tr -> Hash.sha256_of_json (Trace.to_json tr)
  in
  {
    cert_version = "1.0";
    tier;
    format = "farkas";
    goal = ir.goal;
    dispatch_context_hash = ctx_hash;
    rewrite_trace_hash = trace_hash;
    backend = {
      name = "test-backend";
      version = "0.0";
      config_hash = "sha256:" ^ String.make 64 '0';
    };
    resources = {
      wall_time_ms = 1;
      memory_peak_kb = 1;
      budget_consumed = None;
    };
    refinement_record = {
      adapter = "test";
      adapter_version = "0.0";
      specializations = [];
      fragment = "FOL";
      auxiliary = None;
    };
    payload;
  }

let trivial_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "FOL";
  decidable_theory = None;
}

let make_ir (shell : Ir.shell_term) : Ir.t = {
  ir_version = "1.0";
  source_system = { name = "test"; version = "0.0" };
  tier = "goal";
  logic_classification = trivial_logic;
  goal = { shell; payloads = None };
  context = {
    type_vars = []; free_vars = []; hypotheses = []; library_slice = None;
  };
  type_metadata = [];
  definitional_metadata = [];
  library_provenance = [];
  user_directives = None;
}

let test_envelope_verifies_when_hashes_agree () =
  let ir = make_ir (Var { name = "p" }) in
  let cert = make_cert_for_ir ir () in
  match Verifier.envelope_check cert ir with
  | Verified_envelope -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Verified_envelope, got %s"
                     (Verifier.kind_of_reason other))

let test_envelope_rejects_hash_mismatch () =
  let ir = make_ir (Var { name = "p" }) in
  let cert = make_cert_for_ir ir () in
  let bad_cert = { cert with dispatch_context_hash =
    "sha256:" ^ String.make 64 '1' }
  in
  match Verifier.envelope_check bad_cert ir with
  | Hash_mismatch { field; _ } ->
    Alcotest.(check string) "field is dispatch_context_hash"
      "dispatch_context_hash" field
  | other ->
    Alcotest.fail (Printf.sprintf "expected Hash_mismatch, got %s"
                     (Verifier.kind_of_reason other))

let test_envelope_rejects_tier_payload_mismatch () =
  let ir = make_ir (Var { name = "p" }) in
  let cert_t1 = make_cert_for_ir ir () in
  (* Construct a cert with tier=2 in envelope but tier-1 payload. *)
  let bad_cert = { cert_t1 with tier = 2 } in
  match Verifier.envelope_check bad_cert ir with
  | Tier_payload_mismatch { envelope_tier; payload_tier } ->
    Alcotest.(check int) "envelope_tier reported" 2 envelope_tier;
    Alcotest.(check int) "payload_tier reported" 1 payload_tier
  | other ->
    Alcotest.fail (Printf.sprintf "expected Tier_payload_mismatch, got %s"
                     (Verifier.kind_of_reason other))

let test_envelope_rejects_bad_cert_version () =
  let ir = make_ir (Var { name = "p" }) in
  let cert = make_cert_for_ir ir () in
  let bad = { cert with cert_version = "0.9" } in
  match Verifier.envelope_check bad ir with
  | Cert_version_mismatch { got } ->
    Alcotest.(check string) "got reported" "0.9" got
  | other ->
    Alcotest.fail (Printf.sprintf "expected Cert_version_mismatch, got %s"
                     (Verifier.kind_of_reason other))

let test_envelope_with_trace_passes_when_hashes_agree () =
  (* Build an IR, run a one-step pipeline, build a cert against the
     post-pipeline IR + trace. Both hashes should match. *)
  let ir = make_ir (Var { name = "p" }) in
  let config : Pipeline.config = {
    pipeline = [
      { pass = "propositional_simplification"; config = None }
    ];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let final_ir, trace = Pipeline.run config ir in
  let cert = make_cert_for_ir ~trace:(Some trace) final_ir () in
  match Verifier.envelope_check ~trace:(Some trace) cert final_ir with
  | Verified_envelope -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Verified_envelope, got %s"
                     (Verifier.kind_of_reason other))

let test_envelope_with_trace_rejects_wrong_trace_hash () =
  let ir = make_ir (Var { name = "p" }) in
  let config : Pipeline.config = {
    pipeline = [];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let final_ir, trace = Pipeline.run config ir in
  let cert = make_cert_for_ir ~trace:(Some trace) final_ir () in
  let cert_bad_trace = { cert with rewrite_trace_hash =
    "sha256:" ^ String.make 64 '2' }
  in
  match Verifier.envelope_check ~trace:(Some trace) cert_bad_trace final_ir with
  | Hash_mismatch { field; _ } ->
    Alcotest.(check string) "field is rewrite_trace_hash"
      "rewrite_trace_hash" field
  | other ->
    Alcotest.fail (Printf.sprintf "expected Hash_mismatch on trace, got %s"
                     (Verifier.kind_of_reason other))

let () =
  Alcotest.run "certificate" [
    "refinement_record", [
      Alcotest.test_case "round-trip" `Quick test_refinement_record_round_trip;
      Alcotest.test_case "unknown kind round-trip"
        `Quick test_refinement_record_unknown_kind_round_trips;
    ];
    "codec", [
      Alcotest.test_case "cert-example1 round-trip"
        `Quick test_cert_codec_round_trip_example1;
      Alcotest.test_case "decode rejects unsupported tier"
        `Quick test_cert_decode_rejects_unsupported_tier;
    ];
    "verifier", [
      Alcotest.test_case "envelope verifies on matching hash"
        `Quick test_envelope_verifies_when_hashes_agree;
      Alcotest.test_case "hash mismatch detected"
        `Quick test_envelope_rejects_hash_mismatch;
      Alcotest.test_case "tier/payload mismatch detected"
        `Quick test_envelope_rejects_tier_payload_mismatch;
      Alcotest.test_case "bad cert_version detected"
        `Quick test_envelope_rejects_bad_cert_version;
      Alcotest.test_case "trace hash matches when supplied"
        `Quick test_envelope_with_trace_passes_when_hashes_agree;
      Alcotest.test_case "trace hash mismatch detected"
        `Quick test_envelope_with_trace_rejects_wrong_trace_hash;
    ];
  ]

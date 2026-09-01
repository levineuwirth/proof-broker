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

let test_budget_decode_rejects_negative_wall_time () =
  let bad = `Assoc [ "wall_time_ms", `Int (-1) ] in
  Alcotest.(check bool) "negative wall_time_ms rejected at decode time"
    true
    (try ignore (Codec.budget_of_json bad); false
     with Codec.Decode_error _ -> true)

let test_budget_decode_rejects_negative_memory () =
  let bad = `Assoc [ "memory_mb", `Int (-1) ] in
  Alcotest.(check bool) "negative memory_mb rejected at decode time"
    true
    (try ignore (Codec.budget_of_json bad); false
     with Codec.Decode_error _ -> true)

let test_budget_decode_accepts_zero () =
  (* 0 is the schema's lower bound, must round-trip cleanly. *)
  let ok = `Assoc [ "wall_time_ms", `Int 0; "memory_mb", `Int 0 ] in
  let b = Codec.budget_of_json ok in
  Alcotest.(check (option int)) "wall_time_ms = 0" (Some 0) b.wall_time_ms;
  Alcotest.(check (option int)) "memory_mb = 0" (Some 0) b.memory_mb

let test_adapter_resolve_timeout_clamps_high () =
  let ir : Ir.t = {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = {
      order = "first_order"; features_used = [];
      first_order_fragment = "LIA"; decidable_theory = None;
    };
    goal = { shell = Const { name = "True" }; payloads = None };
    context = { type_vars = []; free_vars = []; hypotheses = [];
                library_slice = None };
    type_metadata = []; definitional_metadata = [];
    library_provenance = [];
    user_directives = Some {
      preferred_backend = None;
      tier_preference = None;
      rewriter_preferences = None;
      budget = Some { wall_time_ms = Some 1_000_000_000; memory_mb = None };
    };
  } in
  let t = Adapter.resolve_timeout_ms ~default_ms:5000 ir in
  Alcotest.(check int) "huge wall_time_ms clamped to cap"
    Adapter.max_solver_wall_time_ms t

let test_adapter_resolve_timeout_clamps_zero () =
  let ir : Ir.t = {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = {
      order = "first_order"; features_used = [];
      first_order_fragment = "LIA"; decidable_theory = None;
    };
    goal = { shell = Const { name = "True" }; payloads = None };
    context = { type_vars = []; free_vars = []; hypotheses = [];
                library_slice = None };
    type_metadata = []; definitional_metadata = [];
    library_provenance = [];
    user_directives = Some {
      preferred_backend = None;
      tier_preference = None;
      rewriter_preferences = None;
      budget = Some { wall_time_ms = Some 0; memory_mb = None };
    };
  } in
  let t = Adapter.resolve_timeout_ms ~default_ms:5000 ir in
  Alcotest.(check int) "zero wall_time_ms clamped to 1ms" 1 t

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
  (* R2: no cert carries the zero sentinel any more — with no
     explicit trace, stamp the identity trace's hash (what a direct
     dispatch of this IR would mint). *)
  let trace_hash = match trace with
    | None -> Pipeline.identity_trace_hash ir
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
      memory_peak_kb = None;
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

let test_envelope_rejects_sentinel_trace_hash () =
  (* Fail-closed pin on the R2 sentinel arm: a cert whose
     [rewrite_trace_hash] is the all-zeros sentinel is rejected with
     [Trace_hash_sentinel] even when everything else agrees and no
     trace is supplied. Deleting [check_trace_hash_sentinel] from
     [envelope_check] turns this test red (C2 ROUND 1 finding 2). *)
  let ir = make_ir (Var { name = "p" }) in
  let cert = make_cert_for_ir ir () in
  let bad = { cert with
              Certificate.rewrite_trace_hash =
                "sha256:" ^ String.make 64 '0' } in
  match Verifier.envelope_check bad ir with
  | Trace_hash_sentinel -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Trace_hash_sentinel, got %s"
                     (Verifier.kind_of_reason other))

let test_envelope_rejects_trace_endpoint_mismatch () =
  (* Fail-closed pin on the R2 endpoint arm: the trace hashes
     correctly into the cert (so [check_rewrite_trace_hash] passes)
     but its [final_ir_hash] is not the IR being verified — only
     [check_trace_endpoint] can reject. Deleting that arm turns this
     test red (C2 ROUND 1 finding 2). *)
  let ir = make_ir (Var { name = "p" }) in
  let config : Pipeline.config = {
    pipeline = [];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let final_ir, trace = Pipeline.run config ir in
  let tampered = { trace with
                   Trace.final_ir_hash = "sha256:" ^ String.make 64 'e' } in
  let cert = make_cert_for_ir ~trace:(Some tampered) final_ir () in
  match Verifier.envelope_check ~trace:(Some tampered) cert final_ir with
  | Hash_mismatch { field; _ } ->
    Alcotest.(check string) "field is trace.final_ir_hash"
      "trace.final_ir_hash" field
  | other ->
    Alcotest.fail (Printf.sprintf
                     "expected Hash_mismatch on trace endpoint, got %s"
                     (Verifier.kind_of_reason other))

(* --- end-to-end Verifier.verify (envelope + tier-specific) ---------- *)

(** Build the example1 IR shape: hypotheses [h1: n + m = 10,
    h3: 0 <= m] and goal [n <= 10]. Mirrors the linguistic shape of
    [examples/example1-lia-typeclass.json] but uses [Int] for the
    numeric type so the type-tag ambiguity isn't a factor here —
    the linearizer ignores types anyway. *)
let example1_ir () =
  let n = Ir.Var { name = "n" } in
  let m = Ir.Var { name = "m" } in
  let ten = Ir.Num_lit { value = "10"; ty = "Int" } in
  let zero_lit = Ir.Num_lit { value = "0"; ty = "Int" } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = Eq {
      ty = "Int";
      left = App { symbol = "Int.add"; type_args = []; args = [ n; m ] };
      right = ten;
    };
  } in
  let h3 : Ir.hypothesis = {
    name = "h3";
    shell = App { symbol = "LE.le"; type_args = []; args = [ zero_lit; m ] };
  } in
  let goal_shell = Ir.App {
    symbol = "LE.le"; type_args = []; args = [ n; ten ];
  } in
  let ir = make_ir goal_shell in
  { ir with context =
    { ir.context with
      free_vars = [ { name = "n"; ty = "Int" }; { name = "m"; ty = "Int" } ];
      hypotheses = [ h1; h3 ];
    }
  }

let example1_witness () : Yojson.Safe.t =
  `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "h1"; "coefficient", `String "1" ];
      `Assoc [ "hypothesis", `String "h3"; "coefficient", `String "1" ];
      `Assoc [ "hypothesis", `String "neg_goal"; "coefficient", `String "1" ];
    ];
  ]

let test_verify_envelope_plus_farkas () =
  let ir = example1_ir () in
  let cert = make_cert_for_ir ir
    ~payload:(Tier1_witness {
      witness_kind = Farkas;
      witness_data = example1_witness ();
      checking_recipe = "lean.farkas_check";
    }) ()
  in
  match Verifier.verify cert ir with
  | Verified_farkas -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Verified_farkas, got %s (%s)"
                     (Verifier.kind_of_reason other)
                     (Verifier.detail_of_reason other))

let test_verify_failed_envelope_short_circuits_before_farkas () =
  let ir = example1_ir () in
  let cert = make_cert_for_ir ir
    ~payload:(Tier1_witness {
      witness_kind = Farkas;
      witness_data = example1_witness ();
      checking_recipe = "lean.farkas_check";
    }) ()
  in
  let bad_cert = { cert with cert_version = "0.9" } in
  match Verifier.verify bad_cert ir with
  | Cert_version_mismatch _ -> ()
  | other ->
    Alcotest.fail (Printf.sprintf
                     "expected Cert_version_mismatch (envelope short-circuits), got %s"
                     (Verifier.kind_of_reason other))

let test_verify_farkas_unknown_hypothesis () =
  let ir = example1_ir () in
  let bad_witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "h99"; "coefficient", `String "1" ];
    ];
  ] in
  let cert = make_cert_for_ir ir
    ~payload:(Tier1_witness {
      witness_kind = Farkas;
      witness_data = bad_witness;
      checking_recipe = "lean.farkas_check";
    }) ()
  in
  match Verifier.verify cert ir with
  | Farkas_unknown_hypothesis { hypothesis = "h99" } -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Farkas_unknown_hypothesis, got %s"
                     (Verifier.kind_of_reason other))

let test_verify_tier_check_deferred_for_tier0 () =
  let ir = example1_ir () in
  let cert = make_cert_for_ir ir
    ~tier:0
    ~payload:(Tier0_oracle {
      claim = "proved";
      backend_attestation = None;
    }) ()
  in
  match Verifier.verify cert ir with
  | Tier_check_deferred { tier = 0 } -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Tier_check_deferred(0), got %s"
                     (Verifier.kind_of_reason other))

let test_verify_unsupported_witness_kind () =
  let ir = example1_ir () in
  let cert = make_cert_for_ir ir
    ~payload:(Tier1_witness {
      witness_kind = Sat_assignment;
      witness_data = `Assoc [];
      checking_recipe = "lean.sat_check";
    }) ()
  in
  match Verifier.verify cert ir with
  | Unsupported_witness_kind { kind = "sat_assignment" } -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "expected Unsupported_witness_kind, got %s"
                     (Verifier.kind_of_reason other))

(** End-to-end on the fixture triple: read the cert + IR + paired
    identity-trace fixture (R2: `tools/regen_cert_hashes.py` pins
    the cert's dispatch_context_hash / rewrite_trace_hash to the
    shipped IR / trace), override the cert's dispatch_context_hash
    to the IR's actual hash as re-serialized by THIS codec (guards
    the OCaml↔Python canonicalization agreement), and verify with
    the trace supplied — all four envelope hash checks run. *)
let test_verify_fixture_pair () =
  let ir_raw = load_json
    (Filename.concat (fixture_dir ()) "example1-lia-typeclass.json") in
  let cert_raw = load_json
    (Filename.concat (fixture_dir ()) "cert-example1-tier1-farkas.json") in
  let trace_raw = load_json
    (Filename.concat (fixture_dir ()) "rewrite-trace-example1-identity.json") in
  let ir = Codec.of_json ir_raw in
  let cert = Certificate.of_json cert_raw in
  let trace = Trace.of_json trace_raw in
  let real_hash = Hash.sha256_of_json (Codec.to_json ir) in
  Alcotest.(check string)
    "fixture dispatch_context_hash = canonical hash of fixture IR \
     (Python regen and OCaml codec agree)"
    real_hash cert.dispatch_context_hash;
  Alcotest.(check bool) "paired trace is identity" true
    (Trace.is_identity trace);
  let cert' = { cert with dispatch_context_hash = real_hash } in
  match Verifier.verify ~trace:(Some trace) cert' ir with
  | Verified_farkas -> ()
  | other ->
    Alcotest.fail (Printf.sprintf
                     "expected Verified_farkas on fixture pair, got %s (%s)"
                     (Verifier.kind_of_reason other)
                     (Verifier.detail_of_reason other))

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
      Alcotest.test_case "budget decode rejects negative wall_time_ms"
        `Quick test_budget_decode_rejects_negative_wall_time;
      Alcotest.test_case "budget decode rejects negative memory_mb"
        `Quick test_budget_decode_rejects_negative_memory;
      Alcotest.test_case "budget decode accepts zero"
        `Quick test_budget_decode_accepts_zero;
      Alcotest.test_case "adapter clamps wall_time_ms to cap"
        `Quick test_adapter_resolve_timeout_clamps_high;
      Alcotest.test_case "adapter clamps zero wall_time_ms to 1ms"
        `Quick test_adapter_resolve_timeout_clamps_zero;
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
      Alcotest.test_case "envelope rejects the sentinel rewrite_trace_hash"
        `Quick test_envelope_rejects_sentinel_trace_hash;
      Alcotest.test_case "envelope rejects a trace whose endpoint is not the IR"
        `Quick test_envelope_rejects_trace_endpoint_mismatch;
    ];
    "verify (envelope + tier)", [
      Alcotest.test_case "envelope + Farkas verifies on example1 shape"
        `Quick test_verify_envelope_plus_farkas;
      Alcotest.test_case "envelope failure short-circuits before Farkas"
        `Quick test_verify_failed_envelope_short_circuits_before_farkas;
      Alcotest.test_case "Farkas unknown hypothesis surfaces"
        `Quick test_verify_farkas_unknown_hypothesis;
      Alcotest.test_case "tier 0 falls through to deferred"
        `Quick test_verify_tier_check_deferred_for_tier0;
      Alcotest.test_case "unsupported witness kind surfaces"
        `Quick test_verify_unsupported_witness_kind;
      Alcotest.test_case "fixture pair (with hash override) verifies"
        `Quick test_verify_fixture_pair;
    ];
  ]

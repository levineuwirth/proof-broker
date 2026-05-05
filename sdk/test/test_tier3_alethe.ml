(** Unit tests for [Tier3_alethe], the Tier 3 alethe-2024 per-step
    re-checker.

    Coverage:
    * The single-la_generic LIA fixture verifies end-to-end
      ([Verified_tier3]).
    * The case-split fixture trips the [Unsupported_rule] bailout
      because [subproof] / [resolution] aren't yet registered.
    * A bogus la_generic step (wrong coefficient) trips
      [Step_failed] with the la_generic rule name preserved.
    * End-to-end through [Verifier.verify] on a Tier 3 cert built
      via [Alethe_passthrough.make_payload]: the alethe-x-3-x-1
      fixture lifts to [Verified_tier3]; an unknown trace_format
      surfaces as [Tier3_unsupported_format]. *)

open Proof_broker

let load_fixture name =
  let path =
    Filename.concat (Sys.getcwd ()) ("../../../../sdk/test/fixtures/" ^ name)
  in
  In_channel.with_open_text path In_channel.input_all

let lia_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LIA";
  decidable_theory = None;
}

(** IR for the trivial Farkas: [x >= 3, x <= 1 ⊢ False]. Matches
    the alethe-x-3-x-1.proof fixture's hypotheses. *)
let make_x_ir () : Ir.t =
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
      shell = Eq {
        ty = "Real"; left = x; right = x;
      };
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

(** IR matching alethe-case-split-x.proof: disjunctive hyp + two
    bounds. Used to exercise the unsupported-rule bailout. *)
let make_case_split_ir () : Ir.t =
  let x : Ir.shell_term = Var { name = "x" } in
  let zero : Ir.shell_term = Num_lit { value = "0"; ty = "Real" } in
  let one : Ir.shell_term = Num_lit { value = "1"; ty = "Real" } in
  let nine : Ir.shell_term = Num_lit { value = "9"; ty = "Real" } in
  let ten : Ir.shell_term = Num_lit { value = "10"; ty = "Real" } in
  let h_disj : Ir.hypothesis = {
    name = "h_disj";
    shell = Or {
      left = App { symbol = "<="; type_args = []; args = [ x; zero ] };
      right = App { symbol = ">="; type_args = []; args = [ x; ten ] };
    };
  } in
  let h_low : Ir.hypothesis = {
    name = "h_low";
    shell = App { symbol = ">="; type_args = []; args = [ x; one ] };
  } in
  let h_high : Ir.hypothesis = {
    name = "h_high";
    shell = App { symbol = "<="; type_args = []; args = [ x; nine ] };
  } in
  {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = {
      lia_logic with first_order_fragment = "LRA"
    };
    goal = {
      shell = Const { name = "False" };
      payloads = None;
    };
    context = {
      type_vars = [];
      free_vars = [ { name = "x"; ty = "Real" } ];
      hypotheses = [ h_disj; h_low; h_high ];
      library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

(** A synthetic minimal Alethe proof: two assumes, one la_generic
    step, one resolution step that combines la_generic's clause
    with the assumes to reach the empty clause [(cl)]. Uses only
    rules in [supported_rules]. *)
let synthetic_la_generic_only_proof : string =
  "(\n\
   (assume a0 (>= x 3))\n\
   (assume a1 (<= x 1))\n\
   (step t1 (cl (not (>= x 3)) (not (<= x 1))) \
   :rule la_generic :args (1 1))\n\
   (step t2 (cl) :rule resolution :premises (t1 a0 a1))\n\
   )"

(* --- whole-proof verifier tests ------------------------------------ *)

let test_verify_synthetic_la_generic_only () =
  let ir = make_x_ir () in
  match Tier3_alethe.verify ir synthetic_la_generic_only_proof with
  | Verified -> ()
  | Unsupported_rule { rule; step_id } ->
    Alcotest.fail (Printf.sprintf
      "expected Verified, got Unsupported_rule(%s) at %s" rule step_id)
  | Step_failed { rule; step_id; detail } ->
    Alcotest.fail (Printf.sprintf
      "expected Verified, got Step_failed at %s (rule=%s): %s"
      step_id rule detail)

let test_verify_real_fixture_unsupported () =
  (* The alethe-x-3-x-1 fixture uses 14 distinct Alethe rules.
     With la_generic + refl + trans + cong + resolution + false
     registered, the walker now gets further than v0 but still
     trips on the propositional bookkeeping rules cvc5 emits
     ([equiv_pos2], [hole], [la_mult_neg], [implies], [and_neg],
     [equiv_simplify], [equiv1], [rare_rewrite]). The bailout
     rule must be one of these — i.e., NOT in our supported set. *)
  let proof_str = load_fixture "alethe-x-3-x-1.proof" in
  let ir = make_x_ir () in
  match Tier3_alethe.verify ir proof_str with
  | Unsupported_rule { rule; _ } ->
    Alcotest.(check bool)
      (Printf.sprintf
         "bailout rule %s is not in supported_rules" rule)
      false (List.mem rule Tier3_alethe.supported_rules)
  | Verified ->
    Alcotest.fail "real fixture should not Verify yet — \
                   supported_rules doesn't cover all 14 rules"
  | Step_failed { rule; step_id; detail } ->
    Alcotest.fail (Printf.sprintf
      "expected Unsupported_rule, got Step_failed at %s (rule=%s): %s"
      step_id rule detail)

let test_verify_case_split_unsupported () =
  let proof_str = load_fixture "alethe-case-split-x.proof" in
  let ir = make_case_split_ir () in
  match Tier3_alethe.verify ir proof_str with
  | Unsupported_rule { rule; _ } ->
    Alcotest.(check bool) "bailout names a non-la_generic rule"
      true (rule <> "la_generic")
  | Verified ->
    Alcotest.fail "case-split fixture should not Verify under v0"
  | Step_failed { rule; _ } ->
    Alcotest.fail (Printf.sprintf
      "expected Unsupported_rule, got Step_failed (rule=%s)" rule)

(** Forge a la_generic step with a wrong coefficient on the second
    literal: replace the original [1] with [9999], so the matched
    Farkas witness fails the contradiction check at
    [Farkas.verify]. *)
(* --- per-rule checker tests ----------------------------------------- *)

let env_with (ir : Ir.t) (proven : (string * Alethe.Sexp.t list) list)
  : Tier3_alethe.env =
  let h = Hashtbl.create (List.length proven) in
  List.iter (fun (k, v) -> Hashtbl.replace h k v) proven;
  { ir; proven = h }

let mk_step ?(args = []) ?(premises = []) ~rule ~clause id : Alethe.step = {
  id; rule; clause;
  args = (if args = [] then None else Some args);
  premises = (if premises = [] then None else Some premises);
  discharge = None;
}

let test_check_refl_accepts () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.refl" ~rule:"refl"
    ~clause:[ List [ Atom "="; Atom "x"; Atom "x" ] ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "refl rejected (= x x): %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | Step_unsupported_rule r -> "unsupported " ^ r
       | _ -> "?"))

let test_check_refl_rejects_non_equal () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.refl" ~rule:"refl"
    ~clause:[ List [ Atom "="; Atom "x"; Atom "y" ] ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "refl should reject (= x y) with distinct sides"

let test_check_trans_accepts_chain () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ List [ Atom "="; Atom "a"; Atom "b" ] ];
    "p2", [ List [ Atom "="; Atom "b"; Atom "c" ] ];
  ] in
  let step = mk_step "t.trans" ~rule:"trans"
    ~clause:[ List [ Atom "="; Atom "a"; Atom "c" ] ]
    ~premises:[ "p1"; "p2" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "trans rejected a=b, b=c → a=c: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_trans_rejects_broken_chain () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ List [ Atom "="; Atom "a"; Atom "b" ] ];
    "p2", [ List [ Atom "="; Atom "c"; Atom "d" ] ];
  ] in
  let step = mk_step "t.trans" ~rule:"trans"
    ~clause:[ List [ Atom "="; Atom "a"; Atom "d" ] ]
    ~premises:[ "p1"; "p2" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "trans should reject broken chain"

let test_check_cong_accepts () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ List [ Atom "="; Atom "a1"; Atom "b1" ] ];
    "p2", [ List [ Atom "="; Atom "a2"; Atom "b2" ] ];
  ] in
  let step = mk_step "t.cong" ~rule:"cong"
    ~clause:[ List [ Atom "=";
                     List [ Atom "f"; Atom "a1"; Atom "a2" ];
                     List [ Atom "f"; Atom "b1"; Atom "b2" ] ] ]
    ~premises:[ "p1"; "p2" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "cong rejected: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_resolution_simple () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ Atom "p"; Atom "q" ];
    "p2", [ List [ Atom "not"; Atom "p" ] ];
  ] in
  let step = mk_step "t.res" ~rule:"resolution"
    ~clause:[ Atom "q" ]
    ~premises:[ "p1"; "p2" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "resolution rejected (p∨q), ¬p → q: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_resolution_to_empty () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ Atom "p" ];
    "p2", [ List [ Atom "not"; Atom "p" ] ];
  ] in
  let step = mk_step "t.res" ~rule:"resolution"
    ~clause:[]
    ~premises:[ "p1"; "p2" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "resolution to empty rejected: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_resolution_rejects_unsound () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ Atom "p" ];
    "p2", [ Atom "q" ];
  ] in
  (* Conclusion `r` doesn't appear in any premise; resolution
     should reject. *)
  let step = mk_step "t.res" ~rule:"resolution"
    ~clause:[ Atom "r" ]
    ~premises:[ "p1"; "p2" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "resolution should reject unsound conclusion"

let test_check_equiv_pos2_accepts () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.eq2" ~rule:"equiv_pos2"
    ~clause:[
      List [ Atom "not"; List [ Atom "="; Atom "p"; Atom "q" ] ];
      List [ Atom "not"; Atom "p" ];
      Atom "q";
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "equiv_pos2 rejected: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_equiv_pos2_rejects_mismatched_phi () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.eq2" ~rule:"equiv_pos2"
    ~clause:[
      List [ Atom "not"; List [ Atom "="; Atom "p"; Atom "q" ] ];
      List [ Atom "not"; Atom "r" ];  (* != p *)
      Atom "q";
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "equiv_pos2 should reject mismatched phi"

let test_check_equiv_simplify_phi_eq_true () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.es" ~rule:"equiv_simplify"
    ~clause:[
      List [ Atom "=";
             List [ Atom "="; Atom "phi"; Atom "true" ];
             Atom "phi" ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "equiv_simplify rejected (= φ true) ↔ φ: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_equiv_simplify_phi_eq_false () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.es" ~rule:"equiv_simplify"
    ~clause:[
      List [ Atom "=";
             List [ Atom "="; Atom "phi"; Atom "false" ];
             List [ Atom "not"; Atom "phi" ] ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "equiv_simplify rejected (= φ false) ↔ ¬φ: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_equiv_simplify_rejects_unknown_shape () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.es" ~rule:"equiv_simplify"
    ~clause:[ List [ Atom "="; Atom "p"; Atom "q" ] ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "equiv_simplify should reject (= p q)"

let test_check_and_neg_accepts () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.an" ~rule:"and_neg"
    ~clause:[
      List [ Atom "and"; Atom "p"; Atom "q"; Atom "r" ];
      List [ Atom "not"; Atom "p" ];
      List [ Atom "not"; Atom "q" ];
      List [ Atom "not"; Atom "r" ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "and_neg rejected: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_and_neg_rejects_mismatched_order () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.an" ~rule:"and_neg"
    ~clause:[
      List [ Atom "and"; Atom "p"; Atom "q" ];
      List [ Atom "not"; Atom "q" ];  (* swapped *)
      List [ Atom "not"; Atom "p" ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "and_neg should reject swapped negated literals"

let test_check_implies_accepts () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ List [ Atom "=>"; Atom "a"; Atom "b" ] ];
  ] in
  let step = mk_step "t.imp" ~rule:"implies"
    ~clause:[ List [ Atom "not"; Atom "a" ]; Atom "b" ]
    ~premises:[ "p1" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "implies rejected (=> a b) → ¬a, b: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_implies_rejects_mismatch () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ List [ Atom "=>"; Atom "a"; Atom "b" ] ];
  ] in
  let step = mk_step "t.imp" ~rule:"implies"
    ~clause:[ List [ Atom "not"; Atom "x" ]; Atom "b" ]  (* a → x *)
    ~premises:[ "p1" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "implies should reject when antecedent doesn't match"

let test_check_equiv1_accepts () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ List [ Atom "="; Atom "a"; Atom "b" ] ];
  ] in
  let step = mk_step "t.e1" ~rule:"equiv1"
    ~clause:[ List [ Atom "not"; Atom "a" ]; Atom "b" ]
    ~premises:[ "p1" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "equiv1 rejected (= a b) → ¬a, b: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_false () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.false" ~rule:"false"
    ~clause:[ List [ Atom "not"; Atom "false" ] ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "false rejected (cl (not false)): %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_verify_requires_terminal_clause () =
  (* la_generic alone, no resolution: terminates with non-empty
     clause, should fail termination check. *)
  let proof_str =
    "(\n\
     (assume a0 (>= x 3))\n\
     (assume a1 (<= x 1))\n\
     (step t1 (cl (not (>= x 3)) (not (<= x 1))) \
     :rule la_generic :args (1 1))\n\
     )"
  in
  let ir = make_x_ir () in
  match Tier3_alethe.verify ir proof_str with
  | Step_failed { detail; _ }
    when (try
            let _ = Str.search_forward
              (Str.regexp_string "final step") detail 0
            in true
          with Not_found -> false) -> ()
  | other ->
    let label = match other with
      | Verified -> "Verified"
      | Unsupported_rule { rule; _ } -> "Unsupported_rule " ^ rule
      | Step_failed { detail; _ } -> "Step_failed " ^ detail
    in
    Alcotest.fail
      (Printf.sprintf "expected Step_failed (final step …), got %s"
         label)

(* --- supported_rules / proof_rules_supported gate ------------------- *)

let test_supported_rules_sync () =
  (* Every rule listed in [supported_rules] should actually have a
     [check_step] dispatch — i.e., a step using that rule must not
     return [Step_unsupported_rule]. We can't easily produce a
     "valid" step for every rule (some need linearizable atoms,
     args, etc.), but a malformed step is enough to confirm the
     dispatch knows the rule: it'll return [Step_failed], not
     [Step_unsupported_rule]. *)
  let ir = make_x_ir () in
  let env : Tier3_alethe.env = { ir; proven = Hashtbl.create 0 } in
  List.iter (fun rule ->
    let probe : Alethe.step = {
      id = "probe"; rule;
      clause = []; args = Some []; premises = None; discharge = None;
    } in
    match Tier3_alethe.check_step env probe with
    | Step_unsupported_rule r ->
      Alcotest.fail
        (Printf.sprintf "rule %s in supported_rules but check_step \
                         returned Unsupported_rule(%s)" rule r)
    | _ -> ())
    Tier3_alethe.supported_rules

let test_proof_rules_supported_synthetic () =
  (* The minimal one-la_generic proof should pass the gate. *)
  let proof_str =
    "(\n\
     (assume a0 (>= x 3))\n\
     (assume a1 (<= x 1))\n\
     (step t1 (cl (not (>= x 3)) (not (<= x 1))) \
     :rule la_generic :args (1 1))\n\
     )"
  in
  let p = Alethe.parse proof_str in
  Alcotest.(check bool) "synthetic la_generic-only proof passes gate"
    true (Tier3_alethe.proof_rules_supported p)

let test_proof_rules_supported_real_fixture () =
  (* Real cvc5 fixture has 14 distinct rules; gate should fail. *)
  let proof_str = load_fixture "alethe-x-3-x-1.proof" in
  let p = Alethe.parse proof_str in
  Alcotest.(check bool) "real cvc5 fixture fails gate (rules beyond v0)"
    false (Tier3_alethe.proof_rules_supported p)

let test_verify_step_failed () =
  let ir = make_x_ir () in
  let bogus_step : Alethe.step = {
    id = "t.bogus";
    rule = "la_generic";
    clause = [
      (* Negated atoms over LRA: ¬(x ≥ 3) and ¬(x ≤ 1). *)
      List [ Atom "not"; List [ Atom ">="; Atom "x"; Atom "3" ] ];
      List [ Atom "not"; List [ Atom "<="; Atom "x"; Atom "1" ] ];
    ];
    args = Some [
      Atom "1";
      Atom "9999";  (* bogus *)
    ];
    premises = None;
    discharge = None;
  } in
  let env : Tier3_alethe.env = { ir; proven = Hashtbl.create 0 } in
  match Tier3_alethe.check_step env bogus_step with
  | Step_failed { rule; _ } ->
    Alcotest.(check string) "rule preserved on failure"
      "la_generic" rule
  | Step_verified ->
    Alcotest.fail "expected Step_failed on bogus coefficient, \
                   got Step_verified"
  | Step_unsupported_rule rule ->
    Alcotest.fail
      (Printf.sprintf "expected Step_failed, got Step_unsupported_rule(%s)"
         rule)

(* --- end-to-end through Verifier.verify ----------------------------- *)

let test_end_to_end_tier3_verified () =
  let proof_str = synthetic_la_generic_only_proof in
  let p = Alethe.parse proof_str in
  let payload = Alethe_passthrough.make_payload ~proof_str p in
  let ir = make_x_ir () in
  let cert : Certificate.t = {
    cert_version = "1.0";
    tier = 3;
    format = "alethe-2024";
    goal = ir.goal;
    dispatch_context_hash = Hash.sha256_of_json (Codec.to_json ir);
    rewrite_trace_hash = "sha256:" ^ String.make 64 '0';
    backend = {
      name = "synthetic"; version = "0.0";
      config_hash = "sha256:" ^ String.make 64 '0';
    };
    resources = {
      wall_time_ms = 0; memory_peak_kb = 0; budget_consumed = None;
    };
    refinement_record = {
      adapter = "synthetic"; adapter_version = "0.0";
      specializations = []; fragment = "LRA"; auxiliary = None;
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

let test_end_to_end_unsupported_format () =
  let ir = make_x_ir () in
  let payload : Certificate.payload = Tier3_proof_trace {
    trace_format = "lfsc";
    trace_data = `String "(... not alethe ...)";
    trace_dialect_features = None;
    trace_annotations = None;
  } in
  let cert : Certificate.t = {
    cert_version = "1.0";
    tier = 3;
    format = "lfsc";
    goal = ir.goal;
    dispatch_context_hash = Hash.sha256_of_json (Codec.to_json ir);
    rewrite_trace_hash = "sha256:" ^ String.make 64 '0';
    backend = {
      name = "synthetic"; version = "0.0";
      config_hash = "sha256:" ^ String.make 64 '0';
    };
    resources = {
      wall_time_ms = 0; memory_peak_kb = 0; budget_consumed = None;
    };
    refinement_record = {
      adapter = "synthetic"; adapter_version = "0.0";
      specializations = []; fragment = "LRA"; auxiliary = None;
    };
    payload;
  } in
  match Verifier.verify cert ir with
  | Tier3_unsupported_format { trace_format } ->
    Alcotest.(check string) "trace_format reported on bailout"
      "lfsc" trace_format
  | other ->
    Alcotest.fail
      (Printf.sprintf "expected Tier3_unsupported_format, got %s"
         (Verifier.kind_of_reason other))

let () =
  Alcotest.run "tier3_alethe" [
    "whole-proof", [
      Alcotest.test_case "synthetic la_generic-only proof verifies"
        `Quick test_verify_synthetic_la_generic_only;
      Alcotest.test_case "real fixture bailouts on unsupported rule"
        `Quick test_verify_real_fixture_unsupported;
      Alcotest.test_case "case-split bailouts on unsupported rule"
        `Quick test_verify_case_split_unsupported;
      Alcotest.test_case "bogus la_generic surfaces step_failed"
        `Quick test_verify_step_failed;
    ];
    "gate", [
      Alcotest.test_case "supported_rules in sync with check_step"
        `Quick test_supported_rules_sync;
      Alcotest.test_case "synthetic proof passes gate"
        `Quick test_proof_rules_supported_synthetic;
      Alcotest.test_case "real fixture fails gate"
        `Quick test_proof_rules_supported_real_fixture;
    ];
    "rules", [
      Alcotest.test_case "refl accepts (= x x)"
        `Quick test_check_refl_accepts;
      Alcotest.test_case "refl rejects (= x y)"
        `Quick test_check_refl_rejects_non_equal;
      Alcotest.test_case "trans accepts a=b ∧ b=c → a=c"
        `Quick test_check_trans_accepts_chain;
      Alcotest.test_case "trans rejects broken chain"
        `Quick test_check_trans_rejects_broken_chain;
      Alcotest.test_case "cong accepts per-arg equalities"
        `Quick test_check_cong_accepts;
      Alcotest.test_case "resolution: (p∨q), ¬p → q"
        `Quick test_check_resolution_simple;
      Alcotest.test_case "resolution: p, ¬p → ()"
        `Quick test_check_resolution_to_empty;
      Alcotest.test_case "resolution rejects unsound conclusion"
        `Quick test_check_resolution_rejects_unsound;
      Alcotest.test_case "false rule accepts (cl (not false))"
        `Quick test_check_false;
      Alcotest.test_case "equiv_pos2 accepts tautology"
        `Quick test_check_equiv_pos2_accepts;
      Alcotest.test_case "equiv_pos2 rejects mismatched phi"
        `Quick test_check_equiv_pos2_rejects_mismatched_phi;
      Alcotest.test_case "equiv_simplify (= φ true) ↔ φ"
        `Quick test_check_equiv_simplify_phi_eq_true;
      Alcotest.test_case "equiv_simplify (= φ false) ↔ ¬φ"
        `Quick test_check_equiv_simplify_phi_eq_false;
      Alcotest.test_case "equiv_simplify rejects unknown shape"
        `Quick test_check_equiv_simplify_rejects_unknown_shape;
      Alcotest.test_case "and_neg accepts (and ...) + negated literals"
        `Quick test_check_and_neg_accepts;
      Alcotest.test_case "and_neg rejects mismatched order"
        `Quick test_check_and_neg_rejects_mismatched_order;
      Alcotest.test_case "implies accepts (=> a b) → ¬a, b"
        `Quick test_check_implies_accepts;
      Alcotest.test_case "implies rejects when antecedent mismatch"
        `Quick test_check_implies_rejects_mismatch;
      Alcotest.test_case "equiv1 accepts (= a b) → ¬a, b"
        `Quick test_check_equiv1_accepts;
    ];
    "termination", [
      Alcotest.test_case "non-terminal final clause rejected"
        `Quick test_verify_requires_terminal_clause;
    ];
    "verifier-end-to-end", [
      Alcotest.test_case "Tier 3 alethe-2024 cert verifies"
        `Quick test_end_to_end_tier3_verified;
      Alcotest.test_case "non-alethe trace_format surfaces unsupported_format"
        `Quick test_end_to_end_unsupported_format;
    ];
  ]

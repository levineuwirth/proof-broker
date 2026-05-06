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

(** Negative test: a malicious proof that smuggles in an extra
    top-level [(assume a99 false)] not backed by any IR fact must
    be rejected at validate time, before any step is walked.
    Without the fix, this would have verified trivially since
    [false] could be resolved with [(not false)] to derive (cl). *)
let test_verify_rejects_unbacked_top_level_assume () =
  let bogus_proof =
    "(\n\
     (assume a0 (>= x 3))\n\
     (assume a1 (<= x 1))\n\
     (assume a99 false)\n\
     (step t1 (cl (not false)) :rule false)\n\
     (step t2 (cl) :rule resolution :premises (t1 a99))\n\
     )"
  in
  let ir = make_x_ir () in
  match Tier3_alethe.verify ir bogus_proof with
  | Verified ->
    Alcotest.fail "expected validation rejection of unbacked top-level assume"
  | Step_failed { rule = "<assume>"; _ } -> ()
  | Step_failed { rule; step_id; detail } ->
    Alcotest.fail (Printf.sprintf
      "expected <assume> rejection, got Step_failed at %s (rule=%s): %s"
      step_id rule detail)
  | Unsupported_rule { rule; step_id } ->
    Alcotest.fail (Printf.sprintf
      "expected <assume> rejection, got Unsupported_rule(%s) at %s"
      rule step_id)

(** Unit test on [proven_in_scope]: a top-level step's id has no
    enclosing subproof, so any subproof-local id is out of scope.
    A step inside subproof [t1] sees [t1.*] but not [t22.*]. *)
let test_proven_in_scope_filters_local_assumes () =
  let ir = make_x_ir () in
  let proven = Hashtbl.create 4 in
  Hashtbl.replace proven "t1.a0" [ Alethe.Sexp.Atom "A_t1" ];
  Hashtbl.replace proven "t22.a0" [ Alethe.Sexp.Atom "A_t22" ];
  Hashtbl.replace proven "global" [ Alethe.Sexp.Atom "G" ];
  let env : Tier3_alethe.env = {
    ir; proven; assumes = Hashtbl.create 0;
    last_step_clause = None;
    last_step_id = None;
  } in
  let mk_at id : Alethe.step = {
    id; rule = "any"; clause = []; args = None;
    premises = None; discharge = None;
  } in
  (* Top-level step: only globals in scope. *)
  Alcotest.(check bool) "top-level sees global"
    true (Option.is_some (Tier3_alethe.proven_in_scope env (mk_at "outer") "global"));
  Alcotest.(check bool) "top-level cannot see t1.a0"
    true (Option.is_none (Tier3_alethe.proven_in_scope env (mk_at "outer") "t1.a0"));
  Alcotest.(check bool) "top-level cannot see t22.a0"
    true (Option.is_none (Tier3_alethe.proven_in_scope env (mk_at "outer") "t22.a0"));
  (* Step inside t1: sees t1.* and globals, not t22.*. *)
  Alcotest.(check bool) "inside t1 sees t1.a0"
    true (Option.is_some (Tier3_alethe.proven_in_scope env (mk_at "t1.t10") "t1.a0"));
  Alcotest.(check bool) "inside t1 sees global"
    true (Option.is_some (Tier3_alethe.proven_in_scope env (mk_at "t1.t10") "global"));
  Alcotest.(check bool) "inside t1 cannot see t22.a0"
    true (Option.is_none (Tier3_alethe.proven_in_scope env (mk_at "t1.t10") "t22.a0"));
  (* Step inside t22 cannot see t1.a0 either (siblings). *)
  Alcotest.(check bool) "inside t22 cannot see t1.a0"
    true (Option.is_none (Tier3_alethe.proven_in_scope env (mk_at "t22.t5") "t1.a0"));
  (* Deeply nested t1.t5.t10 sees t1.* and t1.t5.* but not t1.t6.*. *)
  Alcotest.(check bool) "nested step sees outer-subproof assume"
    true (Option.is_some (Tier3_alethe.proven_in_scope env (mk_at "t1.t5.t10") "t1.a0"))

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

let test_verify_real_fixture_verified () =
  (* The alethe-x-3-x-1 fixture uses 14 distinct Alethe rules.
     With the full registry — la_generic, refl, trans, cong,
     resolution, false, equiv_pos2, equiv_simplify, and_neg,
     implies, equiv1, la_mult_neg, hole, rare_rewrite — the
     walker now verifies the proof end-to-end. This is the
     "real cvc5 proof verified by the Tier 3 walker" milestone. *)
  let proof_str = load_fixture "alethe-x-3-x-1.proof" in
  let ir = make_x_ir () in
  match Tier3_alethe.verify ir proof_str with
  | Verified -> ()
  | Unsupported_rule { rule; step_id } ->
    Alcotest.fail (Printf.sprintf
      "expected Verified, got Unsupported_rule(%s) at %s" rule step_id)
  | Step_failed { rule; step_id; detail } ->
    Alcotest.fail (Printf.sprintf
      "expected Verified, got Step_failed at %s (rule=%s): %s"
      step_id rule detail)

let test_verify_case_split_verified () =
  (* The alethe-case-split-x fixture exercises the full subproof
     path: anchor blocks bracketing local assumes, la_generic
     steps inside subproofs (which need local-assume Farkas
     inputs), the [subproof] discharge close, plus the proposition
     bookkeeping rules around them ([implies_neg1/2], [and_pos],
     [reordering], [contraction], [not_and], [or], [symm], etc.).
     The whole proof verifies end-to-end now that all 24 rules
     are registered. *)
  let proof_str = load_fixture "alethe-case-split-x.proof" in
  let ir = make_case_split_ir () in
  match Tier3_alethe.verify ir proof_str with
  | Verified -> ()
  | Unsupported_rule { rule; step_id } ->
    Alcotest.fail (Printf.sprintf
      "expected Verified, got Unsupported_rule(%s) at %s" rule step_id)
  | Step_failed { rule; step_id; detail } ->
    Alcotest.fail (Printf.sprintf
      "expected Verified, got Step_failed at %s (rule=%s): %s"
      step_id rule detail)

(** Forge a la_generic step with a wrong coefficient on the second
    literal: replace the original [1] with [9999], so the matched
    Farkas witness fails the contradiction check at
    [Farkas.verify]. *)
(* --- per-rule checker tests ----------------------------------------- *)

let env_with (ir : Ir.t) (proven : (string * Alethe.Sexp.t list) list)
  : Tier3_alethe.env =
  let h = Hashtbl.create (List.length proven) in
  List.iter (fun (k, v) -> Hashtbl.replace h k v) proven;
  { ir; proven = h; assumes = Hashtbl.create 0;
    last_step_clause = None; last_step_id = None }

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

let test_check_hole_const_arith () =
  (* hole asserts (-1)*3 = -3 — constant arithmetic fold. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom "*"; Atom "-1/1"; Atom "3/1" ];
             Atom "-3/1" ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "hole rejected (* -1 3) = -3: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_hole_x_minus_x () =
  (* hole asserts x + (-x) = 0 — algebraic identity, x cancels. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom "+";
                    Atom "x";
                    List [ Atom "*"; Atom "-1/1"; Atom "x" ] ];
             Atom "0/1" ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "hole rejected (+ x (* -1 x)) = 0: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_hole_bool_eval_false () =
  (* (<= 0 -2) = false — comparison evaluates to false. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom "<="; Atom "0/1"; Atom "-2/1" ];
             Atom "false" ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "hole rejected (<= 0 -2) = false: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_hole_rejects_wrong_const () =
  (* hole asserts (-1)*3 = 5 — bogus constant. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom "*"; Atom "-1/1"; Atom "3/1" ];
             Atom "5/1" ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "hole should reject (* -1 3) = 5"

let test_check_hole_rejects_wrong_bool () =
  (* (<= 0 -2) = true — comparison is false, so RHS=true is wrong. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom "<="; Atom "0/1"; Atom "-2/1" ];
             Atom "true" ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "hole should reject (<= 0 -2) = true"

let test_check_hole_direction_flip () =
  (* (<= 0 m) = (>= m 0): direction flip on inequality. Both sides
     normalize to Le(-m). *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom "<="; Atom "0/1"; Atom "m" ];
             List [ Atom ">="; Atom "m"; Atom "0/1" ] ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "hole rejected direction flip: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_hole_double_negation () =
  (* (not (not (>= n 11))) = (>= n 11). Both sides normalize to
     Le(11 - n) — the outer not pair cancels. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom "not";
                    List [ Atom "not";
                           List [ Atom ">="; Atom "n"; Atom "11/1" ] ] ];
             List [ Atom ">="; Atom "n"; Atom "11/1" ] ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "hole rejected double negation: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

(** Build an LIA-fragment IR so the LIA tightening tests can exercise
    the +1 trick path inside [normalize_literal]. *)
let make_lia_ir () : Ir.t =
  let ir = make_x_ir () in
  { ir with
    logic_classification = {
      ir.logic_classification with first_order_fragment = "LIA"
    }
  }

let test_check_hole_lia_tightening () =
  (* Over LIA, (<= n 10) = (not (>= n 11)). Both sides normalize
     to Le(n - 10): LHS directly, RHS via negate-Le(11-n) →
     Lt(n-11) → +1 trick → Le(n-10). The check requires fragment=LIA;
     under LRA the tightening is unsound and we'd reject. *)
  let ir = make_lia_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom "<="; Atom "n"; Atom "10/1" ];
             List [ Atom "not";
                    List [ Atom ">="; Atom "n"; Atom "11/1" ] ] ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "hole rejected LIA tightening: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_hole_lia_tightening_rejected_in_lra () =
  (* The same LIA tightening shape is unsound over LRA — there's a
     gap between (<= n 10) and (not (>= n 11)) at non-integer n
     in [10, 11). Under LRA fragment, the +1 trick doesn't fire,
     and the two sides normalize to different Farkas forms. *)
  let ir = make_x_ir () in  (* LRA *)
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom "<="; Atom "n"; Atom "10/1" ];
             List [ Atom "not";
                    List [ Atom ">="; Atom "n"; Atom "11/1" ] ] ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "hole should reject LIA tightening under LRA"

let test_check_hole_equation_rearrangement () =
  (* hole asserts (= (+ n m) 10) = (= n (+ 10 -m)). Both sides
     compile to Eq(n + m - 10) once linearized. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom "=";
                    List [ Atom "+"; Atom "n"; Atom "m" ];
                    Atom "10/1" ];
             List [ Atom "=";
                    Atom "n";
                    List [ Atom "+";
                           Atom "10/1";
                           List [ Atom "*"; Atom "-1/1"; Atom "m" ] ] ] ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "hole rejected equation rearrangement: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_hole_combined_arith_lia () =
  (* hole asserts (>= (+ 10 -m) 11) = (not (>= m 0)) over LIA.
     LHS: 10 - m >= 11 normalizes to Le(m + 1).
     RHS: ¬(m >= 0) → strip not → (>= m 0) → Le(-m) → negate to
       Lt(m) → LIA +1 → Le(m + 1).
     Same. *)
  let ir = make_lia_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom ">=";
                    List [ Atom "+";
                           Atom "10/1";
                           List [ Atom "*"; Atom "-1/1"; Atom "m" ] ];
                    Atom "11/1" ];
             List [ Atom "not";
                    List [ Atom ">="; Atom "m"; Atom "0/1" ] ] ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "hole rejected combined arith+LIA: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_hole_constant_bool_eval () =
  (* (not (not true)) = true: nested constant-boolean evaluation. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.h" ~rule:"hole"
    ~clause:[
      List [ Atom "=";
             List [ Atom "not"; List [ Atom "not"; Atom "true" ] ];
             Atom "true" ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "hole rejected (not (not true)) = true: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_implies_neg1 () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.in1" ~rule:"implies_neg1"
    ~clause:[
      List [ Atom "=>"; Atom "a"; Atom "b" ];
      Atom "a";
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "implies_neg1 rejected (cl (=> a b) a): %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_implies_neg2 () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.in2" ~rule:"implies_neg2"
    ~clause:[
      List [ Atom "=>"; Atom "a"; Atom "b" ];
      List [ Atom "not"; Atom "b" ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "implies_neg2 rejected (cl (=> a b) (not b)): %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_implies_simplify () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.is" ~rule:"implies_simplify"
    ~clause:[
      List [ Atom "=";
             List [ Atom "=>"; Atom "a"; Atom "false" ];
             List [ Atom "not"; Atom "a" ] ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "implies_simplify rejected: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_and_pos () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.ap" ~rule:"and_pos"
    ~args:[ Atom "1" ]
    ~clause:[
      List [ Atom "not"; List [ Atom "and"; Atom "p"; Atom "q"; Atom "r" ] ];
      Atom "q";
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "and_pos rejected i=1 → q: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_and_pos_rejects_wrong_index () =
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.ap" ~rule:"and_pos"
    ~args:[ Atom "1" ]
    ~clause:[
      List [ Atom "not"; List [ Atom "and"; Atom "p"; Atom "q" ] ];
      Atom "p";  (* should be q at i=1 *)
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "and_pos should reject wrong-index projection"

let test_check_reordering () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ Atom "a"; Atom "b"; Atom "c" ];
  ] in
  let step = mk_step "t.r" ~rule:"reordering"
    ~clause:[ Atom "c"; Atom "a"; Atom "b" ]
    ~premises:[ "p1" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "reordering rejected permutation: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_contraction () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ Atom "a"; Atom "b"; Atom "a"; Atom "c"; Atom "b" ];
  ] in
  let step = mk_step "t.c" ~rule:"contraction"
    ~clause:[ Atom "a"; Atom "b"; Atom "c" ]
    ~premises:[ "p1" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "contraction rejected dup-collapse: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_not_and () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ List [ Atom "not"; List [ Atom "and"; Atom "p"; Atom "q"; Atom "r" ] ] ];
  ] in
  let step = mk_step "t.na" ~rule:"not_and"
    ~clause:[
      List [ Atom "not"; Atom "p" ];
      List [ Atom "not"; Atom "q" ];
      List [ Atom "not"; Atom "r" ];
    ]
    ~premises:[ "p1" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "not_and rejected De Morgan: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_or () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ List [ Atom "or"; Atom "a"; Atom "b"; Atom "c" ] ];
  ] in
  let step = mk_step "t.or" ~rule:"or"
    ~clause:[ Atom "a"; Atom "b"; Atom "c" ]
    ~premises:[ "p1" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "or rejected disjunction unwrap: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_symm () =
  let ir = make_x_ir () in
  let env = env_with ir [
    "p1", [ List [ Atom "="; Atom "a"; Atom "b" ] ];
  ] in
  let step = mk_step "t.s" ~rule:"symm"
    ~clause:[ List [ Atom "="; Atom "b"; Atom "a" ] ]
    ~premises:[ "p1" ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "symm rejected: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_subproof () =
  (* A minimal subproof shape: one local assume A, body proves
     (cl B), close concludes (cl (not A) B). The walker has just
     verified the body step (last_step_clause = [B]) and a0 was
     seeded into env.proven and env.assumes as A. *)
  let ir = make_x_ir () in
  let env = env_with ir [
    "t1.a0", [ Atom "A" ];
  ] in
  Hashtbl.replace env.assumes "t1.a0" (Atom "A");
  env.last_step_clause <- Some [ Atom "B" ];
  env.last_step_id <- Some "t1.body";
  let step : Alethe.step = {
    id = "t1"; rule = "subproof";
    clause = [ List [ Atom "not"; Atom "A" ]; Atom "B" ];
    args = None; premises = None;
    discharge = Some [ "t1.a0" ];
  } in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "subproof rejected discharge close: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_subproof_rejects_nested_body_conclusion () =
  (* Closing t1 while the most recent verified step lives inside
     t1.t2 (an unsealed nested subproof) must be rejected: the
     close would otherwise lift a clause derived under unsealed
     nested-local assumptions. *)
  let ir = make_x_ir () in
  let env = env_with ir [
    "t1.a0", [ Atom "A" ];
  ] in
  Hashtbl.replace env.assumes "t1.a0" (Atom "A");
  env.last_step_clause <- Some [ Atom "B" ];
  env.last_step_id <- Some "t1.t2.body";
  let step : Alethe.step = {
    id = "t1"; rule = "subproof";
    clause = [ List [ Atom "not"; Atom "A" ]; Atom "B" ];
    args = None; premises = None;
    discharge = Some [ "t1.a0" ];
  } in
  match Tier3_alethe.check_step env step with
  | Step_failed { detail; _ } ->
    let pat = Str.regexp_string "direct child" in
    Alcotest.(check bool) "diagnostics mentions 'direct child'"
      true (try ignore (Str.search_forward pat detail 0); true
            with Not_found -> false)
  | _ ->
    Alcotest.fail
      "subproof close with nested body conclusion should have been rejected"

let test_verify_rejects_dotted_assume_without_anchor () =
  (* Top-level (assume t1.t2.a0 false) without any (anchor :step t1)
     is structurally illegitimate. The parser collects it but
     [validate_anchor_structure] rejects it before any step runs. *)
  let ir = make_x_ir () in
  let bogus =
    "(\n\
     (assume t1.t2.a0 false)\n\
     (step t.bot (cl false) :rule resolution :premises (t1.t2.a0))\n\
     )"
  in
  match Tier3_alethe.verify ir bogus with
  | Step_failed { rule = "<anchor>"; detail; _ } ->
    let pat = Str.regexp_string "no matching (anchor" in
    Alcotest.(check bool) "diagnostics points at the missing anchor"
      true (try ignore (Str.search_forward pat detail 0); true
            with Not_found -> false)
  | other ->
    Alcotest.fail
      (Printf.sprintf
         "expected anchor-validation failure, got %s"
         (match other with
          | Verified -> "Verified"
          | Step_failed { rule; _ } -> "Step_failed[" ^ rule ^ "]"
          | Unsupported_rule { rule; _ } -> "Unsupported_rule[" ^ rule ^ "]"))

let test_check_rare_rewrite_evaluate () =
  (* (< -1 0) = true — fixture's rare_rewrite "evaluate" instance. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.rr" ~rule:"rare_rewrite"
    ~args:[ Atom "\"evaluate\"" ]
    ~clause:[
      List [ Atom "=";
             List [ Atom "<"; Atom "-1/1"; Atom "0/1" ];
             Atom "true" ];
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "rare_rewrite rejected (< -1 0) = true: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_la_mult_neg_accepts () =
  (* Canonical fixture shape: (=> (and (< -1 0) (>= x 3)) (<= -x -3)).
     Both (>= x 3) and (<= -x -3) linearize to Le(3 - x), and the
     hyp scaled by |c| = 1 is the same form, so the check passes. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.lmn" ~rule:"la_mult_neg"
    ~clause:[
      List [
        Atom "=>";
        List [ Atom "and";
               List [ Atom "<"; Atom "-1/1"; Atom "0/1" ];
               List [ Atom ">="; Atom "x"; Atom "3/1" ] ];
        List [ Atom "<=";
               List [ Atom "*"; Atom "-1/1"; Atom "x" ];
               List [ Atom "*"; Atom "-1/1"; Atom "3/1" ] ];
      ]
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "la_mult_neg rejected canonical shape: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

let test_check_la_mult_neg_rejects_positive_c () =
  (* c = 1 > 0 should be rejected — the rule requires c < 0. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.lmn" ~rule:"la_mult_neg"
    ~clause:[
      List [
        Atom "=>";
        List [ Atom "and";
               List [ Atom "<"; Atom "1/1"; Atom "0/1" ];
               List [ Atom ">="; Atom "x"; Atom "3/1" ] ];
        List [ Atom "<="; Atom "x"; Atom "3/1" ];
      ]
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "la_mult_neg should reject c >= 0"

let test_check_la_mult_neg_rejects_wrong_scale () =
  (* c = -1, hyp = (>= x 3), but conc claims (<= -x -10) instead of
     (<= -x -3) — the conclusion isn't hyp scaled by |c|. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.lmn" ~rule:"la_mult_neg"
    ~clause:[
      List [
        Atom "=>";
        List [ Atom "and";
               List [ Atom "<"; Atom "-1/1"; Atom "0/1" ];
               List [ Atom ">="; Atom "x"; Atom "3/1" ] ];
        List [ Atom "<=";
               List [ Atom "*"; Atom "-1/1"; Atom "x" ];
               Atom "-10" ];
      ]
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_failed _ -> ()
  | _ -> Alcotest.fail "la_mult_neg should reject mismatched scale"

let test_check_la_mult_neg_scale_two () =
  (* c = -2, hyp = (>= x 3), conc = (<= -2*x -2*3). Hyp's Farkas
     form is Le(3 - x); scaled by |c|=2 is Le(6 - 2x). Conc
     linearizes to Le((-2x) - (-6)) = Le(-2x + 6). Both equal
     Le(-2x + 6) so the check accepts. *)
  let ir = make_x_ir () in
  let env = env_with ir [] in
  let step = mk_step "t.lmn" ~rule:"la_mult_neg"
    ~clause:[
      List [
        Atom "=>";
        List [ Atom "and";
               List [ Atom "<"; Atom "-2/1"; Atom "0/1" ];
               List [ Atom ">="; Atom "x"; Atom "3/1" ] ];
        List [ Atom "<=";
               List [ Atom "*"; Atom "-2/1"; Atom "x" ];
               List [ Atom "*"; Atom "-2/1"; Atom "3/1" ] ];
      ]
    ]
  in
  match Tier3_alethe.check_step env step with
  | Step_verified -> ()
  | other ->
    Alcotest.fail (Printf.sprintf "la_mult_neg c=-2 rejected: %s"
      (match other with
       | Step_failed { detail; _ } -> detail
       | _ -> "?"))

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
  let env : Tier3_alethe.env = {
    ir; proven = Hashtbl.create 0; assumes = Hashtbl.create 0;
    last_step_clause = None; last_step_id = None;
  } in
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
  (* Real cvc5 fixture: all 14 rules are registered in the
     supported_rules set, so the rule-name pre-check now passes.
     (Whether the *full* verifier accepts the proof is a separate
     question, addressed by test_verify_real_fixture_verified.) *)
  let proof_str = load_fixture "alethe-x-3-x-1.proof" in
  let p = Alethe.parse proof_str in
  Alcotest.(check bool) "real cvc5 fixture passes rule-name gate"
    true (Tier3_alethe.proof_rules_supported p)

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
  let env : Tier3_alethe.env = {
    ir; proven = Hashtbl.create 0; assumes = Hashtbl.create 0;
    last_step_clause = None; last_step_id = None;
  } in
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
      Alcotest.test_case "rejects unbacked top-level assume"
        `Quick test_verify_rejects_unbacked_top_level_assume;
      Alcotest.test_case "proven_in_scope filters local assumes by ID prefix"
        `Quick test_proven_in_scope_filters_local_assumes;
      Alcotest.test_case "real cvc5 fixture verifies end-to-end"
        `Quick test_verify_real_fixture_verified;
      Alcotest.test_case "case-split fixture verifies end-to-end"
        `Quick test_verify_case_split_verified;
      Alcotest.test_case "bogus la_generic surfaces step_failed"
        `Quick test_verify_step_failed;
    ];
    "gate", [
      Alcotest.test_case "supported_rules in sync with check_step"
        `Quick test_supported_rules_sync;
      Alcotest.test_case "synthetic proof passes gate"
        `Quick test_proof_rules_supported_synthetic;
      Alcotest.test_case "real fixture passes rule-name gate"
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
      Alcotest.test_case "la_mult_neg accepts canonical c=-1 shape"
        `Quick test_check_la_mult_neg_accepts;
      Alcotest.test_case "la_mult_neg rejects c >= 0"
        `Quick test_check_la_mult_neg_rejects_positive_c;
      Alcotest.test_case "la_mult_neg rejects wrong-scale conclusion"
        `Quick test_check_la_mult_neg_rejects_wrong_scale;
      Alcotest.test_case "la_mult_neg accepts c=-2 scaling"
        `Quick test_check_la_mult_neg_scale_two;
      Alcotest.test_case "hole accepts (* -1 3) = -3 (const arith)"
        `Quick test_check_hole_const_arith;
      Alcotest.test_case "hole accepts (+ x (* -1 x)) = 0 (cancellation)"
        `Quick test_check_hole_x_minus_x;
      Alcotest.test_case "hole accepts (<= 0 -2) = false (bool eval)"
        `Quick test_check_hole_bool_eval_false;
      Alcotest.test_case "hole rejects wrong constant"
        `Quick test_check_hole_rejects_wrong_const;
      Alcotest.test_case "hole rejects wrong boolean"
        `Quick test_check_hole_rejects_wrong_bool;
      Alcotest.test_case "rare_rewrite accepts (< -1 0) = true"
        `Quick test_check_rare_rewrite_evaluate;
      Alcotest.test_case "hole accepts direction flip (<= 0 m) = (>= m 0)"
        `Quick test_check_hole_direction_flip;
      Alcotest.test_case "hole accepts double negation collapse"
        `Quick test_check_hole_double_negation;
      Alcotest.test_case "hole accepts LIA tightening (<= n 10) = (not (>= n 11))"
        `Quick test_check_hole_lia_tightening;
      Alcotest.test_case "hole rejects LIA tightening shape under LRA"
        `Quick test_check_hole_lia_tightening_rejected_in_lra;
      Alcotest.test_case "hole accepts equation rearrangement"
        `Quick test_check_hole_equation_rearrangement;
      Alcotest.test_case "hole accepts combined arith + LIA tightening"
        `Quick test_check_hole_combined_arith_lia;
      Alcotest.test_case "hole accepts nested-not constant-bool eval"
        `Quick test_check_hole_constant_bool_eval;
      Alcotest.test_case "implies_neg1 accepts (cl (=> A B) A)"
        `Quick test_check_implies_neg1;
      Alcotest.test_case "implies_neg2 accepts (cl (=> A B) (not B))"
        `Quick test_check_implies_neg2;
      Alcotest.test_case "implies_simplify accepts (=> A false) ↔ (not A)"
        `Quick test_check_implies_simplify;
      Alcotest.test_case "and_pos projects conjunct at index"
        `Quick test_check_and_pos;
      Alcotest.test_case "and_pos rejects wrong-index projection"
        `Quick test_check_and_pos_rejects_wrong_index;
      Alcotest.test_case "reordering accepts permutation of premise"
        `Quick test_check_reordering;
      Alcotest.test_case "contraction collapses duplicate literals"
        `Quick test_check_contraction;
      Alcotest.test_case "not_and applies De Morgan"
        `Quick test_check_not_and;
      Alcotest.test_case "or unwraps singleton disjunction"
        `Quick test_check_or;
      Alcotest.test_case "symm flips equality sides"
        `Quick test_check_symm;
      Alcotest.test_case "subproof accepts minimal discharge close"
        `Quick test_check_subproof;
      Alcotest.test_case "subproof rejects nested unsealed body conclusion"
        `Quick test_check_subproof_rejects_nested_body_conclusion;
      Alcotest.test_case "verify rejects dotted assume without anchor"
        `Quick test_verify_rejects_dotted_assume_without_anchor;
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

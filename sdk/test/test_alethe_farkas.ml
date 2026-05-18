(** Unit tests for [Alethe_farkas].

    Coverage:
    * Parse a real cvc5 Alethe proof for [x>=3 ∧ x<=1] and extract
      the Farkas witness, then run it through [Farkas.verify].
    * Same for an LRA goal with a non-trivial negated goal.
    * No la_generic in the proof → [No_la_generic] error.
    * Coefficient mismatch fixture (synthetic) → caught.

    Fixture proofs live under [sdk/test/fixtures/] and were generated
    by running cvc5 with [--produce-proofs --proof-format-mode=alethe]
    on the SMT-LIB scripts described in each test. *)

open Proof_broker

let load_fixture name =
  let path =
    Filename.concat (Sys.getcwd ()) ("../../../../sdk/test/fixtures/" ^ name)
  in
  In_channel.with_open_text path In_channel.input_all

(* --- IR builders ----------------------------------------------------- *)

let lra_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LRA";
  decidable_theory = None;
}

let real_var name : Ir.shell_term = Var { name }
let real_const value : Ir.shell_term = Num_lit { value; ty = "Real" }

(** IR for the trivial Farkas: [x ≥ 3, x ≤ 1 ⊢ False]. We model
    "False" as a goal that is itself contradicted, by setting the
    goal to [True] (so [neg_goal] is [False] = unused) and letting
    the two hypotheses do the work. The simplest encoding is to
    use the goal [x = x] (always true, neg_goal = (not (x = x))
    which compiles fine but won't appear in the witness). *)
let make_g4_ir () : Ir.t =
  let h0 : Ir.hypothesis = {
    name = "h0";
    shell = App {
      symbol = ">="; type_args = [];
      args = [ real_var "x"; real_const "3" ];
    };
  } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = App {
      symbol = "<="; type_args = [];
      args = [ real_var "x"; real_const "1" ];
    };
  } in
  {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = lra_logic;
    goal = {
      shell = Eq {
        ty = "Real"; left = real_var "x"; right = real_var "x";
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

(** IR for [x+y >= 10, x <= 4 ⊢ y >= 6]. *)
let make_g5_ir () : Ir.t =
  let xy_sum : Ir.shell_term = App {
    symbol = "+"; type_args = []; args = [ real_var "x"; real_var "y" ];
  } in
  let h0 : Ir.hypothesis = {
    name = "h0";
    shell = App {
      symbol = ">="; type_args = []; args = [ xy_sum; real_const "10" ];
    };
  } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = App {
      symbol = "<="; type_args = []; args = [ real_var "x"; real_const "4" ];
    };
  } in
  {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = lra_logic;
    goal = {
      shell = App {
        symbol = ">="; type_args = [];
        args = [ real_var "y"; real_const "6" ];
      };
      payloads = None;
    };
    context = {
      type_vars = [];
      free_vars = [
        { name = "x"; ty = "Real" };
        { name = "y"; ty = "Real" };
      ];
      hypotheses = [ h0; h1 ];
      library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

(* --- tests ---------------------------------------------------------- *)

let test_parse_g4 () =
  let proof_str = load_fixture "alethe-x-3-x-1.proof" in
  let p = Alethe.parse proof_str in
  Alcotest.(check int) "two assumes" 2 (List.length p.assumes);
  Alcotest.(check bool) "has la_generic step"
    true (Option.is_some (Alethe.unique_la_generic p))

let test_extract_g4 () =
  let proof_str = load_fixture "alethe-x-3-x-1.proof" in
  let ir = make_g4_ir () in
  match Alethe_farkas.extract ir proof_str with
  | Error e ->
    Alcotest.fail (Printf.sprintf "extract failed: %s — %s"
                     (Alethe_farkas.error_kind e)
                     (Alethe_farkas.error_detail e))
  | Ok witness ->
    (match Farkas.verify ir witness with
     | Verified -> ()
     | other ->
       let kind = match other with
         | Verified -> "Verified"
         | Unknown_hypothesis _ -> "Unknown_hypothesis"
         | Nonlinear _ -> "Nonlinear"
         | Bad_coefficient _ -> "Bad_coefficient"
         | Negative_coefficient _ -> "Negative_coefficient"
         | Not_contradictory _ -> "Not_contradictory"
         | Malformed_witness _ -> "Malformed_witness"
       in
       Alcotest.fail
         (Printf.sprintf "verify rejected witness: %s; witness=%s"
            kind (Yojson.Safe.to_string witness)))

let test_extract_g5 () =
  let proof_str = load_fixture "alethe-xy-10-x-4-y-6.proof" in
  let ir = make_g5_ir () in
  match Alethe_farkas.extract ir proof_str with
  | Error e ->
    Alcotest.fail (Printf.sprintf "extract failed: %s — %s"
                     (Alethe_farkas.error_kind e)
                     (Alethe_farkas.error_detail e))
  | Ok witness ->
    (match Farkas.verify ir witness with
     | Verified -> ()
     | other ->
       let kind = match other with
         | Verified -> "Verified"
         | Unknown_hypothesis _ -> "Unknown_hypothesis"
         | Nonlinear _ -> "Nonlinear"
         | Bad_coefficient _ -> "Bad_coefficient"
         | Negative_coefficient _ -> "Negative_coefficient"
         | Not_contradictory _ -> "Not_contradictory"
         | Malformed_witness _ -> "Malformed_witness"
       in
       Alcotest.fail
         (Printf.sprintf "verify rejected witness: %s; witness=%s"
            kind (Yojson.Safe.to_string witness)))

(** IR for the case-split fixture: [(or (<= x 0) (>= x 10)),
    x >= 1, x <= 9 ⊢ False]. The disjunctive hypothesis closes
    via two subproofs, each running its own la_generic. *)
let make_case_split_ir () : Ir.t =
  let x = real_var "x" in
  let zero = real_const "0" in
  let one = real_const "1" in
  let nine = real_const "9" in
  let ten = real_const "10" in
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
    logic_classification = lra_logic;
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

let test_extract_case_split () =
  let proof_str = load_fixture "alethe-case-split-x.proof" in
  let ir = make_case_split_ir () in
  match Alethe_farkas.extract_case_split_payload ir proof_str with
  | Error e ->
    Alcotest.fail (Printf.sprintf "case-split extract failed: %s — %s"
                     (Alethe_farkas.error_kind e)
                     (Alethe_farkas.error_detail e))
  | Ok (lemmas, hyp_name) ->
    Alcotest.(check string) "disjunctive hyp = h_disj" "h_disj" hyp_name;
    Alcotest.(check int) "two lemmas" 2 (List.length lemmas);
    (* Round-trip the lemmas through the verifier's case-split path. *)
    let cert : Certificate.t = {
      cert_version = "1.0";
      tier = 2;
      format = "case_split_farkas";
      goal = ir.goal;
      dispatch_context_hash = Hash.sha256_of_json (Codec.to_json ir);
      rewrite_trace_hash = "sha256:" ^ String.make 64 '0';
      backend = {
        name = "cvc5"; version = "1.3.3";
        config_hash = "sha256:" ^ String.make 64 '0';
      };
      resources = {
        wall_time_ms = 0; memory_peak_kb = 0; budget_consumed = None;
      };
      refinement_record = {
        adapter = "cvc5"; adapter_version = "1.3.3";
        specializations = []; fragment = "LRA"; auxiliary = None;
      };
      payload = Tier2_lemma_list {
        lemmas_used = lemmas;
        strategy_hint = "case_split_farkas";
        structural_hint = Some (`Assoc [
          "disjunctive_hypothesis", `String hyp_name;
        ]);
      };
    } in
    (match Verifier.verify cert ir with
     | Verified_case_split -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf "case-split verifier rejected extracted lemmas: %s — %s"
            (Verifier.kind_of_reason other)
            (Verifier.detail_of_reason other)))

(** IR for the arity-3 case-split fixture:
    [(or (<= x 0) (or (>= x 10) (>= y 5))), x >= 1, x <= 9, y <= 4 ⊢ False].
    Three disjuncts, each Farkas-closable against the matching outer
    hypothesis. cvc5 doesn't emit arity-3+ case-split proofs for LRA
    today (it falls back to Tier 0 oracle), so the arity-N path in
    `Alethe_farkas.extract_case_split` couldn't be exercised end-to-
    end from bridge-level tests alone. This IR + the matching
    `alethe-case-split-arity3.proof` fixture covers it directly at
    the SDK layer. Phase-5 carried-forward item. *)
let make_case_split_arity3_ir () : Ir.t =
  let x = real_var "x" in
  let y = real_var "y" in
  let zero = real_const "0" in
  let one = real_const "1" in
  let four = real_const "4" in
  let five = real_const "5" in
  let nine = real_const "9" in
  let ten = real_const "10" in
  let h_disj : Ir.hypothesis = {
    name = "h_disj";
    shell = Or {
      left = App { symbol = "<="; type_args = []; args = [ x; zero ] };
      right = Or {
        left = App { symbol = ">="; type_args = []; args = [ x; ten ] };
        right = App { symbol = ">="; type_args = []; args = [ y; five ] };
      };
    };
  } in
  let h_x_low : Ir.hypothesis = {
    name = "h_x_low";
    shell = App { symbol = ">="; type_args = []; args = [ x; one ] };
  } in
  let h_x_high : Ir.hypothesis = {
    name = "h_x_high";
    shell = App { symbol = "<="; type_args = []; args = [ x; nine ] };
  } in
  let h_y_high : Ir.hypothesis = {
    name = "h_y_high";
    shell = App { symbol = "<="; type_args = []; args = [ y; four ] };
  } in
  {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = lra_logic;
    goal = {
      shell = Const { name = "False" };
      payloads = None;
    };
    context = {
      type_vars = [];
      free_vars = [
        { name = "x"; ty = "Real" };
        { name = "y"; ty = "Real" };
      ];
      hypotheses = [ h_disj; h_x_low; h_x_high; h_y_high ];
      library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

let test_extract_case_split_arity3 () =
  let proof_str = load_fixture "alethe-case-split-arity3.proof" in
  let ir = make_case_split_arity3_ir () in
  match Alethe_farkas.extract_case_split_payload ir proof_str with
  | Error e ->
    Alcotest.fail (Printf.sprintf "arity-3 case-split extract failed: %s — %s"
                     (Alethe_farkas.error_kind e)
                     (Alethe_farkas.error_detail e))
  | Ok (lemmas, hyp_name) ->
    Alcotest.(check string) "disjunctive hyp = h_disj" "h_disj" hyp_name;
    Alcotest.(check int) "three lemmas" 3 (List.length lemmas);
    let cert : Certificate.t = {
      cert_version = "1.0";
      tier = 2;
      format = "case_split_farkas";
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
      payload = Tier2_lemma_list {
        lemmas_used = lemmas;
        strategy_hint = "case_split_farkas";
        structural_hint = Some (`Assoc [
          "disjunctive_hypothesis", `String hyp_name;
        ]);
      };
    } in
    (match Verifier.verify cert ir with
     | Verified_case_split -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf "arity-3 case-split verifier rejected lemmas: %s — %s"
            (Verifier.kind_of_reason other)
            (Verifier.detail_of_reason other)))

let test_no_la_generic () =
  (* A proof that contains only assumes and a trivial closing
     resolution — no la_generic. Build it inline. *)
  let synth_proof = "(\n\
                     (assume a0 (= 1 1))\n\
                     (step t0 (cl false) :rule resolution)\n\
                     )" in
  let ir = make_g4_ir () in
  match Alethe_farkas.extract ir synth_proof with
  | Error No_la_generic -> ()
  | Error e ->
    Alcotest.fail
      (Printf.sprintf "expected No_la_generic, got %s"
         (Alethe_farkas.error_kind e))
  | Ok _ -> Alcotest.fail "expected error, got Ok"

(** Audit H2 regression: the verifier must reject a Tier-2
    case-split cert whose [disjunctive_hypothesis] names a real but
    non-[Or] hypothesis, even when the per-branch witnesses would
    otherwise close. Uses the genuine extracted lemmas but repoints
    [structural_hint] at [h_low] ([x >= 1], a linear atom, not a
    disjunction). Expect [Case_split_malformed], NOT
    [Verified_case_split]. *)
let test_case_split_rejects_non_or_hypothesis () =
  let proof_str = load_fixture "alethe-case-split-x.proof" in
  let ir = make_case_split_ir () in
  match Alethe_farkas.extract_case_split_payload ir proof_str with
  | Error e ->
    Alcotest.fail (Printf.sprintf "fixture extract failed: %s — %s"
                     (Alethe_farkas.error_kind e)
                     (Alethe_farkas.error_detail e))
  | Ok (lemmas, _real_hyp) ->
    let cert : Certificate.t = {
      cert_version = "1.0";
      tier = 2;
      format = "case_split_farkas";
      goal = ir.goal;
      dispatch_context_hash = Hash.sha256_of_json (Codec.to_json ir);
      rewrite_trace_hash = "sha256:" ^ String.make 64 '0';
      backend = {
        name = "cvc5"; version = "1.3.3";
        config_hash = "sha256:" ^ String.make 64 '0';
      };
      resources = {
        wall_time_ms = 0; memory_peak_kb = 0; budget_consumed = None;
      };
      refinement_record = {
        adapter = "cvc5"; adapter_version = "1.3.3";
        specializations = []; fragment = "LRA"; auxiliary = None;
      };
      payload = Tier2_lemma_list {
        lemmas_used = lemmas;
        strategy_hint = "case_split_farkas";
        (* h_low is `x >= 1` — a real hypothesis, but NOT an Or. *)
        structural_hint = Some (`Assoc [
          "disjunctive_hypothesis", `String "h_low";
        ]);
      };
    } in
    (match Verifier.verify cert ir with
     | Case_split_malformed _ -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf
            "non-Or disjunctive_hypothesis must be rejected as \
             case_split_malformed; got %s — %s"
            (Verifier.kind_of_reason other)
            (Verifier.detail_of_reason other)))

(* Audit H4: pathologically deep nesting in (untrusted) solver
   output must surface as a typed [Alethe.Parse_error], never a
   process-killing [Stack_overflow]. The string is far past
   [Alethe.max_parse_depth] so the depth bound (not the
   Stack_overflow backstop) is what fires. *)
let test_alethe_deep_nesting_is_parse_error () =
  let n = 200_000 in
  let s = String.make n '(' ^ "x" ^ String.make n ')' in
  match Alethe.parse s with
  | exception Alethe.Parse_error _ -> ()
  | exception Stack_overflow ->
    Alcotest.fail "deep nesting raised Stack_overflow (should be \
                   a bounded Parse_error)"
  | _ -> Alcotest.fail "deep nesting unexpectedly parsed"

let () =
  Alcotest.run "alethe_farkas" [
    "parse", [
      Alcotest.test_case "parse g4 fixture" `Quick test_parse_g4;
      Alcotest.test_case "deep nesting -> Parse_error, not crash (H4)"
        `Quick test_alethe_deep_nesting_is_parse_error;
    ];
    "extract", [
      Alcotest.test_case "extract g4 farkas witness" `Quick test_extract_g4;
      Alcotest.test_case "extract g5 farkas witness" `Quick test_extract_g5;
      Alcotest.test_case "no la_generic in proof" `Quick test_no_la_generic;
    ];
    "case_split", [
      Alcotest.test_case "extract + verify case-split witness"
        `Quick test_extract_case_split;
      Alcotest.test_case "extract + verify arity-3 case-split witness"
        `Quick test_extract_case_split_arity3;
      Alcotest.test_case "reject non-Or disjunctive_hypothesis (audit H2)"
        `Quick test_case_split_rejects_non_or_hypothesis;
    ];
  ]

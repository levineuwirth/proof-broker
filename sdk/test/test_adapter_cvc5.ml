(** End-to-end tests for [Adapter_cvc5].

    These tests spawn the cvc5 binary and require it to be on PATH.
    If cvc5 is not available, every test logs a skip and the suite
    exits 0 — same convention as the cvc4 tests. Coverage mirrors
    [test_adapter_cvc4]:
    * Provable LIA goal → [Cert _] addressing the IR by hash, with
      tier=0 and backend=cvc5.
    * Satisfiable goal → [Failed Sat_returned].
    * Unsupported IR shape (a quantifier) → [Failed
      (Unsupported_ir _)] (purely Smtlib-level, no cvc5 spawn).
    * Cert envelope-verifies through [Verifier.verify] as
      [Tier_check_deferred 0]. *)

open Proof_broker

let cvc5_available () : bool =
  Sys.command "which cvc5 > /dev/null 2>&1" = 0

let with_cvc5 f =
  if not (cvc5_available ()) then
    Printf.printf "[skip] cvc5 not on PATH\n"
  else f ()

let trivial_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LIA";
  decidable_theory = None;
}

let make_ir ?(free_vars = []) ?(hypotheses = []) (goal_shell : Ir.shell_term)
  : Ir.t = {
  ir_version = "1.0";
  source_system = { name = "test"; version = "0.0" };
  tier = "goal";
  logic_classification = trivial_logic;
  goal = { shell = goal_shell; payloads = None };
  context = { type_vars = []; free_vars; hypotheses; library_slice = None };
  type_metadata = [];
  definitional_metadata = [];
  library_provenance = [];
  user_directives = None;
}

(** IR: n + m = 10, 0 <= m, ⊢ n <= 10. *)
let example1_ir () =
  let n = Ir.Var { name = "n" } in
  let m = Ir.Var { name = "m" } in
  let ten = Ir.Num_lit { value = "10"; ty = "Int" } in
  let zero = Ir.Num_lit { value = "0"; ty = "Int" } in
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
    shell = App { symbol = "LE.le"; type_args = []; args = [ zero; m ] };
  } in
  make_ir
    ~free_vars:[ { name = "n"; ty = "Int" }; { name = "m"; ty = "Int" } ]
    ~hypotheses:[ h1; h3 ]
    (App { symbol = "LE.le"; type_args = []; args = [ n; ten ] })

let test_dispatch_unsat_mints_tier3_cert () =
  with_cvc5 @@ fun () ->
  let ir = example1_ir () in
  match Adapter_cvc5.dispatch ir with
  | Cert cert ->
    (* cvc5 closes example1's LIA shape via a chain of theory
       rewrites (LIA tightening + variable isolation + direction
       flip + double negation), all of which the Tier 3 hole/
       rare_rewrite checker recognizes via normalize_literal. The
       full proof verifies under the strict Tier 3 gate, so
       [Adapter_cvc5.dispatch] mints a Tier 3 alethe-2024 cert. *)
    Alcotest.(check int) "tier=3" 3 cert.tier;
    Alcotest.(check string) "format=alethe-2024" "alethe-2024" cert.format;
    Alcotest.(check string) "backend=cvc5" "cvc5" cert.backend.name;
    Alcotest.(check string) "backend.version pinned" Adapter_cvc5.version
      cert.backend.version;
    let dispatch_hash = Hash.sha256_of_json (Codec.to_json ir) in
    Alcotest.(check string) "dispatch_context_hash addresses ir"
      dispatch_hash cert.dispatch_context_hash;
    Alcotest.(check string) "fragment = LIA" "LIA"
      cert.refinement_record.fragment;
    Alcotest.(check string) "refinement_record adapter = cvc5" "cvc5"
      cert.refinement_record.adapter
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s: %s)"
         (Adapter.kind_of_failure f)
         (Adapter.detail_of_failure f))

let test_dispatch_sat_returns_failure () =
  with_cvc5 @@ fun () ->
  let n = Ir.Var { name = "n" } in
  let ten = Ir.Num_lit { value = "10"; ty = "Int" } in
  let ir = make_ir
    ~free_vars:[ { name = "n"; ty = "Int" } ]
    (App { symbol = "LE.le"; type_args = []; args = [ n; ten ] })
  in
  match Adapter_cvc5.dispatch ir with
  | Failed Sat_returned -> ()
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Sat_returned, got %s"
         (Adapter.kind_of_failure f))
  | Cert _ ->
    Alcotest.fail "expected Sat_returned, got Cert (goal is not provable!)"

let test_dispatch_unsupported_ir () =
  let ir = make_ir
    (Forall { var = "x"; ty = "Int"; body = Var { name = "x" } })
  in
  match Adapter_cvc5.dispatch ir with
  | Failed (Unsupported_ir { kind; _ }) ->
    Alcotest.(check string) "kind = unsupported_node"
      "unsupported_node" kind
  | other ->
    let label = match other with
      | Cert _ -> "Cert"
      | Failed f -> Adapter.kind_of_failure f
    in
    Alcotest.fail (Printf.sprintf "expected Unsupported_ir, got %s" label)

let test_minted_cert_passes_envelope_verifier () =
  with_cvc5 @@ fun () ->
  let ir = example1_ir () in
  match Adapter_cvc5.dispatch ir with
  | Cert cert ->
    (* The Tier 3 cert minted for example1 verifies end-to-end via
       the envelope verifier: [Tier3_alethe.verify] walks every
       step (la_generic, refl, trans, cong, resolution, false,
       equiv_pos2, hole, ...) and the strict mint-time gate
       guaranteed every rule check accepted at mint time. *)
    (match Verifier.verify cert ir with
     | Verified_tier3 -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf "expected Verified_tier3, got %s — %s"
            (Verifier.kind_of_reason other)
            (Verifier.detail_of_reason other)))
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s)"
         (Adapter.kind_of_failure f))

(** LRA IR exercising the Tier 1 Alethe→Farkas path: [x + y >= 10,
    x <= 4 ⊢ y >= 6]. cvc5 closes this via a single la_generic
    step with rational coefficients, which our extractor turns into
    a Farkas witness that [Farkas.verify] re-checks. *)
let lra_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LRA";
  decidable_theory = None;
}

let make_lra_ir ?(free_vars = []) ?(hypotheses = []) (goal_shell : Ir.shell_term)
  : Ir.t = {
  ir_version = "1.0";
  source_system = { name = "test"; version = "0.0" };
  tier = "goal";
  logic_classification = lra_logic;
  goal = { shell = goal_shell; payloads = None };
  context = { type_vars = []; free_vars; hypotheses; library_slice = None };
  type_metadata = [];
  definitional_metadata = [];
  library_provenance = [];
  user_directives = None;
}

let lra_farkas_ir () =
  let x : Ir.shell_term = Var { name = "x" } in
  let y : Ir.shell_term = Var { name = "y" } in
  let ten : Ir.shell_term = Num_lit { value = "10"; ty = "Real" } in
  let four : Ir.shell_term = Num_lit { value = "4"; ty = "Real" } in
  let six : Ir.shell_term = Num_lit { value = "6"; ty = "Real" } in
  let h0 : Ir.hypothesis = {
    name = "h0";
    shell = App {
      symbol = ">="; type_args = [];
      args = [
        App { symbol = "+"; type_args = []; args = [ x; y ] };
        ten;
      ];
    };
  } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = App { symbol = "<="; type_args = []; args = [ x; four ] };
  } in
  make_lra_ir
    ~free_vars:[
      { name = "x"; ty = "Real" };
      { name = "y"; ty = "Real" };
    ]
    ~hypotheses:[ h0; h1 ]
    (App { symbol = ">="; type_args = []; args = [ y; six ] })

let test_dispatch_lra_mints_farkas_cert () =
  with_cvc5 @@ fun () ->
  let ir = lra_farkas_ir () in
  match Adapter_cvc5.dispatch ir with
  | Cert cert ->
    Alcotest.(check int) "tier=1" 1 cert.tier;
    Alcotest.(check string) "format=farkas" "farkas" cert.format;
    (match cert.payload with
     | Tier1_witness { witness_kind = Farkas; witness_data; _ } ->
       (match Farkas.verify ir witness_data with
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
            (Printf.sprintf "extracted witness rejected by Farkas.verify: %s"
               kind))
     | _ -> Alcotest.fail "expected Tier1_witness payload")
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s: %s)"
         (Adapter.kind_of_failure f)
         (Adapter.detail_of_failure f))

(** LIA IR exercising the integer-tightening normalization in
    Alethe_farkas. cvc5 emits [la_generic] for [x + y >= 10, x <=
    4 ⊢ y >= 6] over Int, and uses tightened strict literals like
    [(< y 6)] for our loose [(>= y 6)] negated goal. The +1
    normalization in [Alethe_farkas.lia_normalize] folds these
    back to a loose form the IR-side compile recognizes. *)
let lia_farkas_ir () =
  let x : Ir.shell_term = Var { name = "x" } in
  let y : Ir.shell_term = Var { name = "y" } in
  let ten : Ir.shell_term = Num_lit { value = "10"; ty = "Int" } in
  let four : Ir.shell_term = Num_lit { value = "4"; ty = "Int" } in
  let six : Ir.shell_term = Num_lit { value = "6"; ty = "Int" } in
  let h0 : Ir.hypothesis = {
    name = "h0";
    shell = App {
      symbol = ">="; type_args = [];
      args = [
        App { symbol = "+"; type_args = []; args = [ x; y ] };
        ten;
      ];
    };
  } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = App { symbol = "<="; type_args = []; args = [ x; four ] };
  } in
  make_ir
    ~free_vars:[
      { name = "x"; ty = "Int" };
      { name = "y"; ty = "Int" };
    ]
    ~hypotheses:[ h0; h1 ]
    (App { symbol = ">="; type_args = []; args = [ y; six ] })

let test_dispatch_lia_mints_farkas_cert () =
  with_cvc5 @@ fun () ->
  let ir = lia_farkas_ir () in
  match Adapter_cvc5.dispatch ir with
  | Cert cert ->
    Alcotest.(check int) "tier=1" 1 cert.tier;
    Alcotest.(check string) "format=farkas" "farkas" cert.format;
    (match cert.payload with
     | Tier1_witness { witness_kind = Farkas; witness_data; _ } ->
       (match Farkas.verify ir witness_data with
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
            (Printf.sprintf "extracted LIA witness rejected by Farkas.verify: %s"
               kind))
     | _ -> Alcotest.fail "expected Tier1_witness payload")
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s: %s)"
         (Adapter.kind_of_failure f)
         (Adapter.detail_of_failure f))

(** Disjunctive-hypothesis IR exercising the Tier 2 case-split
    path: [(or (<= x 0) (>= x 10)), x >= 1, x <= 9 ⊢ False].
    cvc5 emits two la_generic steps, one per branch; we extract a
    case-split lemma list and the verifier re-checks both branches
    plus partition coverage. *)
let case_split_ir () : Ir.t =
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
  make_lra_ir
    ~free_vars:[ { name = "x"; ty = "Real" } ]
    ~hypotheses:[ h_disj; h_low; h_high ]
    (Const { name = "False" })

let test_dispatch_case_split_mints_tier2 () =
  with_cvc5 @@ fun () ->
  let ir = case_split_ir () in
  match Adapter_cvc5.dispatch ir with
  | Cert cert ->
    Alcotest.(check int) "tier=2" 2 cert.tier;
    Alcotest.(check string) "format=case_split_farkas"
      "case_split_farkas" cert.format;
    (match cert.payload with
     | Tier2_lemma_list { lemmas_used; strategy_hint; _ } ->
       Alcotest.(check string) "strategy_hint=case_split_farkas"
         "case_split_farkas" strategy_hint;
       Alcotest.(check int) "two lemmas" 2 (List.length lemmas_used)
     | _ -> Alcotest.fail "expected Tier2_lemma_list payload")
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s: %s)"
         (Adapter.kind_of_failure f)
         (Adapter.detail_of_failure f))

let test_case_split_cert_envelope_verifies () =
  with_cvc5 @@ fun () ->
  let ir = case_split_ir () in
  match Adapter_cvc5.dispatch ir with
  | Cert cert ->
    (match Verifier.verify cert ir with
     | Verified_case_split -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf "verifier rejected case-split cert: %s — %s"
            (Verifier.kind_of_reason other)
            (Verifier.detail_of_reason other)))
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s)"
         (Adapter.kind_of_failure f))

let test_lra_farkas_cert_envelope_verifies () =
  with_cvc5 @@ fun () ->
  let ir = lra_farkas_ir () in
  match Adapter_cvc5.dispatch ir with
  | Cert cert ->
    (match Verifier.verify cert ir with
     | Verified_farkas -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf "envelope verifier rejected Tier 1 cert: %s"
            (Verifier.kind_of_reason other)))
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s)"
         (Adapter.kind_of_failure f))

(** Confirm the strict "fail-closed" Tier 3 gate accepts a proof
    once every step's rule check passes. example1's proof uses
    [hole]/[rare_rewrite] for LIA tightening, double-negation,
    direction flip, and equation rearrangement — all of which our
    [normalize_literal]-based rewriter handles. Mint time =
    verify time, so the produced cert verifies as
    [Verified_tier3]. If a future cvc5 emits a hole shape outside
    our scope, the gate would fall through to Tier 1 (closer);
    that's the intended fail-closed direction. *)
let test_dispatch_tier3_gate_admits_real_proof () =
  with_cvc5 @@ fun () ->
  let ir = example1_ir () in
  match Adapter_cvc5.dispatch ir with
  | Cert cert ->
    Alcotest.(check int) "strict gate admits example1's proof at Tier 3"
      3 cert.tier;
    Alcotest.(check string) "format=alethe-2024 (Tier 3 path)"
      "alethe-2024" cert.format;
    (match Verifier.verify cert ir with
     | Verified_tier3 -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf "expected Verified_tier3, got %s — %s"
            (Verifier.kind_of_reason other)
            (Verifier.detail_of_reason other)))
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s)"
         (Adapter.kind_of_failure f))

let () =
  Alcotest.run "adapter_cvc5" [
    "dispatch", [
      Alcotest.test_case "unsat on Farkas-shape mints Tier 3 alethe cert"
        `Quick test_dispatch_unsat_mints_tier3_cert;
      Alcotest.test_case "sat returns Sat_returned"
        `Quick test_dispatch_sat_returns_failure;
      Alcotest.test_case "unsupported IR shape"
        `Quick test_dispatch_unsupported_ir;
      Alcotest.test_case "minted cert verifies through envelope"
        `Quick test_minted_cert_passes_envelope_verifier;
    ];
    "tier1", [
      Alcotest.test_case "LRA mints Tier 1 farkas cert"
        `Quick test_dispatch_lra_mints_farkas_cert;
      Alcotest.test_case "LIA mints Tier 1 farkas cert (with tightening)"
        `Quick test_dispatch_lia_mints_farkas_cert;
      Alcotest.test_case "Tier 1 cert envelope-verifies"
        `Quick test_lra_farkas_cert_envelope_verifies;
    ];
    "tier2", [
      Alcotest.test_case "case-split mints Tier 2 cert"
        `Quick test_dispatch_case_split_mints_tier2;
      Alcotest.test_case "Tier 2 case-split cert envelope-verifies"
        `Quick test_case_split_cert_envelope_verifies;
    ];
    "tier3", [
      Alcotest.test_case "strict gate admits example1's real cvc5 proof"
        `Quick test_dispatch_tier3_gate_admits_real_proof;
    ];
  ]

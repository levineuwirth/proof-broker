(** Regression test for [Z3_proof] / [Z3_farkas] keyed to a saved
    real z3 4.16.0 [(get-proof)] output.

    Why this exists: every other z3-proof test either constructs the
    proof string inline (see [test_z3_proof.ml]) or spawns the
    locally installed z3 (see [test_adapter_z3.ml]). Inline strings
    silently bit-rot if z3 changes its proof format; a live spawn
    only exercises whatever version is on PATH right now. This test
    pins the parser to a verbatim capture from z3 4.16.0 so that any
    future format drift surfaces as a deterministic test failure
    rather than a silent extraction regression.

    Coverage:
    * [Z3_proof.extract_proof_term] + [find_farkas_clause] on the
      saved fixture: coefficients [1; 1], two literals, the literal
      S-expressions render to exactly the strings z3 4.16.0 emits
      ([(<= x 3.0)] and [(>= x 5.0)]).
    * [Z3_farkas.extract] against a 2-hyp LRA IR (x >= 5, x <= 3 ⊢
      False) succeeds and produces a witness JSON with two
      hypothesis/coefficient entries. *)

open Proof_broker

(** Path resolution mirrors [test_round_trip] / [test_tier3_alethe]:
    dune runtest invokes us from sdk/_build/default/test/, so the
    repo's [sdk/test/fixtures/] is four levels up. The dune file
    does not declare the fixture as a dep; it lives outside the
    sdk/ workspace's source-copy boundary in the same way the
    Alethe fixtures do. *)
let load_fixture name =
  let path =
    Filename.concat (Sys.getcwd ()) ("../../../../sdk/test/fixtures/" ^ name)
  in
  In_channel.with_open_text path In_channel.input_all

let rat (n : int) (d : int) : Linear_arith.rational =
  { num = Z.of_int n; den = Z.of_int d }

let rat_eq (a : Linear_arith.rational) (b : Linear_arith.rational) : bool =
  Z.equal a.num b.num && Z.equal a.den b.den

(* --- Z3_proof on the saved fixture ----------------------------------- *)

let test_extract_and_find_farkas_on_fixture () =
  let envelope = load_fixture "z3-lra-two-hyp-farkas.proof" in
  let term = match Z3_proof.extract_proof_term envelope with
    | Some t -> t
    | None -> Alcotest.fail "fixture envelope did not parse"
  in
  match Z3_proof.find_farkas_clause term with
  | None ->
    Alcotest.fail "expected a Farkas clause in the saved z3 4.16.0 proof"
  | Some { coefficients; literals } ->
    Alcotest.(check int) "two coefficients" 2 (List.length coefficients);
    Alcotest.(check int) "two literals" 2 (List.length literals);
    Alcotest.(check bool) "first coef = 1" true
      (rat_eq (rat 1 1) (List.nth coefficients 0));
    Alcotest.(check bool) "second coef = 1" true
      (rat_eq (rat 1 1) (List.nth coefficients 1));
    (* Literal order in z3 4.16.0's emitted clause for this goal is
       (<= x 3.0) then (>= x 5.0) — matches the order the
       hypotheses appear inside the let-bindings. If z3's literal
       ordering ever flips, this assertion is the canary. *)
    Alcotest.(check string) "first literal renders to (<= x 3.0)"
      "(<= x 3.0)" (Z3_proof.Sexp.to_string (List.nth literals 0));
    Alcotest.(check string) "second literal renders to (>= x 5.0)"
      "(>= x 5.0)" (Z3_proof.Sexp.to_string (List.nth literals 1))

(* --- Z3_farkas.extract against a 2-hyp LRA IR + the fixture --------- *)

let lra_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LRA";
  decidable_theory = None;
}

(** IR for [x >= 5, x <= 3 ⊢ False]. Real-typed integer-form
    literals — same shape as
    [test_adapter_z3.test_dispatch_lra_two_hyp_uses_native_extraction]
    so the fixture's emitted literal atoms ([(<= x 3.0)] /
    [(>= x 5.0)]) align cleanly to these hypotheses under
    [Alethe_farkas.match_one]'s positive-scale matching. *)
let two_hyp_lra_ir () : Ir.t =
  let x : Ir.shell_term = Var { name = "x" } in
  let three : Ir.shell_term = Num_lit { value = "3"; ty = "Real" } in
  let five : Ir.shell_term = Num_lit { value = "5"; ty = "Real" } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = App { symbol = ">="; type_args = []; args = [ x; five ] };
  } in
  let h2 : Ir.hypothesis = {
    name = "h2";
    shell = App { symbol = "<="; type_args = []; args = [ x; three ] };
  } in
  {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = lra_logic;
    goal = { shell = Const { name = "False" }; payloads = None };
    context = {
      type_vars = [];
      free_vars = [ { name = "x"; ty = "Real" } ];
      hypotheses = [ h1; h2 ];
      library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

let test_z3_farkas_extract_on_fixture () =
  let envelope = load_fixture "z3-lra-two-hyp-farkas.proof" in
  let ir = two_hyp_lra_ir () in
  match Z3_farkas.extract ir envelope with
  | Error e ->
    Alcotest.fail
      (Printf.sprintf "expected Ok, got Error(%s: %s)"
         (Z3_farkas.error_kind e) (Z3_farkas.error_detail e))
  | Ok witness ->
    (* witness is [{coefficients: [{hypothesis, coefficient}, ...]}].
       Both hypotheses appear with rational-string coefficients —
       we only assert the entry count and shape; the hypothesis
       names are what align_extract recovered, which depends on
       match_one's order of evaluation, so we don't pin specific
       names beyond "two distinct entries". *)
    let entries = match witness with
      | `Assoc fields ->
        (match List.assoc_opt "coefficients" fields with
         | Some (`List items) -> items
         | _ -> Alcotest.fail "witness JSON missing coefficients list")
      | _ -> Alcotest.fail "witness JSON not an object"
    in
    Alcotest.(check int) "witness has two coefficient entries"
      2 (List.length entries);
    List.iter (fun entry ->
      match entry with
      | `Assoc fields ->
        Alcotest.(check bool) "entry has 'hypothesis' field" true
          (List.mem_assoc "hypothesis" fields);
        Alcotest.(check bool) "entry has 'coefficient' field" true
          (List.mem_assoc "coefficient" fields)
      | _ -> Alcotest.fail "witness entry not an object") entries

let () =
  Alcotest.run "z3_proof_fixture" [
    "z3_proof", [
      Alcotest.test_case "extract_proof_term + find_farkas_clause on saved 4.16.0 fixture"
        `Quick test_extract_and_find_farkas_on_fixture;
    ];
    "z3_farkas", [
      Alcotest.test_case "extract on saved 4.16.0 fixture against 2-hyp LRA IR"
        `Quick test_z3_farkas_extract_on_fixture;
    ];
  ]

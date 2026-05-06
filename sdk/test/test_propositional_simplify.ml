(** Unit tests for the propositional_simplify pass.

    Tests are organized as small synthetic IR documents constructed
    with the minimum top-level scaffolding required by the schema.
    The interesting variation is in [goal.shell] / [hypothesis.shell];
    everything else stays fixed across cases.

    Coverage:
    * Each rule fires on its minimal trigger.
    * No-op (no rewritable structure) yields [outcome = No_op] and
      empty inversion list.
    * Idempotence: running the pass twice gives the same result as
      running it once.
    * Cascade: rules that open up further opportunities are taken
      to fixpoint inside one invocation.
    * Hypothesis simplification: rules fire under hypothesis sites
      with the right [site] tag.
    * Hash discipline: [before_hash != after_hash] iff at least one
      rule fired. *)

open Proof_broker

(* --- IR scaffolding --------------------------------------------------- *)

let trivial_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "FOL";
  decidable_theory = None;
}

let trivial_source : Ir.source_system = { name = "test"; version = "0.0" }

(** Build a minimal IR with a given goal shell and (optionally) a list
    of hypothesis shells. *)
let make_ir ?(hypotheses = []) (shell : Ir.shell_term) : Ir.t =
  let hyps =
    List.mapi
      (fun i s -> ({ name = Printf.sprintf "h%d" i; shell = s } : Ir.hypothesis))
      hypotheses
  in
  {
    ir_version = "1.0";
    source_system = trivial_source;
    tier = "goal";
    logic_classification = trivial_logic;
    goal = { shell; payloads = None };
    context = {
      type_vars = [];
      free_vars = [];
      hypotheses = hyps;
      library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

(* --- Term builders ---------------------------------------------------- *)

let v name : Ir.shell_term = Var { name }
let c_true : Ir.shell_term = Const { name = "True" }
let c_false : Ir.shell_term = Const { name = "False" }
let mk_and l r : Ir.shell_term = And { left = l; right = r }
let mk_or l r : Ir.shell_term = Or { left = l; right = r }
let mk_not p : Ir.shell_term = Not { operand = p }
let mk_implies a c : Ir.shell_term = Implies { antecedent = a; consequent = c }

(* --- Trace inspection ------------------------------------------------- *)

let extract_rules (entry : Trace.entry) : (string * string) list =
  match entry.inversion_data with
  | Some (`Assoc pairs) ->
    (match List.assoc_opt "simplifications" pairs with
     | Some (`List xs) ->
       List.map
         (fun j ->
           let p = match j with `Assoc p -> p | _ -> failwith "bad simp" in
           let r = match List.assoc "rule" p with `String s -> s | _ -> failwith "bad rule" in
           let s = match List.assoc "site" p with `String s -> s | _ -> failwith "bad site" in
           (r, s))
         xs
     | _ -> [])
  | _ -> []

let rule_names entry = List.map fst (extract_rules entry)

(* --- Tests ------------------------------------------------------------ *)

let test_and_true_left () =
  let result = Propositional_simplify.run (make_ir (mk_and c_true (v "p"))) in
  Alcotest.(check (list string)) "single rule applied"
    [ "And_True_left" ] (rule_names result.trace);
  Alcotest.(check bool) "outcome=applied"
    true (result.trace.outcome = Some Applied);
  Alcotest.(check bool) "goal collapsed to p"
    true (result.ir.goal.shell = v "p")

let test_and_true_right () =
  let result = Propositional_simplify.run (make_ir (mk_and (v "p") c_true)) in
  Alcotest.(check (list string)) "single rule applied"
    [ "And_True_right" ] (rule_names result.trace)

let test_and_false_left () =
  let result = Propositional_simplify.run (make_ir (mk_and c_false (v "p"))) in
  Alcotest.(check (list string)) "And_False_left fires"
    [ "And_False_left" ] (rule_names result.trace);
  Alcotest.(check bool) "goal is False"
    true (result.ir.goal.shell = c_false)

let test_or_true_short_circuits () =
  let result = Propositional_simplify.run (make_ir (mk_or (v "p") c_true)) in
  Alcotest.(check (list string)) "Or_True_right fires"
    [ "Or_True_right" ] (rule_names result.trace);
  Alcotest.(check bool) "goal is True"
    true (result.ir.goal.shell = c_true)

let test_not_not () =
  let result = Propositional_simplify.run (make_ir (mk_not (mk_not (v "p")))) in
  Alcotest.(check (list string)) "Not_Not strips"
    [ "Not_Not" ] (rule_names result.trace);
  Alcotest.(check bool) "goal is p"
    true (result.ir.goal.shell = v "p")

let test_not_true () =
  let result = Propositional_simplify.run (make_ir (mk_not c_true)) in
  Alcotest.(check (list string)) "Not_True fires"
    [ "Not_True" ] (rule_names result.trace);
  Alcotest.(check bool) "goal is False"
    true (result.ir.goal.shell = c_false)

let test_implies_true_left () =
  let result =
    Propositional_simplify.run (make_ir (mk_implies c_true (v "q")))
  in
  Alcotest.(check (list string)) "Implies_True_left fires"
    [ "Implies_True_left" ] (rule_names result.trace);
  Alcotest.(check bool) "goal is q"
    true (result.ir.goal.shell = v "q")

let test_no_op () =
  (* p ∧ q has no rewritable structure. *)
  let ir = make_ir (mk_and (v "p") (v "q")) in
  let result = Propositional_simplify.run ir in
  Alcotest.(check (list string)) "no rules applied"
    [] (rule_names result.trace);
  Alcotest.(check bool) "outcome=No_op"
    true (result.trace.outcome = Some No_op);
  Alcotest.(check bool) "before_hash = after_hash"
    true (result.trace.before_hash = result.trace.after_hash);
  Alcotest.(check bool) "goal is unchanged"
    true (result.ir.goal.shell = mk_and (v "p") (v "q"))

let test_idempotence () =
  let ir = make_ir (mk_and c_true (mk_or (v "p") c_false)) in
  let r1 = Propositional_simplify.run ir in
  let r2 = Propositional_simplify.run r1.ir in
  Alcotest.(check (list string)) "second run is no-op"
    [] (rule_names r2.trace);
  Alcotest.(check bool) "second run preserves IR hash"
    true (r1.trace.after_hash = r2.trace.after_hash)

let test_cascade () =
  (* (True ∧ True) ∧ p — first iteration simplifies the inner And to
     True, second iteration simplifies the outer And. Both should land
     in one [run] call. *)
  let ir = make_ir (mk_and (mk_and c_true c_true) (v "p")) in
  let result = Propositional_simplify.run ir in
  Alcotest.(check bool) "goal is p after fixpoint"
    true (result.ir.goal.shell = v "p");
  Alcotest.(check int) "two rules fired"
    2 (List.length (rule_names result.trace))

let test_hypothesis_site () =
  let ir = make_ir
             ~hypotheses:[ mk_and c_true (v "h0body"); v "h1body" ]
             (v "g") in
  let result = Propositional_simplify.run ir in
  let rules = extract_rules result.trace in
  Alcotest.(check (list string)) "site is hypothesis[0]"
    [ "hypothesis[0]" ] (List.map snd rules);
  Alcotest.(check (list string)) "rule is And_True_left"
    [ "And_True_left" ] (List.map fst rules)

let test_hash_changes_iff_rewrites () =
  let with_rewrites = Propositional_simplify.run (make_ir (mk_and c_true (v "p"))) in
  Alcotest.(check bool) "hash differs when rules fired"
    true (with_rewrites.trace.before_hash <> with_rewrites.trace.after_hash);
  let without = Propositional_simplify.run (make_ir (v "p")) in
  Alcotest.(check bool) "hash equal when no rules fired"
    true (without.trace.before_hash = without.trace.after_hash)

let extract_indices (entry : Trace.entry) : int list =
  match entry.inversion_data with
  | Some (`Assoc pairs) ->
    (match List.assoc_opt "simplifications" pairs with
     | Some (`List xs) ->
       List.map
         (fun j ->
           let p = match j with `Assoc p -> p | _ -> failwith "bad simp" in
           match List.assoc_opt "index" p with
           | Some (`Int i) -> i
           | _ -> failwith "missing index")
         xs
     | _ -> [])
  | _ -> []

let test_inversion_records_indexed () =
  (* Cascade fires two rules; both must have distinct indices 0 and 1. *)
  let ir = make_ir (mk_and (mk_and c_true c_true) (v "p")) in
  let result = Propositional_simplify.run ir in
  Alcotest.(check (list int)) "indices are dense [0; 1]"
    [ 0; 1 ] (extract_indices result.trace)

let test_pass_metadata () =
  let result = Propositional_simplify.run (make_ir (v "p")) in
  Alcotest.(check string) "pass name"
    "propositional_simplification" result.trace.pass;
  Alcotest.(check string) "version"
    "1.0" result.trace.version

let () =
  Alcotest.run "propositional_simplify" [
    "rules", [
      Alcotest.test_case "And_True_left" `Quick test_and_true_left;
      Alcotest.test_case "And_True_right" `Quick test_and_true_right;
      Alcotest.test_case "And_False_left" `Quick test_and_false_left;
      Alcotest.test_case "Or_True_right" `Quick test_or_true_short_circuits;
      Alcotest.test_case "Not_Not" `Quick test_not_not;
      Alcotest.test_case "Not_True" `Quick test_not_true;
      Alcotest.test_case "Implies_True_left" `Quick test_implies_true_left;
    ];
    "outcome", [
      Alcotest.test_case "no_op outcome on inert goal" `Quick test_no_op;
      Alcotest.test_case "idempotence" `Quick test_idempotence;
      Alcotest.test_case "fixpoint cascades in one run" `Quick test_cascade;
    ];
    "trace_shape", [
      Alcotest.test_case "hypothesis site tag" `Quick test_hypothesis_site;
      Alcotest.test_case "hash discipline" `Quick test_hash_changes_iff_rewrites;
      Alcotest.test_case "pass metadata" `Quick test_pass_metadata;
      Alcotest.test_case "inversion records carry dense indices"
        `Quick test_inversion_records_indexed;
    ];
  ]

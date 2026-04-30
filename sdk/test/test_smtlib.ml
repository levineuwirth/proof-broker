(** Unit tests for [Smtlib].

    Coverage:
    * Term-level snapshots: [Var], [NumLit] (positive/negative
      literal), arithmetic [App] forms, comparison forms, boolean
      connectives, [Const True/False], [Eq] at [Bool] vs [Int].
    * Script assembly: [(set-logic ...)] picks [QF_LIA] for Int-only,
      [QF_LRA] when a [Real] free var is present.
    * Free vars become [(declare-const name sort)] with the right
      sort.
    * Hypotheses become [(assert ...)] and the goal becomes
      [(assert (not ...))].
    * Errors: quantifier rejected, opaque rejected, unsupported
      symbol rejected.
    * Specialization side-channel: [HAdd.hAdd]/[LE.le] are recorded;
      primitive symbols are also recorded with their canonical
      source name. *)

open Proof_broker

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

let emit_term_ok t =
  let specs = ref [] in
  match Smtlib.emit_term ~specs t with
  | Ok s -> s
  | Error e ->
    Alcotest.fail
      ("Smtlib.emit_term failed: " ^ Smtlib.detail_of_error e)

(* --- term emission --------------------------------------------------- *)

let test_emit_var () =
  Alcotest.(check string) "Var n → n"
    "n" (emit_term_ok (Var { name = "n" }))

let test_emit_num_lit_pos () =
  Alcotest.(check string) "NumLit 10 → 10"
    "10" (emit_term_ok (Num_lit { value = "10"; ty = "Int" }))

let test_emit_num_lit_neg () =
  Alcotest.(check string) "NumLit -3 → (- 3)"
    "(- 3)" (emit_term_ok (Num_lit { value = "-3"; ty = "Int" }))

let test_emit_add () =
  let t = Ir.App {
    symbol = "Int.add"; type_args = [];
    args = [ Var { name = "n" }; Num_lit { value = "5"; ty = "Int" } ];
  } in
  Alcotest.(check string) "(+ n 5)" "(+ n 5)" (emit_term_ok t)

let test_emit_le () =
  let t = Ir.App {
    symbol = "LE.le"; type_args = [];
    args = [ Var { name = "n" }; Num_lit { value = "10"; ty = "Int" } ];
  } in
  Alcotest.(check string) "(<= n 10)" "(<= n 10)" (emit_term_ok t)

let test_emit_eq () =
  let t = Ir.Eq {
    ty = "Int";
    left = Var { name = "n" };
    right = Num_lit { value = "10"; ty = "Int" };
  } in
  Alcotest.(check string) "(= n 10)" "(= n 10)" (emit_term_ok t)

let test_emit_bool_connectives () =
  let p = Ir.Var { name = "p" } in
  let q = Ir.Var { name = "q" } in
  Alcotest.(check string) "and" "(and p q)"
    (emit_term_ok (And { left = p; right = q }));
  Alcotest.(check string) "or" "(or p q)"
    (emit_term_ok (Or { left = p; right = q }));
  Alcotest.(check string) "not" "(not p)"
    (emit_term_ok (Not { operand = p }));
  Alcotest.(check string) "implies → =>" "(=> p q)"
    (emit_term_ok (Implies { antecedent = p; consequent = q }));
  Alcotest.(check string) "true" "true"
    (emit_term_ok (Const { name = "True" }));
  Alcotest.(check string) "false" "false"
    (emit_term_ok (Const { name = "False" }))

let test_emit_neg () =
  let t = Ir.App {
    symbol = "Neg.neg"; type_args = [];
    args = [ Var { name = "n" } ];
  } in
  Alcotest.(check string) "(- n)" "(- n)" (emit_term_ok t)

(* --- error paths ----------------------------------------------------- *)

let test_emit_quantifier_rejected () =
  let specs = ref [] in
  let t = Ir.Forall {
    var = "n"; ty = "Int"; body = Var { name = "n" };
  } in
  match Smtlib.emit_term ~specs t with
  | Error (Unsupported_node { node = "Forall"; _ }) -> ()
  | _ -> Alcotest.fail "expected Unsupported_node Forall"

let test_emit_unknown_symbol_rejected () =
  let specs = ref [] in
  let t = Ir.App {
    symbol = "Real.exp"; type_args = [];
    args = [ Var { name = "x" } ];
  } in
  match Smtlib.emit_term ~specs t with
  | Error (Unsupported_symbol { symbol = "Real.exp"; _ }) -> ()
  | _ -> Alcotest.fail "expected Unsupported_symbol"

let test_emit_opaque_rejected () =
  let specs = ref [] in
  match Smtlib.emit_term ~specs
          (Opaque { payload_id = "p" }) with
  | Error (Unsupported_node { node = "Opaque"; _ }) -> ()
  | _ -> Alcotest.fail "expected Unsupported_node Opaque"

(* --- specialization side-channel ------------------------------------- *)

let test_specs_recorded () =
  let specs = ref [] in
  let t = Ir.App {
    symbol = "HAdd.hAdd"; type_args = [];
    args = [ Var { name = "n" }; Num_lit { value = "5"; ty = "Int" } ];
  } in
  ignore (Smtlib.emit_term ~specs t);
  Alcotest.(check int) "1 specialization recorded" 1 (List.length !specs);
  let s = List.hd !specs in
  Alcotest.(check string) "source = HAdd.hAdd" "HAdd.hAdd" s.source;
  Alcotest.(check string) "target = +" "+" s.target

let test_specs_dedup () =
  let specs = ref [] in
  let n_plus_m = Ir.App {
    symbol = "HAdd.hAdd"; type_args = [];
    args = [ Var { name = "n" }; Var { name = "m" } ];
  } in
  let nested = Ir.App {
    symbol = "HAdd.hAdd"; type_args = [];
    args = [ n_plus_m; Var { name = "k" } ];
  } in
  ignore (Smtlib.emit_term ~specs nested);
  Alcotest.(check int) "deduped to 1 entry" 1 (List.length !specs)

(* --- script assembly ------------------------------------------------- *)

let test_emit_logic_lia () =
  let ir = make_ir
    ~free_vars:[ { name = "n"; ty = "Int" } ]
    (Ir.App {
      symbol = "LE.le"; type_args = [];
      args = [ Var { name = "n" }; Num_lit { value = "10"; ty = "Int" } ];
    })
  in
  match Smtlib.emit ir with
  | Ok script ->
    Alcotest.(check string) "logic = QF_LIA" "QF_LIA" script.logic;
    Alcotest.(check bool) "body opens with (set-logic QF_LIA)" true
      (String.length script.body > 20
       && String.sub script.body 0 20 = "(set-logic QF_LIA)\n(")
  | Error e ->
    Alcotest.fail ("emit failed: " ^ Smtlib.detail_of_error e)

let test_emit_logic_lra () =
  let ir = make_ir
    ~free_vars:[ { name = "x"; ty = "Real" } ]
    (Ir.App {
      symbol = "LE.le"; type_args = [];
      args = [ Var { name = "x" }; Num_lit { value = "1"; ty = "Real" } ];
    })
  in
  match Smtlib.emit ir with
  | Ok script ->
    Alcotest.(check string) "logic = QF_LRA" "QF_LRA" script.logic
  | Error e ->
    Alcotest.fail ("emit failed: " ^ Smtlib.detail_of_error e)

let test_emit_full_script () =
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
  let ir = make_ir
    ~free_vars:[ { name = "n"; ty = "Int" }; { name = "m"; ty = "Int" } ]
    ~hypotheses:[ h1; h3 ]
    (App { symbol = "LE.le"; type_args = []; args = [ n; ten ] })
  in
  match Smtlib.emit ir with
  | Ok script ->
    let expected =
      "(set-logic QF_LIA)\n\
       (declare-const n Int)\n\
       (declare-const m Int)\n\
       (assert (= (+ n m) 10))\n\
       (assert (<= 0 m))\n\
       (assert (not (<= n 10)))\n"
    in
    Alcotest.(check string) "full script matches" expected script.body
  | Error e ->
    Alcotest.fail ("emit failed: " ^ Smtlib.detail_of_error e)

let test_emit_unsupported_type_rejected () =
  let ir = make_ir
    ~free_vars:[ { name = "x"; ty = "alpha" } ]
    (Var { name = "x" })
  in
  match Smtlib.emit ir with
  | Error (Unsupported_type { ty = "alpha"; _ }) -> ()
  | _ -> Alcotest.fail "expected Unsupported_type alpha"

let () =
  Alcotest.run "smtlib" [
    "term emission", [
      Alcotest.test_case "Var" `Quick test_emit_var;
      Alcotest.test_case "NumLit positive" `Quick test_emit_num_lit_pos;
      Alcotest.test_case "NumLit negative" `Quick test_emit_num_lit_neg;
      Alcotest.test_case "add" `Quick test_emit_add;
      Alcotest.test_case "<=" `Quick test_emit_le;
      Alcotest.test_case "= (Int)" `Quick test_emit_eq;
      Alcotest.test_case "bool connectives" `Quick test_emit_bool_connectives;
      Alcotest.test_case "Neg.neg" `Quick test_emit_neg;
    ];
    "errors", [
      Alcotest.test_case "Forall rejected" `Quick test_emit_quantifier_rejected;
      Alcotest.test_case "unknown symbol rejected" `Quick test_emit_unknown_symbol_rejected;
      Alcotest.test_case "Opaque rejected" `Quick test_emit_opaque_rejected;
      Alcotest.test_case "unsupported type rejected" `Quick test_emit_unsupported_type_rejected;
    ];
    "specialization side-channel", [
      Alcotest.test_case "HAdd.hAdd recorded" `Quick test_specs_recorded;
      Alcotest.test_case "deduped" `Quick test_specs_dedup;
    ];
    "script", [
      Alcotest.test_case "QF_LIA logic" `Quick test_emit_logic_lia;
      Alcotest.test_case "QF_LRA logic" `Quick test_emit_logic_lra;
      Alcotest.test_case "full script" `Quick test_emit_full_script;
    ];
  ]

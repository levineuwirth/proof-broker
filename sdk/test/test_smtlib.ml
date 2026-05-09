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

let test_emit_num_lit_big_int () =
  let big = "123456789012345678901234567890" in
  Alcotest.(check string) "big positive integer round-trips"
    big (emit_term_ok (Num_lit { value = big; ty = "Int" }));
  Alcotest.(check string) "big negative integer wraps in (- N)"
    (Printf.sprintf "(- %s)" big)
    (emit_term_ok (Num_lit { value = "-" ^ big; ty = "Int" }))

let test_emit_num_lit_real_rational () =
  Alcotest.(check string) "Real 3/4 → (/ 3 4)"
    "(/ 3 4)" (emit_term_ok (Num_lit { value = "3/4"; ty = "Real" }));
  Alcotest.(check string) "Real -3/4 → (- (/ 3 4))"
    "(- (/ 3 4))" (emit_term_ok (Num_lit { value = "-3/4"; ty = "Real" }))

let test_emit_num_lit_real_decimal () =
  Alcotest.(check string) "Real 0.5 verbatim"
    "0.5" (emit_term_ok (Num_lit { value = "0.5"; ty = "Real" }));
  Alcotest.(check string) "Real -1.25 → (- 1.25)"
    "(- 1.25)" (emit_term_ok (Num_lit { value = "-1.25"; ty = "Real" }))

let test_emit_num_lit_int_with_slash_rejected () =
  let specs = ref [] in
  match Smtlib.emit_term ~specs
          (Num_lit { value = "3/4"; ty = "Int" }) with
  | Error (Bad_literal { value = "3/4"; ty = "Int" }) -> ()
  | _ -> Alcotest.fail "expected Bad_literal for Int 3/4"

let test_emit_num_lit_int_with_dot_rejected () =
  let specs = ref [] in
  match Smtlib.emit_term ~specs
          (Num_lit { value = "1.5"; ty = "Int" }) with
  | Error (Bad_literal { value = "1.5"; ty = "Int" }) -> ()
  | _ -> Alcotest.fail "expected Bad_literal for Int 1.5"

let test_emit_num_lit_exponent_rejected () =
  let specs = ref [] in
  match Smtlib.emit_term ~specs
          (Num_lit { value = "1e6"; ty = "Real" }) with
  | Error (Bad_literal { value = "1e6"; ty = "Real" }) -> ()
  | _ -> Alcotest.fail "expected Bad_literal for exponent literal"

let test_emit_num_lit_garbage_rejected () =
  let specs = ref [] in
  match Smtlib.emit_term ~specs
          (Num_lit { value = "abc"; ty = "Int" }) with
  | Error (Bad_literal { value = "abc"; ty = "Int" }) -> ()
  | _ -> Alcotest.fail "expected Bad_literal for non-numeric"

(* --- identifier quoting --------------------------------------------- *)

let test_emit_var_simple_unquoted () =
  Alcotest.(check string) "simple symbol unquoted"
    "n.0" (emit_term_ok (Var { name = "n.0" }));
  Alcotest.(check string) "dotted simple symbol unquoted"
    "Nat.add" (emit_term_ok (Var { name = "Nat.add" }))

let test_emit_var_with_space_rejected () =
  let specs = ref [] in
  match Smtlib.emit_term ~specs (Var { name = "user input" }) with
  | Error (Bad_identifier { name = "user input"; _ }) -> ()
  | _ -> Alcotest.fail "expected Bad_identifier for name containing space"

let test_emit_var_starting_with_digit_rejected () =
  let specs = ref [] in
  match Smtlib.emit_term ~specs (Var { name = "3foo" }) with
  | Error (Bad_identifier { name = "3foo"; _ }) -> ()
  | _ -> Alcotest.fail "expected Bad_identifier for name with leading digit"

let test_emit_var_reserved_word_rejected () =
  let specs = ref [] in
  (match Smtlib.emit_term ~specs (Var { name = "let" }) with
   | Error (Bad_identifier { name = "let"; _ }) -> ()
   | _ -> Alcotest.fail "expected Bad_identifier for reserved word 'let'");
  (match Smtlib.emit_term ~specs (Var { name = "Real" }) with
   | Error (Bad_identifier { name = "Real"; _ }) -> ()
   | _ -> Alcotest.fail "expected Bad_identifier for reserved word 'Real'")

let test_emit_var_pipe_rejected () =
  let specs = ref [] in
  match Smtlib.emit_term ~specs (Var { name = "bad|name" }) with
  | Error (Bad_identifier { name = "bad|name"; _ }) -> ()
  | _ -> Alcotest.fail "expected Bad_identifier for name containing |"

let test_emit_declare_const_rejects_non_simple () =
  let ir = make_ir
    ~free_vars:[ { name = "user input"; ty = "Int" } ]
    ~hypotheses:[]
    (Var { name = "user input" })
  in
  match Smtlib.emit ir with
  | Error (Bad_identifier _) -> ()
  | _ ->
    Alcotest.fail
      "expected Bad_identifier when free var name is not a simple symbol"

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

let test_emit_logic_lra_from_real_literal_only () =
  (* Closed Real-arithmetic goal: no free vars at all, but a Real
     numeric literal. pick_logic must scan term types and select
     QF_LRA — the previous free-var-only rule would have emitted
     QF_LIA and either trip an ill-sorted reject or quietly run
     the goal under integer semantics. *)
  let half = Ir.Num_lit { value = "1/2"; ty = "Real" } in
  let one = Ir.Num_lit { value = "1"; ty = "Real" } in
  let ir = make_ir
    ~free_vars:[]
    (Ir.App {
      symbol = "LE.le"; type_args = [];
      args = [ half; one ];
    })
  in
  match Smtlib.emit ir with
  | Ok script ->
    Alcotest.(check string) "closed Real-literal goal picks QF_LRA"
      "QF_LRA" script.logic
  | Error e ->
    Alcotest.fail ("emit failed: " ^ Smtlib.detail_of_error e)

let test_emit_logic_lra_from_real_eq_only () =
  (* Real-typed equality with no Real free var: still QF_LRA. *)
  let n : Ir.shell_term = Var { name = "n" } in
  let h0 : Ir.hypothesis = {
    name = "h0";
    shell = Eq {
      ty = "Real"; left = n; right = n;
    };
  } in
  let ir = make_ir
    ~free_vars:[ { name = "n"; ty = "Int" } ]
    ~hypotheses:[ h0 ]
    (Ir.Const { name = "True" })
  in
  match Smtlib.emit ir with
  | Ok script ->
    Alcotest.(check string) "Real-typed Eq picks QF_LRA"
      "QF_LRA" script.logic
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

(* --- BV vertical slice ----------------------------------------------- *)

let bv8 : Ir.type_ref = "BitVec(8)"

let test_emit_bv_sort () =
  let ir = make_ir
    ~free_vars:[ { name = "x"; ty = bv8 } ]
    (Eq { ty = bv8; left = Var { name = "x" }; right = Var { name = "x" } })
  in
  match Smtlib.emit ir with
  | Ok script ->
    Alcotest.(check bool) "declare-const x with BitVec sort" true
      (try
         ignore (Str.search_forward
           (Str.regexp_string "(declare-const x (_ BitVec 8))")
           script.body 0); true
       with Not_found -> false)
  | Error e ->
    Alcotest.fail ("emit failed: " ^ Smtlib.detail_of_error e)

let test_emit_bv_literal () =
  Alcotest.(check string) "BV literal 5 over BV8 → (_ bv5 8)"
    "(_ bv5 8)" (emit_term_ok (Num_lit { value = "5"; ty = bv8 }))

let test_emit_bvadd () =
  let t = Ir.App {
    symbol = "BV.add"; type_args = [];
    args = [
      Var { name = "x" };
      Num_lit { value = "3"; ty = bv8 };
    ];
  } in
  Alcotest.(check string) "(bvadd x (_ bv3 8))"
    "(bvadd x (_ bv3 8))" (emit_term_ok t)

let test_emit_bvult () =
  let t = Ir.App {
    symbol = "BV.ult"; type_args = [];
    args = [ Var { name = "x" }; Num_lit { value = "5"; ty = bv8 } ];
  } in
  Alcotest.(check string) "(bvult x (_ bv5 8))"
    "(bvult x (_ bv5 8))" (emit_term_ok t)

let test_emit_bvsle () =
  let t = Ir.App {
    symbol = "BV.sle"; type_args = [];
    args = [ Num_lit { value = "0"; ty = bv8 }; Var { name = "x" } ];
  } in
  Alcotest.(check string) "(bvsle (_ bv0 8) x)"
    "(bvsle (_ bv0 8) x)" (emit_term_ok t)

let test_emit_bv_eq () =
  let t = Ir.Eq {
    ty = bv8;
    left = Var { name = "x" };
    right = Num_lit { value = "8"; ty = bv8 };
  } in
  Alcotest.(check string) "(= x (_ bv8 8))"
    "(= x (_ bv8 8))" (emit_term_ok t)

let test_emit_logic_bv () =
  let ir = make_ir
    ~free_vars:[ { name = "x"; ty = bv8 } ]
    (Eq { ty = bv8;
          left = Var { name = "x" };
          right = Num_lit { value = "0"; ty = bv8 } })
  in
  match Smtlib.emit ir with
  | Ok script -> Alcotest.(check string) "QF_BV" "QF_BV" script.logic
  | Error e -> Alcotest.fail ("emit failed: " ^ Smtlib.detail_of_error e)

let test_emit_bv_negative_rejected () =
  let specs = ref [] in
  match Smtlib.emit_term ~specs (Num_lit { value = "-1"; ty = bv8 }) with
  | Ok s -> Alcotest.fail ("expected rejection, got: " ^ s)
  | Error _ -> ()

let test_emit_bv_zero_width_rejected () =
  match Smtlib.sort_of_type_ref ~site:"test" "BitVec(0)" with
  | Ok s -> Alcotest.fail ("expected rejection of width 0, got: " ^ s)
  | Error _ -> ()

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
      Alcotest.test_case "NumLit big int (Zarith)"
        `Quick test_emit_num_lit_big_int;
      Alcotest.test_case "NumLit Real rational"
        `Quick test_emit_num_lit_real_rational;
      Alcotest.test_case "NumLit Real decimal"
        `Quick test_emit_num_lit_real_decimal;
    ];
    "literal errors", [
      Alcotest.test_case "Int with slash rejected"
        `Quick test_emit_num_lit_int_with_slash_rejected;
      Alcotest.test_case "Int with dot rejected"
        `Quick test_emit_num_lit_int_with_dot_rejected;
      Alcotest.test_case "exponent rejected"
        `Quick test_emit_num_lit_exponent_rejected;
      Alcotest.test_case "garbage rejected"
        `Quick test_emit_num_lit_garbage_rejected;
    ];
    "identifier sanitization", [
      Alcotest.test_case "simple symbol unquoted"
        `Quick test_emit_var_simple_unquoted;
      Alcotest.test_case "name with space rejected"
        `Quick test_emit_var_with_space_rejected;
      Alcotest.test_case "leading digit rejected"
        `Quick test_emit_var_starting_with_digit_rejected;
      Alcotest.test_case "reserved word rejected"
        `Quick test_emit_var_reserved_word_rejected;
      Alcotest.test_case "pipe in name rejected"
        `Quick test_emit_var_pipe_rejected;
      Alcotest.test_case "declare-const rejects non-simple name"
        `Quick test_emit_declare_const_rejects_non_simple;
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
      Alcotest.test_case "QF_LRA from closed Real-literal goal"
        `Quick test_emit_logic_lra_from_real_literal_only;
      Alcotest.test_case "QF_LRA from Real-typed Eq with no Real free var"
        `Quick test_emit_logic_lra_from_real_eq_only;
      Alcotest.test_case "full script" `Quick test_emit_full_script;
    ];
    "bv", [
      Alcotest.test_case "BitVec(8) sort" `Quick test_emit_bv_sort;
      Alcotest.test_case "BV literal" `Quick test_emit_bv_literal;
      Alcotest.test_case "bvadd" `Quick test_emit_bvadd;
      Alcotest.test_case "bvult" `Quick test_emit_bvult;
      Alcotest.test_case "bvsle" `Quick test_emit_bvsle;
      Alcotest.test_case "BV equality" `Quick test_emit_bv_eq;
      Alcotest.test_case "QF_BV logic" `Quick test_emit_logic_bv;
      Alcotest.test_case "negative BV literal rejected"
        `Quick test_emit_bv_negative_rejected;
      Alcotest.test_case "BitVec(0) rejected" `Quick test_emit_bv_zero_width_rejected;
    ];
  ]

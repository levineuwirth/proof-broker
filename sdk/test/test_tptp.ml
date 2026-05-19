(** Unit tests for [Tptp].

    Coverage:
    * Dialect selection: [dialect_of_ir] is order-driven
      (higher_order → THF, else FOF).
    * FOF: predicate/function application, connectives, equality,
      quantifiers with alpha-renamed bound vars, free vars as
      constants, single-quoted non-lower-word symbols, hypotheses
      as [axiom] + goal as [conjecture].
    * THF: $tType + typed-constant declarations, [@] application,
      [^]-lambda, typed binders; the M1 boundary error when an
      applied symbol has no [free_vars] declaration (example2 as
      written).
    * Errors: [Num_lit] rejected (no M1 arithmetic), [Lambda] in a
      FOF IR is [Higher_order_in_fof], [Opaque] rejected. *)

open Proof_broker

let trivial_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "FOL";
  decidable_theory = None;
}

let ho_logic : Ir.logic_classification = {
  order = "higher_order";
  features_used = [];
  first_order_fragment = "none";
  decidable_theory = None;
}

let make_ir ?(logic = trivial_logic) ?(free_vars = []) ?(hypotheses = [])
    (goal_shell : Ir.shell_term) : Ir.t = {
  ir_version = "1.0";
  source_system = { name = "test"; version = "0.0" };
  tier = "goal";
  logic_classification = logic;
  goal = { shell = goal_shell; payloads = None };
  context = { type_vars = []; free_vars; hypotheses; library_slice = None };
  type_metadata = [];
  definitional_metadata = [];
  library_provenance = [];
  user_directives = None;
}

let emit_ok ir =
  match Tptp.emit ir with
  | Ok s -> s
  | Error e -> Alcotest.fail ("Tptp.emit failed: " ^ Tptp.detail_of_error e)

let emit_err ir =
  match Tptp.emit ir with
  | Ok s -> Alcotest.fail ("expected error, got: " ^ s.body)
  | Error e -> Tptp.kind_of_error e

let contains hay needle =
  let nl = String.length needle and hl = String.length hay in
  let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in
  nl = 0 || go 0

(* --- dialect selection ----------------------------------------------- *)

let test_dialect_fof () =
  let ir = make_ir (App { symbol = "p"; type_args = []; args = [] }) in
  Alcotest.(check bool) "first_order → FOF" true
    (Tptp.dialect_of_ir ir = Tptp.Fof)

let test_dialect_thf () =
  let ir =
    make_ir ~logic:ho_logic (App { symbol = "p"; type_args = []; args = [] })
  in
  Alcotest.(check bool) "higher_order → THF" true
    (Tptp.dialect_of_ir ir = Tptp.Thf)

(* --- FOF ------------------------------------------------------------- *)

let test_fof_atom_goal () =
  let ir =
    make_ir
      ~hypotheses:[ { name = "h1";
                      shell = App { symbol = "p"; type_args = [];
                                    args = [ Var { name = "a" } ] } } ]
      (App { symbol = "p"; type_args = []; args = [ Var { name = "a" } ] })
  in
  let s = emit_ok ir in
  Alcotest.(check bool) "dialect FOF" true (s.dialect = Tptp.Fof);
  Alcotest.(check bool) "hypothesis as axiom" true
    (contains s.body "fof(h1, axiom, p(a)).");
  Alcotest.(check bool) "goal as conjecture" true
    (contains s.body "fof(goal, conjecture, p(a)).")

let test_fof_connectives_and_eq () =
  let ir =
    make_ir
      (Implies {
         antecedent = And {
           left = App { symbol = "p"; type_args = []; args = [] };
           right = Not { operand =
             App { symbol = "q"; type_args = []; args = [] } } };
         consequent = Eq {
           ty = "Nat";
           left = Var { name = "a" };
           right = Var { name = "b" } } })
  in
  let s = emit_ok ir in
  Alcotest.(check bool) "implies/and/not/eq" true
    (contains s.body "((p & ~ (q)) => (a = b))")

let test_fof_quantifier_alpha_rename () =
  (* ! x. (p(x) => q(x)) — bound x must become an upper-word, and
     the same fresh name must appear at both use sites. *)
  let ir =
    make_ir
      (Forall {
         var = "x"; ty = "Nat";
         body = Implies {
           antecedent = App { symbol = "p"; type_args = [];
                              args = [ Var { name = "x" } ] };
           consequent = App { symbol = "q"; type_args = [];
                              args = [ Var { name = "x" } ] } } })
  in
  let s = emit_ok ir in
  Alcotest.(check bool) "fresh upper-word binder + both uses" true
    (contains s.body "! [X1] : ((p(X1) => q(X1)))")

let test_fof_quoted_symbol () =
  (* A non-lower-word functor (uppercase head, dotted name) must be
     single-quoted, and the rename recorded in the side-channel. *)
  let ir =
    make_ir
      (App { symbol = "Function.comp"; type_args = [];
             args = [ Var { name = "g" } ] })
  in
  let s = emit_ok ir in
  Alcotest.(check bool) "single-quoted functor" true
    (contains s.body "'Function.comp'(g)");
  Alcotest.(check bool) "rename recorded" true
    (List.exists
       (fun (sp : Tptp.specialization) ->
          sp.source = "Function.comp" && sp.target = "'Function.comp'")
       s.specializations)

(* --- THF ------------------------------------------------------------- *)

let test_thf_declared_ho () =
  (* P : (Nat -> Nat) -> Prop, g : Nat -> Nat ⊢ P (comp g g), with
     comp declared. Checks $tType + typed decls + @-application. *)
  let ir =
    make_ir ~logic:ho_logic
      ~free_vars:[
        { name = "nat_id"; ty = "Nat -> Nat" };
        { name = "g"; ty = "Nat -> Nat" };
        { name = "pp"; ty = "(Nat -> Nat) -> Prop" };
        { name = "comp"; ty = "(Nat -> Nat) -> (Nat -> Nat) -> (Nat -> Nat)" };
      ]
      (App { symbol = "pp"; type_args = [];
             args = [ App { symbol = "comp"; type_args = [];
                            args = [ Var { name = "g" }; Var { name = "g" } ] } ] })
  in
  let s = emit_ok ir in
  Alcotest.(check bool) "dialect THF" true (s.dialect = Tptp.Thf);
  Alcotest.(check bool) "base $tType declared (single-quoted)" true
    (contains s.body "'Nat': $tType).");
  Alcotest.(check bool) "predicate decl uses $o + arrow" true
    (contains s.body "pp: ('Nat' > 'Nat') > $o).");
  Alcotest.(check bool) "applicative goal" true
    (contains s.body "(pp @ (comp @ g @ g))")

let test_thf_lambda () =
  let ir =
    make_ir ~logic:ho_logic
      ~free_vars:[ { name = "pp"; ty = "(Nat -> Nat) -> Prop" } ]
      (App { symbol = "pp"; type_args = [];
             args = [ Lambda {
               binders = [ { var = "y"; ty = "Nat" } ];
               body = Var { name = "y" } } ] })
  in
  let s = emit_ok ir in
  Alcotest.(check bool) "lambda with typed binder" true
    (contains s.body "(^ [X1 : 'Nat'] : X1)")

let test_thf_undeclared_symbol_is_typed_error () =
  (* example2 as written: Function.comp is only in
     definitional_metadata, not free_vars → typed Unsupported. *)
  let ir =
    make_ir ~logic:ho_logic
      ~free_vars:[ { name = "g"; ty = "Nat -> Nat" };
                   { name = "P"; ty = "(Nat -> Nat) -> Prop" } ]
      (App { symbol = "P"; type_args = [];
             args = [ App { symbol = "Function.comp"; type_args = [];
                            args = [ Var { name = "g" }; Var { name = "g" } ] } ] })
  in
  Alcotest.(check string) "undeclared THF symbol → unsupported_symbol"
    "unsupported_symbol" (emit_err ir)

(* --- errors ---------------------------------------------------------- *)

let test_num_lit_rejected () =
  let ir = make_ir (Num_lit { value = "3"; ty = "Int" }) in
  Alcotest.(check string) "Num_lit → bad_literal" "bad_literal"
    (emit_err ir)

let test_lambda_in_fof_rejected () =
  let ir =
    make_ir (Lambda { binders = [ { var = "z"; ty = "Nat" } ];
                      body = Var { name = "z" } })
  in
  Alcotest.(check string) "Lambda in FOF → higher_order_in_fof"
    "higher_order_in_fof" (emit_err ir)

let test_opaque_rejected () =
  let ir = make_ir (Opaque { payload_id = "blob1" }) in
  Alcotest.(check string) "Opaque → unsupported_node" "unsupported_node"
    (emit_err ir)

let () =
  Alcotest.run "tptp"
    [
      ( "dialect",
        [ Alcotest.test_case "fof" `Quick test_dialect_fof;
          Alcotest.test_case "thf" `Quick test_dialect_thf ] );
      ( "fof",
        [ Alcotest.test_case "atom goal" `Quick test_fof_atom_goal;
          Alcotest.test_case "connectives+eq" `Quick test_fof_connectives_and_eq;
          Alcotest.test_case "alpha-rename" `Quick test_fof_quantifier_alpha_rename;
          Alcotest.test_case "quoted symbol" `Quick test_fof_quoted_symbol ] );
      ( "thf",
        [ Alcotest.test_case "declared HO" `Quick test_thf_declared_ho;
          Alcotest.test_case "lambda" `Quick test_thf_lambda;
          Alcotest.test_case "undeclared→typed error" `Quick
            test_thf_undeclared_symbol_is_typed_error ] );
      ( "errors",
        [ Alcotest.test_case "num_lit" `Quick test_num_lit_rejected;
          Alcotest.test_case "lambda-in-fof" `Quick test_lambda_in_fof_rejected;
          Alcotest.test_case "opaque" `Quick test_opaque_rejected ] );
    ]

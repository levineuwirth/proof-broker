(** Unit tests for [Z3_proof].

    Coverage:
    * Single-binding let resolution: [(let ((x 1)) x)] → [1].
    * Nested-let resolution: each binding resolves under the
      enclosing table.
    * Multi-binding let: parallel SMT-LIB semantics, all values
      resolve under the outer table before new names enter scope.
    * Substitution inside rule applications: bindings stay reachable
      from arbitrary positions in the body.
    * [extract_proof_term] on a synthesized z3 envelope.
    * [extract_proof_term] on a real two-hypothesis Farkas proof
      (the [(_ th-lemma arith farkas 1 1) ...] shape) — the
      resolved term contains no [let] nodes and the th-lemma
      head is reachable. *)

open Proof_broker
open Z3_proof

let parse_one (s : string) : Sexp.t =
  match parse_string s with
  | [ x ] -> x
  | _ -> Alcotest.fail "expected single S-expression"

(* Path is relative to [_build/default/test/], the CWD [dune runtest]
   gives a test executable. Mirrors [test_alethe_passthrough]. *)
let load_fixture name =
  let path =
    Filename.concat (Sys.getcwd ()) ("../../../../sdk/test/fixtures/" ^ name)
  in
  In_channel.with_open_text path In_channel.input_all

let test_atom_passthrough () =
  let t = parse_one "foo" in
  let r = resolve_lets t in
  Alcotest.(check string) "atom unchanged" "foo" (Sexp.to_string r)

let test_single_let () =
  let t = parse_one "(let ((x 42)) x)" in
  let r = resolve_lets t in
  Alcotest.(check string) "x → 42" "42" (Sexp.to_string r)

let test_nested_let () =
  let t = parse_one "(let ((x 1)) (let ((y (+ x 2))) (+ y x)))" in
  let r = resolve_lets t in
  Alcotest.(check string) "y resolves under outer x; body resolves under both"
    "(+ (+ 1 2) 1)" (Sexp.to_string r)

let test_multi_binding_let () =
  (* Parallel SMT-LIB semantics: both values resolve under the
     OUTER table (no x in scope for the inner binding's value), so
     [(let ((x 1) (y x)) ...)] leaves [y] referencing the *outer*
     [x]. We use an outer let to make the difference observable. *)
  let t = parse_one "(let ((x 9)) (let ((x 1) (y x)) (+ x y)))" in
  let r = resolve_lets t in
  Alcotest.(check string) "y binds outer x=9, x rebinds to 1"
    "(+ 1 9)" (Sexp.to_string r)

let test_let_in_rule_application () =
  let t = parse_one
    "(let ((@p (asserted ($x))))(let (($x (>= n 5)))(unit-resolution @p false)))"
  in
  let r = resolve_lets t in
  (* @p resolves under the empty outer table (so $x still atomic
     there), then the inner $x replaces $x in the body's
     [unit-resolution] application. *)
  Alcotest.(check string) "rule application carries resolved bindings"
    "(unit-resolution (asserted ($x)) false)" (Sexp.to_string r)

let test_extract_proof_term_simple () =
  let envelope = "((set-logic QF_LIA)(proof (let ((@p (asserted (>= n 5))))@p)))" in
  match extract_proof_term envelope with
  | None -> Alcotest.fail "expected Some proof term"
  | Some t ->
    Alcotest.(check string) "envelope unwraps + lets resolve"
      "(asserted (>= n 5))" (Sexp.to_string t)

let test_extract_proof_term_real_farkas () =
  (* Verbatim z3 4.16.0 output for QF_LRA x>=5, x<=3 ⊢ false. *)
  let envelope =
    "((set-logic QF_LRA)\n\
     (proof\n\
     (let (($x28 (<= x 3.0)))\n\
     (let ((@x29 (asserted $x28)))\n\
     (let (($x25 (>= x 5.0)))\n\
     (let ((@x26 (asserted $x25)))\n\
     (unit-resolution ((_ th-lemma arith farkas 1 1) (or (not $x28) (not $x25))) @x26 @x29 false)))))))"
  in
  match extract_proof_term envelope with
  | None -> Alcotest.fail "expected Some proof term"
  | Some t ->
    let s = Sexp.to_string t in
    (* All four let-bound names should be substituted out. *)
    Alcotest.(check bool) "no $x28 atoms remain" false
      (String.length s > 0 && (try ignore (Str.search_forward (Str.regexp_string "$x28") s 0); true with Not_found -> false));
    Alcotest.(check bool) "no @x29 atoms remain" false
      (try ignore (Str.search_forward (Str.regexp_string "@x29") s 0); true
       with Not_found -> false);
    (* The Farkas th-lemma head and its coefficients are still
       visible in the resolved term. *)
    Alcotest.(check bool) "th-lemma farkas coefficients survive" true
      (try ignore (Str.search_forward (Str.regexp_string "th-lemma arith farkas 1 1") s 0); true
       with Not_found -> false);
    (* The hypothesis literals (now resolved) appear inside the
       clause. *)
    Alcotest.(check bool) "(>= x 5.0) literal appears" true
      (try ignore (Str.search_forward (Str.regexp_string "(>= x 5.0)") s 0); true
       with Not_found -> false);
    Alcotest.(check bool) "(<= x 3.0) literal appears" true
      (try ignore (Str.search_forward (Str.regexp_string "(<= x 3.0)") s 0); true
       with Not_found -> false)

let test_extract_proof_term_returns_none_on_garbage () =
  match extract_proof_term "not an envelope" with
  | None -> ()
  | Some _ -> Alcotest.fail "expected None on non-envelope input"

(* --- Farkas extraction tests --------------------------------------- *)

let rat (n : int) (d : int) : Linear_arith.rational =
  { num = Z.of_int n; den = Z.of_int d }

let rat_eq (a : Linear_arith.rational) (b : Linear_arith.rational) : bool =
  Z.equal a.num b.num && Z.equal a.den b.den

let test_parse_farkas_rule_head_simple () =
  let head = parse_one "(_ th-lemma arith farkas 1 1)" in
  match parse_farkas_rule_head head with
  | None -> Alcotest.fail "expected Some coefficients"
  | Some coefs ->
    Alcotest.(check int) "two coefficients" 2 (List.length coefs);
    Alcotest.(check bool) "first coef = 1" true (rat_eq (rat 1 1) (List.nth coefs 0));
    Alcotest.(check bool) "second coef = 1" true (rat_eq (rat 1 1) (List.nth coefs 1))

let test_parse_farkas_rule_head_rationals () =
  let head = parse_one "(_ th-lemma arith farkas 3 1/2 7)" in
  match parse_farkas_rule_head head with
  | None -> Alcotest.fail "expected Some coefficients"
  | Some coefs ->
    Alcotest.(check int) "three coefficients" 3 (List.length coefs);
    Alcotest.(check bool) "second coef = 1/2" true (rat_eq (rat 1 2) (List.nth coefs 1))

let test_parse_farkas_rule_head_rejects_non_farkas () =
  let head = parse_one "(_ th-lemma arith)" in
  Alcotest.(check bool) "bare arith th-lemma rejected" true
    (Option.is_none (parse_farkas_rule_head head));
  let head2 = parse_one "(_ th-lemma arith gomory-cut 1 1)" in
  Alcotest.(check bool) "gomory-cut rejected" true
    (Option.is_none (parse_farkas_rule_head head2))

let test_find_farkas_clause_real_proof () =
  (* z3 4.16.0 verbatim, two-hyp LRA Farkas. *)
  let envelope =
    "((set-logic QF_LRA)\n\
     (proof\n\
     (let (($x28 (<= x 3.0)))\n\
     (let ((@x29 (asserted $x28)))\n\
     (let (($x25 (>= x 5.0)))\n\
     (let ((@x26 (asserted $x25)))\n\
     (unit-resolution ((_ th-lemma arith farkas 1 1) (or (not $x28) (not $x25))) @x26 @x29 false)))))))"
  in
  let term = match extract_proof_term envelope with
    | Some t -> t
    | None -> Alcotest.fail "envelope unwrap failed"
  in
  match find_farkas_clause term with
  | None -> Alcotest.fail "expected Farkas extraction on a Farkas-shaped proof"
  | Some { coefficients; literals } ->
    Alcotest.(check int) "two coefficients" 2 (List.length coefficients);
    Alcotest.(check int) "two literals" 2 (List.length literals);
    Alcotest.(check bool) "first coef = 1" true
      (rat_eq (rat 1 1) (List.nth coefficients 0));
    Alcotest.(check bool) "second coef = 1" true
      (rat_eq (rat 1 1) (List.nth coefficients 1));
    Alcotest.(check string) "first literal = (<= x 3.0)"
      "(<= x 3.0)" (Sexp.to_string (List.nth literals 0));
    Alcotest.(check string) "second literal = (>= x 5.0)"
      "(>= x 5.0)" (Sexp.to_string (List.nth literals 1))

let test_find_farkas_clause_returns_none_on_opaque () =
  (* Opaque arith th-lemma (no farkas tag, no clause shape). *)
  let envelope =
    "((set-logic QF_LIA)(proof ((_ th-lemma arith) (asserted (>= n 5)) false)))"
  in
  let term = match extract_proof_term envelope with
    | Some t -> t
    | None -> Alcotest.fail "envelope unwrap failed"
  in
  Alcotest.(check bool) "no Farkas extraction on opaque th-lemma" true
    (Option.is_none (find_farkas_clause term))

let test_find_farkas_clause_mismatched_arity_rejected () =
  (* 2 coefficients but 3 disjuncts — must reject. *)
  let envelope =
    "((set-logic QF_LRA)(proof\n\
     (unit-resolution ((_ th-lemma arith farkas 1 1) (or (not (<= x 3.0)) (not (>= x 5.0)) (not (<= y 0.0)))) false)))"
  in
  let term = match extract_proof_term envelope with
    | Some t -> t
    | None -> Alcotest.fail "envelope unwrap failed"
  in
  Alcotest.(check bool) "mismatched coef/disjunct arity rejected" true
    (Option.is_none (find_farkas_clause term))

(* --- direct-shape (Case 1) tests ----------------------------------- *)

let test_chase_to_conclusion () =
  (* (asserted L) → L. *)
  let p = parse_one "(asserted (<= n 10))" in
  (match chase_to_conclusion p with
   | Some t -> Alcotest.(check string) "(asserted L) chases to L"
                 "(<= n 10)" (Sexp.to_string t)
   | None -> Alcotest.fail "expected Some literal");
  (* (mp p1 p2 L) → L (last positional arg). *)
  let p2 = parse_one "(mp pf rew (>= m 0))" in
  (match chase_to_conclusion p2 with
   | Some t -> Alcotest.(check string) "(mp _ _ L) chases to L"
                 "(>= m 0)" (Sexp.to_string t)
   | None -> Alcotest.fail "expected Some literal");
  (* Atom has no chase target. *)
  Alcotest.(check bool) "atom has no conclusion" true
    (Option.is_none (chase_to_conclusion (Sexp.Atom "@x40")))

let test_parse_farkas_direct_application () =
  (* The verbatim shape z3 4.16.0 emits with arith.solver=2 for a
     three-hypothesis LIA proof. Three premises, three coefs
     (signed: -1, -1, 1), trailing `false`. *)
  let app = parse_one
    "((_ th-lemma arith farkas -1 -1 1) \
       (mp p1 rew (not (<= n 10))) \
       (mp p2 rew (>= m 0)) \
       (asserted (<= (+ n m) 10)) \
       false)"
  in
  match parse_farkas_direct_application app with
  | None -> Alcotest.fail "expected Some farkas_extract"
  | Some { coefficients; literals } ->
    Alcotest.(check int) "three coefficients" 3 (List.length coefficients);
    Alcotest.(check int) "three literals" 3 (List.length literals);
    (* Signs preserved at the parser layer; consumers (Z3_farkas)
       take absolute values. *)
    Alcotest.(check string) "first coef = -1"
      "-1" (Linear_arith.rat_to_string (List.nth coefficients 0));
    Alcotest.(check string) "third coef = 1"
      "1" (Linear_arith.rat_to_string (List.nth coefficients 2));
    Alcotest.(check string) "first literal = (not (<= n 10))"
      "(not (<= n 10))" (Sexp.to_string (List.nth literals 0));
    Alcotest.(check string) "third literal = (<= (+ n m) 10)"
      "(<= (+ n m) 10)" (Sexp.to_string (List.nth literals 2))

let test_parse_farkas_direct_rejects_non_false_conclusion () =
  (* th-lemma not closed by `false` — wrong shape for the direct
     case (probably feeding a downstream resolution). *)
  let app = parse_one
    "((_ th-lemma arith farkas 1) (asserted (<= n 10)) (= (<= n 10) (<= n 10)))"
  in
  Alcotest.(check bool) "non-false conclusion rejected" true
    (Option.is_none (parse_farkas_direct_application app))

let test_parse_farkas_direct_rejects_arity_mismatch () =
  let app = parse_one
    "((_ th-lemma arith farkas 1 1) (asserted A) (asserted B) (asserted C) false)"
  in
  Alcotest.(check bool) "2 coefs vs 3 premises rejected" true
    (Option.is_none (parse_farkas_direct_application app))

let test_find_farkas_direct_walks_into_lets () =
  (* The direct-shape th-lemma is buried inside a let-resolved
     proof tree. find_farkas_direct's depth-first walk should
     locate it. *)
  let envelope =
    "((set-logic QF_LIA)\n\
     (proof\n\
     (let (($p (<= n 10)))\n\
     (let ((@a (asserted $p)))\n\
     ((_ th-lemma arith farkas 1) (mp @a (rewrite (= $p $p)) $p) false)))))"
  in
  let term = match extract_proof_term envelope with
    | Some t -> t
    | None -> Alcotest.fail "envelope unwrap failed"
  in
  match find_farkas_direct term with
  | None -> Alcotest.fail "expected to find a direct th-lemma"
  | Some { coefficients; literals } ->
    Alcotest.(check int) "one coef" 1 (List.length coefficients);
    Alcotest.(check int) "one literal" 1 (List.length literals);
    Alcotest.(check string) "literal resolves through let"
      "(<= n 10)" (Sexp.to_string (List.hd literals))

(** Example1 IR matching [z3-lia-n-m-10-m-0.proof]: hypotheses
    [n + m = 10] and [0 ≤ m], goal [n ≤ 10]. Shared between the
    direct-shape end-to-end test and the fixture_regression mirrors. *)
let lia_three_hyp_ir () : Ir.t =
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
  let logic : Ir.logic_classification = {
    order = "first_order";
    features_used = [];
    first_order_fragment = "LIA";
    decidable_theory = None;
  } in
  {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = logic;
    goal = {
      shell = App { symbol = "LE.le"; type_args = []; args = [ n; ten ] };
      payloads = None;
    };
    context = {
      type_vars = [];
      free_vars = [
        { name = "n"; ty = "Int" }; { name = "m"; ty = "Int" }
      ];
      hypotheses = [ h1; h3 ];
      library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

(** End-to-end: feed a real example1-shaped z3 proof (LIA, three
    hypotheses, direct-shape th-lemma with signed coefficients
    [-1, -1, 1]) through Z3_farkas.extract on a matching IR.
    Exercises the abs-value heuristic + Le-vs-Eq matching + pre-
    verification gate in one path. *)
let test_z3_farkas_extracts_case1_example1 () =
  let ir = lia_three_hyp_ir () in
  let proof_str = load_fixture "z3-lia-n-m-10-m-0.proof" in
  match Z3_farkas.extract ir proof_str with
  | Error e ->
    Alcotest.fail
      (Printf.sprintf "expected Ok witness, got Error %s: %s"
         (Z3_farkas.error_kind e) (Z3_farkas.error_detail e))
  | Ok witness ->
    (* The witness must round-trip through Farkas.verify
       (Z3_farkas pre-verifies, but a cross-check confirms the
       JSON encoding survives serialization). *)
    (match Farkas.verify ir witness with
     | Verified -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf "witness re-verify failed: %s"
            (match other with
             | Not_contradictory { residual } -> "not contradictory: " ^ residual
             | Negative_coefficient { hypothesis; value } ->
               Printf.sprintf "neg coef on %s = %s" hypothesis value
             | _ -> "other failure")))

let test_find_farkas_unified_prefers_clause () =
  (* Both shapes are syntactically present. The unified walker
     should pick the clause shape because the outer wrapping (a
     unit-resolution) contains it. *)
  let envelope =
    "((set-logic QF_LRA)\n\
     (proof\n\
     (let (($x28 (<= x 3.0)))\n\
     (let ((@x29 (asserted $x28)))\n\
     (let (($x25 (>= x 5.0)))\n\
     (let ((@x26 (asserted $x25)))\n\
     (unit-resolution ((_ th-lemma arith farkas 1 1) (or (not $x28) (not $x25))) @x26 @x29 false)))))))"
  in
  let term = match extract_proof_term envelope with
    | Some t -> t
    | None -> Alcotest.fail "envelope unwrap failed"
  in
  match find_farkas term with
  | None -> Alcotest.fail "expected Some farkas_extract"
  | Some { literals; _ } ->
    (* Clause shape returns positive literals (no `(not _)` wrapping). *)
    Alcotest.(check string) "clause-shape literal is positive form"
      "(<= x 3.0)" (Sexp.to_string (List.nth literals 0))

(* --- on-disk fixture regression ----------------------------------- *)

(* Verbatim z3 4.16.0 [(get-proof)] envelopes captured with
   [:smt.arith.solver 2] (mirroring [Adapter_z3]'s preamble), one per
   th-lemma surface shape:
     - [z3-lra-x-5-x-3.proof]: clause-introducing form
       [((_ th-lemma arith farkas C1...Cn) (or (not L1) ...))]
       from LRA [x >= 5, x <= 3 ⊢ False].
     - [z3-lia-n-m-10-m-0.proof]: direct-from-premises form
       [((_ th-lemma arith farkas C1...Cn) p1 ... pn false)] with
       signed coefficients, from LIA [n+m=10, m>=0 ⊢ n<=10].
   The solver-spawning end-to-end variants live in [test_adapter_z3];
   these run without z3 on the box, so CI stays green and the tests
   trip loudly if a z3 upgrade changes the surface syntax. *)

let lra_two_hyp_ir () : Ir.t =
  let lra_logic : Ir.logic_classification = {
    order = "first_order";
    features_used = [];
    first_order_fragment = "LRA";
    decidable_theory = None;
  } in
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

let test_fixture_envelope_unwraps_lra () =
  let envelope = load_fixture "z3-lra-x-5-x-3.proof" in
  match extract_proof_term envelope with
  | None -> Alcotest.fail "expected Some proof term from LRA fixture"
  | Some t ->
    let s = Sexp.to_string t in
    Alcotest.(check bool) "no $x28 atoms remain" false
      (try ignore (Str.search_forward (Str.regexp_string "$x28") s 0); true
       with Not_found -> false);
    Alcotest.(check bool) "no @x29 atoms remain" false
      (try ignore (Str.search_forward (Str.regexp_string "@x29") s 0); true
       with Not_found -> false);
    Alcotest.(check bool) "th-lemma farkas 1 1 head visible" true
      (try ignore (Str.search_forward
                     (Str.regexp_string "th-lemma arith farkas 1 1") s 0); true
       with Not_found -> false)

let test_fixture_find_farkas_clause_lra () =
  let envelope = load_fixture "z3-lra-x-5-x-3.proof" in
  let term = match extract_proof_term envelope with
    | Some t -> t
    | None -> Alcotest.fail "LRA fixture envelope unwrap failed"
  in
  match find_farkas_clause term with
  | None -> Alcotest.fail "expected Farkas extraction on LRA fixture"
  | Some { coefficients; literals } ->
    Alcotest.(check int) "two coefficients" 2 (List.length coefficients);
    Alcotest.(check int) "two literals" 2 (List.length literals);
    Alcotest.(check bool) "both coefs = 1" true
      (List.for_all (rat_eq (rat 1 1)) coefficients);
    Alcotest.(check string) "first literal = (<= x 3.0)"
      "(<= x 3.0)" (Sexp.to_string (List.nth literals 0));
    Alcotest.(check string) "second literal = (>= x 5.0)"
      "(>= x 5.0)" (Sexp.to_string (List.nth literals 1))

let test_fixture_z3_farkas_extract_and_verify_lra () =
  let envelope = load_fixture "z3-lra-x-5-x-3.proof" in
  let ir = lra_two_hyp_ir () in
  match Z3_farkas.extract ir envelope with
  | Error e ->
    Alcotest.fail
      (Printf.sprintf "expected witness, got Error(%s: %s)"
         (Z3_farkas.error_kind e) (Z3_farkas.error_detail e))
  | Ok witness ->
    (* End-to-end soundness gate: the witness re-verifies under the
       independent [Farkas.verify] checker, matching [Adapter_z3]'s
       Tier 1 minting path. *)
    (match Farkas.verify ir witness with
     | Verified -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf "fixture witness failed re-verify: %s"
            (match other with
             | Not_contradictory { residual } ->
               "not contradictory: " ^ residual
             | Negative_coefficient { hypothesis; value } ->
               Printf.sprintf "neg coef on %s = %s" hypothesis value
             | _ -> "other failure")))

let test_fixture_envelope_unwraps_lia () =
  let envelope = load_fixture "z3-lia-n-m-10-m-0.proof" in
  match extract_proof_term envelope with
  | None -> Alcotest.fail "expected Some proof term from LIA fixture"
  | Some t ->
    let s = Sexp.to_string t in
    (* All let-bound names z3 emits in this fixture must disappear
       after [resolve_lets]. *)
    List.iter (fun name ->
      Alcotest.(check bool) (Printf.sprintf "no %s atoms remain" name) false
        (try ignore (Str.search_forward (Str.regexp_string name) s 0); true
         with Not_found -> false))
      [ "$x27"; "$x30"; "$x34"; "$x37"; "$x51"; "$x58";
        "@x31"; "@x33"; "@x38"; "@x40"; "@x62"; "@x64"; "?x25" ];
    Alcotest.(check bool) "th-lemma farkas -1 -1 1 head visible" true
      (try ignore (Str.search_forward
                     (Str.regexp_string "th-lemma arith farkas -1 -1 1") s 0); true
       with Not_found -> false)

let test_fixture_find_farkas_direct_lia () =
  let envelope = load_fixture "z3-lia-n-m-10-m-0.proof" in
  let term = match extract_proof_term envelope with
    | Some t -> t
    | None -> Alcotest.fail "LIA fixture envelope unwrap failed"
  in
  match find_farkas_direct term with
  | None ->
    Alcotest.fail "expected direct-shape Farkas extraction on LIA fixture"
  | Some { coefficients; literals } ->
    Alcotest.(check int) "three coefficients" 3 (List.length coefficients);
    Alcotest.(check int) "three literals" 3 (List.length literals);
    (* z3 emits signed coefficients; Z3_proof preserves them verbatim
       and Z3_farkas takes absolute values. See
       [parse_farkas_direct_application] for the contract. *)
    Alcotest.(check string) "first coef = -1"
      "-1" (Linear_arith.rat_to_string (List.nth coefficients 0));
    Alcotest.(check string) "third coef = 1"
      "1" (Linear_arith.rat_to_string (List.nth coefficients 2));
    Alcotest.(check string) "first literal = (not (<= n 10))"
      "(not (<= n 10))" (Sexp.to_string (List.nth literals 0));
    Alcotest.(check string) "second literal = (>= m 0)"
      "(>= m 0)" (Sexp.to_string (List.nth literals 1));
    (* Third premise was [@x64], which let-resolved is a
       [(not-or-elim _ $x51)] application; chase_to_conclusion picks
       the trailing argument [$x51 = (<= (+ n m) 10)]. *)
    Alcotest.(check string) "third literal = (<= (+ n m) 10)"
      "(<= (+ n m) 10)" (Sexp.to_string (List.nth literals 2))

let () =
  Alcotest.run "z3_proof" [
    "let_resolution", [
      Alcotest.test_case "atom passthrough" `Quick test_atom_passthrough;
      Alcotest.test_case "single binding" `Quick test_single_let;
      Alcotest.test_case "nested" `Quick test_nested_let;
      Alcotest.test_case "multi-binding parallel" `Quick test_multi_binding_let;
      Alcotest.test_case "let inside rule application"
        `Quick test_let_in_rule_application;
    ];
    "extract_proof_term", [
      Alcotest.test_case "simple envelope unwrap"
        `Quick test_extract_proof_term_simple;
      Alcotest.test_case "real Farkas proof from z3 4.16.0"
        `Quick test_extract_proof_term_real_farkas;
      Alcotest.test_case "non-envelope returns None"
        `Quick test_extract_proof_term_returns_none_on_garbage;
    ];
    "farkas_extraction", [
      Alcotest.test_case "rule head: simple integer coefs"
        `Quick test_parse_farkas_rule_head_simple;
      Alcotest.test_case "rule head: rational coefs"
        `Quick test_parse_farkas_rule_head_rationals;
      Alcotest.test_case "rule head: non-farkas arith rejected"
        `Quick test_parse_farkas_rule_head_rejects_non_farkas;
      Alcotest.test_case "find_farkas_clause on real proof"
        `Quick test_find_farkas_clause_real_proof;
      Alcotest.test_case "find_farkas_clause returns None on opaque arith"
        `Quick test_find_farkas_clause_returns_none_on_opaque;
      Alcotest.test_case "find_farkas_clause rejects mismatched arity"
        `Quick test_find_farkas_clause_mismatched_arity_rejected;
    ];
    "farkas_direct", [
      Alcotest.test_case "chase_to_conclusion"
        `Quick test_chase_to_conclusion;
      Alcotest.test_case "parse direct application"
        `Quick test_parse_farkas_direct_application;
      Alcotest.test_case "direct rejects non-false conclusion"
        `Quick test_parse_farkas_direct_rejects_non_false_conclusion;
      Alcotest.test_case "direct rejects arity mismatch"
        `Quick test_parse_farkas_direct_rejects_arity_mismatch;
      Alcotest.test_case "find_farkas_direct walks into lets"
        `Quick test_find_farkas_direct_walks_into_lets;
      Alcotest.test_case "unified find_farkas prefers clause shape"
        `Quick test_find_farkas_unified_prefers_clause;
      Alcotest.test_case "z3_farkas extracts case1 example1 (LIA)"
        `Quick test_z3_farkas_extracts_case1_example1;
    ];
    "fixture_regression", [
      Alcotest.test_case "LRA envelope unwraps + lets resolve"
        `Quick test_fixture_envelope_unwraps_lra;
      Alcotest.test_case "LRA find_farkas_clause"
        `Quick test_fixture_find_farkas_clause_lra;
      Alcotest.test_case "LRA Z3_farkas.extract + Farkas.verify"
        `Quick test_fixture_z3_farkas_extract_and_verify_lra;
      Alcotest.test_case "LIA envelope unwraps + lets resolve"
        `Quick test_fixture_envelope_unwraps_lia;
      Alcotest.test_case "LIA find_farkas_direct"
        `Quick test_fixture_find_farkas_direct_lia;
    ];
  ]

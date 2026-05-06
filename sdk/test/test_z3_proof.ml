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
  ]

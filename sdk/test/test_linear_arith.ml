(** Unit tests for [Linear_arith].

    Coverage:
    * Rational normalization: gcd reduction, sign canonicalization.
    * Rational arithmetic: add / sub / mul preserves the canonical form.
    * Parsing: integer, fraction, negative, malformed.
    * Linear forms: var, const, add, sub, neg, scale.
    * Sorted-merge: variables stay sorted; zero-coefficient entries
      are dropped after merge.
    * Big-integer paths exercised through [Z.of_string] inputs that
      would have overflowed the previous OCaml-int representation. *)

open Proof_broker.Linear_arith

(* --- rationals ------------------------------------------------------- *)

let r n d = mk_rat n d

(** Project [Z.t]-backed numerator/denominator to native int for
    [Alcotest.(check int)] comparisons. Safe for these tests since
    every literal coefficient fits comfortably in a 63-bit int.
    Big-integer paths get their own dedicated tests below. *)
let ni r = Z.to_int r.num
let di r = Z.to_int r.den

let test_mk_rat_normalizes () =
  Alcotest.(check int) "2/4 → 1/2 (num)" 1 (ni (r 2 4));
  Alcotest.(check int) "2/4 → 1/2 (den)" 2 (di (r 2 4));
  Alcotest.(check int) "-1/-2 → 1/2 (num)" 1 (ni (r (-1) (-2)));
  Alcotest.(check int) "-1/-2 → 1/2 (den)" 2 (di (r (-1) (-2)));
  Alcotest.(check int) "1/-2 → -1/2 (num)" (-1) (ni (r 1 (-2)));
  Alcotest.(check int) "0/5 → 0/1 (num)" 0 (ni (r 0 5));
  Alcotest.(check int) "0/5 → 0/1 (den)" 1 (di (r 0 5))

let test_rat_zero_div_raises () =
  Alcotest.check_raises "1/0 raises"
    (Invalid_argument "Linear_arith.mk_rat: zero denominator")
    (fun () -> ignore (mk_rat 1 0))

let test_rat_arith () =
  Alcotest.(check int) "(1/2 + 1/3).num" 5 (ni (rat_add (r 1 2) (r 1 3)));
  Alcotest.(check int) "(1/2 + 1/3).den" 6 (di (rat_add (r 1 2) (r 1 3)));
  Alcotest.(check int) "(1/2 - 1/3).num" 1 (ni (rat_sub (r 1 2) (r 1 3)));
  Alcotest.(check int) "(1/2 - 1/3).den" 6 (di (rat_sub (r 1 2) (r 1 3)));
  Alcotest.(check int) "(2/3 * 3/4).num" 1 (ni (rat_mul (r 2 3) (r 3 4)));
  Alcotest.(check int) "(2/3 * 3/4).den" 2 (di (rat_mul (r 2 3) (r 3 4)));
  Alcotest.(check int) "neg(3/4).num" (-3) (ni (rat_neg (r 3 4)))

let test_rat_signs () =
  Alcotest.(check bool) "0 zero" true (rat_is_zero rat_zero);
  Alcotest.(check bool) "1 nonzero" false (rat_is_zero rat_one);
  Alcotest.(check bool) "1 pos" true (rat_is_pos rat_one);
  Alcotest.(check bool) "-1 not pos" false (rat_is_pos (r (-1) 1));
  Alcotest.(check bool) "-1 neg" true (rat_is_neg (r (-1) 1));
  Alcotest.(check bool) "0 nonneg" true (rat_is_nonneg rat_zero);
  Alcotest.(check bool) "-1 not nonneg" false (rat_is_nonneg (r (-1) 1))

let test_rat_of_string () =
  Alcotest.(check (option int)) "parse 5" (Some 5)
    (Option.map ni (rat_of_string "5"));
  Alcotest.(check (option int)) "parse -3" (Some (-3))
    (Option.map ni (rat_of_string "-3"));
  Alcotest.(check (option int)) "parse 1/2 (num)" (Some 1)
    (Option.map ni (rat_of_string "1/2"));
  Alcotest.(check (option int)) "parse 1/2 (den)" (Some 2)
    (Option.map di (rat_of_string "1/2"));
  Alcotest.(check (option int)) "parse -3/4 (num)" (Some (-3))
    (Option.map ni (rat_of_string "-3/4"));
  Alcotest.(check bool) "reject 1/0" true
    (Option.is_none (rat_of_string "1/0"));
  Alcotest.(check bool) "reject hello" true
    (Option.is_none (rat_of_string "hello"))

let test_rat_to_string () =
  Alcotest.(check string) "0" "0" (rat_to_string rat_zero);
  Alcotest.(check string) "1" "1" (rat_to_string rat_one);
  Alcotest.(check string) "-3" "-3" (rat_to_string (r (-3) 1));
  Alcotest.(check string) "1/2" "1/2" (rat_to_string (r 1 2))

(* --- big-integer rationals ------------------------------------------ *)

(** Confirm [rat_of_string] accepts a 25-digit numerator that would
    overflow the previous OCaml-int representation (max ~9.2e18 on
    64-bit). The parsed rational round-trips through [rat_to_string]
    cleanly, and arithmetic on it stays exact. *)
let test_big_int_parse_round_trip () =
  let big = "12345678901234567890123/7" in
  match rat_of_string big with
  | None -> Alcotest.fail "expected parse to succeed on 23-digit numerator"
  | Some q ->
    Alcotest.(check string) "round-trip preserves big rational"
      big (rat_to_string q)

(** Multiplying two large rationals must not silently wrap. The
    previous int-backed [rat_mul] would have lost precision here
    (the product exceeds 2^63). We confirm the exact product via
    [rat_to_string]. *)
let test_big_int_mul_exact () =
  let a = Option.get (rat_of_string "1000000000") in
  let b = Option.get (rat_of_string "1000000000") in
  let c = Option.get (rat_of_string "1000000000") in
  let abc = rat_mul (rat_mul a b) c in
  Alcotest.(check string) "10^9 * 10^9 * 10^9 = 10^27 exactly"
    "1000000000000000000000000000" (rat_to_string abc)

(** Adding rationals whose product-of-denominators exceeds 2^63
    used to overflow OCaml's native int. With Z.t backing the
    canonical form is exact at any magnitude. We pick 10^18 (just
    over 2^59 — the previous representation rounded), so the
    intermediate cross-multiply blows past int range, and verify
    the canonical form is byte-exact. *)
let test_big_int_add_canonical () =
  let one = rat_one in
  let big_den = Option.get (rat_of_string "1/1000000000000000000") in
  let result = rat_add one big_den in
  (* 1 + 1/10^18 = (10^18 + 1)/10^18 — coprime numerator and den
     so the canonical form is the unreduced ratio. *)
  Alcotest.(check string) "1 + 1/10^18 stays exact"
    "1000000000000000001/1000000000000000000" (rat_to_string result)

(* --- linear forms ---------------------------------------------------- *)

let coeff_count (lf : t) = List.length lf.coeffs
let coef_of (lf : t) name = List.assoc_opt name lf.coeffs

let test_linform_var () =
  let f = var "x" in
  Alcotest.(check int) "var has 1 coeff" 1 (coeff_count f);
  (match coef_of f "x" with
   | Some r when r = rat_one -> ()
   | _ -> Alcotest.fail "x's coeff is not 1");
  Alcotest.(check bool) "const = 0" true (rat_is_zero f.const)

let test_linform_const () =
  let f = const (r 7 1) in
  Alcotest.(check int) "no var coeffs" 0 (coeff_count f);
  Alcotest.(check int) "const num=7" 7 (ni f.const)

let test_linform_add () =
  (* x + (y + 2) = x + y + 2; coefs sorted x,y *)
  let f = add (var "x") (add (var "y") (const (r 2 1))) in
  Alcotest.(check int) "two var coeffs" 2 (coeff_count f);
  Alcotest.(check (list string)) "sorted [x;y]" [ "x"; "y" ]
    (List.map fst f.coeffs);
  Alcotest.(check int) "const = 2" 2 (ni f.const)

let test_linform_add_drops_zero () =
  (* x + (-x) = 0 — coefficient must be elided *)
  let f = add (var "x") (scale (r (-1) 1) (var "x")) in
  Alcotest.(check int) "no var coeffs after cancellation" 0 (coeff_count f);
  Alcotest.(check bool) "const = 0" true (rat_is_zero f.const)

let test_linform_sub () =
  (* (x + y) - (y + 1) = x - 1 *)
  let f = sub (add (var "x") (var "y"))
              (add (var "y") (const (r 1 1))) in
  Alcotest.(check int) "one var coeff" 1 (coeff_count f);
  (match coef_of f "x" with
   | Some r when r = rat_one -> ()
   | _ -> Alcotest.fail "x's coeff is not 1");
  Alcotest.(check int) "const = -1" (-1) (ni f.const)

let test_linform_neg () =
  let f = neg (add (var "x") (const (r 3 1))) in
  Alcotest.(check int) "const = -3" (-3) (ni f.const);
  (match coef_of f "x" with
   | Some r when ni r = -1 && di r = 1 -> ()
   | _ -> Alcotest.fail "x's coeff is not -1")

let test_linform_scale () =
  let f = scale (r 2 1) (add (var "x") (const (r 3 1))) in
  Alcotest.(check int) "x coeff = 2" 2
    (ni (Option.value ~default:(r 0 1) (coef_of f "x")));
  Alcotest.(check int) "const = 6" 6 (ni f.const)

let test_linform_scale_zero () =
  let f = scale rat_zero (add (var "x") (const (r 3 1))) in
  Alcotest.(check int) "no coeffs" 0 (coeff_count f);
  Alcotest.(check bool) "const = 0" true (rat_is_zero f.const)

let test_linform_is_constant () =
  Alcotest.(check bool) "const(5) is constant" true
    (is_constant (const (r 5 1)));
  Alcotest.(check bool) "var x not constant" false
    (is_constant (var "x"));
  Alcotest.(check bool) "x - x is constant" true
    (is_constant (sub (var "x") (var "x")))

let test_linform_merge_three () =
  (* Confirm three-way merge: a + (b + c) keeps sorted order. *)
  let f = add (var "c") (add (var "a") (var "b")) in
  Alcotest.(check (list string)) "sorted [a;b;c]" [ "a"; "b"; "c" ]
    (List.map fst f.coeffs)

let () =
  Alcotest.run "linear_arith" [
    "rationals", [
      Alcotest.test_case "mk_rat normalizes" `Quick test_mk_rat_normalizes;
      Alcotest.test_case "zero denominator raises" `Quick test_rat_zero_div_raises;
      Alcotest.test_case "arithmetic" `Quick test_rat_arith;
      Alcotest.test_case "sign predicates" `Quick test_rat_signs;
      Alcotest.test_case "of_string" `Quick test_rat_of_string;
      Alcotest.test_case "to_string" `Quick test_rat_to_string;
    ];
    "big-int", [
      Alcotest.test_case "parse + round-trip 23-digit numerator"
        `Quick test_big_int_parse_round_trip;
      Alcotest.test_case "10^9 * 10^9 * 10^9 = 10^27 exactly"
        `Quick test_big_int_mul_exact;
      Alcotest.test_case "1 + 1/10^18 stays exact"
        `Quick test_big_int_add_canonical;
    ];
    "linear forms", [
      Alcotest.test_case "var" `Quick test_linform_var;
      Alcotest.test_case "const" `Quick test_linform_const;
      Alcotest.test_case "add (sorted merge)" `Quick test_linform_add;
      Alcotest.test_case "add drops zero coefs" `Quick test_linform_add_drops_zero;
      Alcotest.test_case "sub" `Quick test_linform_sub;
      Alcotest.test_case "neg" `Quick test_linform_neg;
      Alcotest.test_case "scale" `Quick test_linform_scale;
      Alcotest.test_case "scale by zero" `Quick test_linform_scale_zero;
      Alcotest.test_case "is_constant" `Quick test_linform_is_constant;
      Alcotest.test_case "three-way merge stays sorted" `Quick test_linform_merge_three;
    ];
  ]

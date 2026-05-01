(** Unit tests for [Farkas].

    Coverage:
    * Linearization recognizes Var / NumLit / HAdd / HSub / HMul (one
      side constant) / Neg / nested combinations; rejects non-linear.
    * compile_hypothesis handles Eq, LE.le, GE.ge, LT.lt, GT.gt,
      Not(LE.le), Not(LT.lt).
    * verify on the example1-shaped IR + cert returns Verified.
    * verify catches: unknown hypothesis (no h99 in IR), nonlinear
      hypothesis (rejects multiplication of two vars), bad
      coefficient string, negative coefficient on inequality,
      non-contradictory residual, malformed witness JSON.
    * neg_goal lookup negates the IR's goal under the LIA +1 trick. *)

open Proof_broker
module L = Linear_arith

let trivial_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LIA";
  decidable_theory = None;
}

(** Build an IR with the given hypotheses + goal; rest of the schema
    fields are filled with trivial defaults. *)
let make_ir ?(hypotheses = []) (goal_shell : Ir.shell_term) : Ir.t = {
  ir_version = "1.0";
  source_system = { name = "test"; version = "0.0" };
  tier = "goal";
  logic_classification = trivial_logic;
  goal = { shell = goal_shell; payloads = None };
  context = {
    type_vars = [];
    free_vars = [];
    hypotheses;
    library_slice = None;
  };
  type_metadata = [];
  definitional_metadata = [];
  library_provenance = [];
  user_directives = None;
}

(* --- linearization smoke tests -------------------------------------- *)

let test_linearize_var () =
  match Farkas.linearize (Ir.Var { name = "x" }) with
  | Some f ->
    Alcotest.(check int) "x has 1 coef" 1 (List.length f.coeffs);
    Alcotest.(check string) "coef name=x" "x" (fst (List.hd f.coeffs))
  | None -> Alcotest.fail "var x not linear"

let test_linearize_num_lit () =
  match Farkas.linearize (Ir.Num_lit { value = "42"; ty = "Int" }) with
  | Some f ->
    Alcotest.(check bool) "is constant" true (L.is_constant f);
    Alcotest.(check int) "const=42" 42 f.const.num
  | None -> Alcotest.fail "NumLit 42 not linear"

let test_linearize_add () =
  let t = Ir.App {
    symbol = "Int.add"; type_args = [];
    args = [ Var { name = "x" }; Num_lit { value = "5"; ty = "Int" } ];
  } in
  match Farkas.linearize t with
  | Some f ->
    Alcotest.(check int) "const=5" 5 f.const.num;
    Alcotest.(check int) "x coef=1" 1
      (List.assoc "x" f.coeffs).num
  | None -> Alcotest.fail "x + 5 not linear"

let test_linearize_const_mul () =
  let t = Ir.App {
    symbol = "HMul.hMul"; type_args = [];
    args = [ Num_lit { value = "3"; ty = "Int" }; Var { name = "x" } ];
  } in
  match Farkas.linearize t with
  | Some f ->
    Alcotest.(check int) "x coef=3" 3
      (List.assoc "x" f.coeffs).num
  | None -> Alcotest.fail "3 * x not linear"

let test_linearize_var_mul_var_rejected () =
  let t = Ir.App {
    symbol = "HMul.hMul"; type_args = [];
    args = [ Var { name = "x" }; Var { name = "y" } ];
  } in
  Alcotest.(check bool) "x * y not linear" true
    (Option.is_none (Farkas.linearize t))

let test_linearize_unknown_symbol () =
  let t = Ir.App {
    symbol = "Real.exp"; type_args = [];
    args = [ Var { name = "x" } ];
  } in
  Alcotest.(check bool) "exp(x) not linear" true
    (Option.is_none (Farkas.linearize t))

(* --- compile_hypothesis --------------------------------------------- *)

let test_compile_le () =
  let h = Ir.App {
    symbol = "LE.le"; type_args = [];
    args = [ Num_lit { value = "0"; ty = "Int" }; Var { name = "x" } ];
  } in
  match Farkas.compile_hypothesis h with
  | Ok (Le f) ->
    (* 0 <= x  ⇒  -x <= 0  ⇒  form = -x *)
    Alcotest.(check int) "x coef = -1" (-1)
      (List.assoc "x" f.coeffs).num;
    Alcotest.(check bool) "no const" true (L.rat_is_zero f.const)
  | _ -> Alcotest.fail "expected Le compilation"

let test_compile_eq () =
  let h = Ir.Eq {
    ty = "Int";
    left = App {
      symbol = "Int.add"; type_args = [];
      args = [ Var { name = "n" }; Var { name = "m" } ];
    };
    right = Num_lit { value = "10"; ty = "Int" };
  } in
  match Farkas.compile_hypothesis h with
  | Ok (Eq f) ->
    (* n + m = 10  ⇒  form = n + m - 10 *)
    Alcotest.(check int) "const = -10" (-10) f.const.num;
    Alcotest.(check int) "n coef = 1" 1 (List.assoc "n" f.coeffs).num;
    Alcotest.(check int) "m coef = 1" 1 (List.assoc "m" f.coeffs).num
  | _ -> Alcotest.fail "expected Eq compilation"

let test_compile_not_le_int () =
  (* ¬(n <= 10) over Int  ⇒  10 + 1 - n <= 0  ⇒  -n + 11 <= 0 *)
  let h = Ir.Not {
    operand = App {
      symbol = "LE.le"; type_args = [];
      args = [ Var { name = "n" }; Num_lit { value = "10"; ty = "Int" } ];
    };
  } in
  match Farkas.compile_hypothesis h with
  | Ok (Le f) ->
    Alcotest.(check int) "const = 11" 11 f.const.num;
    Alcotest.(check int) "n coef = -1" (-1)
      (List.assoc "n" f.coeffs).num
  | _ -> Alcotest.fail "expected Le compilation for ¬(n <= 10)"

let test_compile_lt () =
  (* n < 10  ⇒  n - 10 + 1 <= 0 *)
  let h = Ir.App {
    symbol = "LT.lt"; type_args = [];
    args = [ Var { name = "n" }; Num_lit { value = "10"; ty = "Int" } ];
  } in
  match Farkas.compile_hypothesis h with
  | Ok (Le f) ->
    Alcotest.(check int) "const = -9" (-9) f.const.num;
    Alcotest.(check int) "n coef = 1" 1 (List.assoc "n" f.coeffs).num
  | _ -> Alcotest.fail "expected Le compilation for n < 10"

let test_compile_lt_lra () =
  (* Under LRA, n < 10 stays strict: Lt(n - 10), no +1. *)
  let h = Ir.App {
    symbol = "LT.lt"; type_args = [];
    args = [ Var { name = "n" }; Num_lit { value = "10"; ty = "Real" } ];
  } in
  match Farkas.compile_hypothesis ~fragment:"LRA" h with
  | Ok (Lt f) ->
    Alcotest.(check int) "const = -10" (-10) f.const.num;
    Alcotest.(check int) "n coef = 1" 1 (List.assoc "n" f.coeffs).num
  | _ -> Alcotest.fail "expected Lt compilation for n < 10 under LRA"

let test_compile_not_le_lra () =
  (* Under LRA, ¬(n <= 10) ≡ 10 < n: Lt(10 - n), no +1. *)
  let h = Ir.Not {
    operand = App {
      symbol = "LE.le"; type_args = [];
      args = [ Var { name = "n" }; Num_lit { value = "10"; ty = "Real" } ];
    };
  } in
  match Farkas.compile_hypothesis ~fragment:"LRA" h with
  | Ok (Lt f) ->
    Alcotest.(check int) "const = 10" 10 f.const.num;
    Alcotest.(check int) "n coef = -1" (-1)
      (List.assoc "n" f.coeffs).num
  | _ -> Alcotest.fail "expected Lt compilation for ¬(n <= 10) under LRA"

let test_compile_not_lt_lra () =
  (* Under LRA, ¬(n < 10) ≡ 10 <= n: Le(10 - n) — same as LIA. *)
  let h = Ir.Not {
    operand = App {
      symbol = "LT.lt"; type_args = [];
      args = [ Var { name = "n" }; Num_lit { value = "10"; ty = "Real" } ];
    };
  } in
  match Farkas.compile_hypothesis ~fragment:"LRA" h with
  | Ok (Le f) ->
    Alcotest.(check int) "const = 10" 10 f.const.num;
    Alcotest.(check int) "n coef = -1" (-1)
      (List.assoc "n" f.coeffs).num
  | _ -> Alcotest.fail "expected Le compilation for ¬(n < 10) under LRA"

let test_compile_unsupported () =
  let h = Ir.Var { name = "p" } in
  Alcotest.(check bool) "Var p not a hypothesis shape" true
    (match Farkas.compile_hypothesis h with
     | Error _ -> true
     | Ok _ -> false)

(* --- verify (end-to-end on example1 shape) --------------------------- *)

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
  let goal = Ir.App {
    symbol = "LE.le"; type_args = []; args = [ n; ten ];
  } in
  make_ir ~hypotheses:[ h1; h3 ] goal

(** The cert from cert-example1-tier1-farkas.json: h1=1, h3=1, neg_goal=1. *)
let example1_witness () : Yojson.Safe.t =
  `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "h1"; "coefficient", `String "1" ];
      `Assoc [ "hypothesis", `String "h3"; "coefficient", `String "1" ];
      `Assoc [ "hypothesis", `String "neg_goal"; "coefficient", `String "1" ];
    ];
  ]

let test_verify_example1 () =
  match Farkas.verify (example1_ir ()) (example1_witness ()) with
  | Verified -> ()
  | other ->
    let detail = match other with
      | Not_contradictory { residual } ->
        Printf.sprintf "Not_contradictory(%s)" residual
      | Unknown_hypothesis { hypothesis } ->
        Printf.sprintf "Unknown(%s)" hypothesis
      | Nonlinear { hypothesis; detail } ->
        Printf.sprintf "Nonlinear(%s: %s)" hypothesis detail
      | Bad_coefficient { hypothesis; raw } ->
        Printf.sprintf "BadCoef(%s: %s)" hypothesis raw
      | Negative_coefficient { hypothesis; value } ->
        Printf.sprintf "NegCoef(%s: %s)" hypothesis value
      | Malformed_witness { detail } ->
        Printf.sprintf "Malformed(%s)" detail
      | Verified -> "Verified" (* unreachable *)
    in
    Alcotest.fail ("expected Verified, got " ^ detail)

let test_verify_unknown_hypothesis () =
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "h99"; "coefficient", `String "1" ];
    ];
  ] in
  match Farkas.verify (example1_ir ()) witness with
  | Unknown_hypothesis { hypothesis = "h99" } -> ()
  | _ -> Alcotest.fail "expected Unknown_hypothesis(h99)"

let test_verify_negative_coefficient_on_le () =
  (* h3 is an inequality (0 <= m); a negative coef on it is invalid. *)
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "h3"; "coefficient", `String "-1" ];
    ];
  ] in
  match Farkas.verify (example1_ir ()) witness with
  | Negative_coefficient { hypothesis = "h3"; _ } -> ()
  | _ -> Alcotest.fail "expected Negative_coefficient on h3"

let test_verify_negative_coefficient_on_eq_allowed () =
  (* Equality coefficients can be signed: -1 on h1 should not error
     out as Negative_coefficient. The residual won't be a
     contradiction by itself, but it should be Not_contradictory,
     not Negative_coefficient. *)
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "h1"; "coefficient", `String "-1" ];
    ];
  ] in
  match Farkas.verify (example1_ir ()) witness with
  | Not_contradictory _ -> ()
  | Negative_coefficient _ ->
    Alcotest.fail "negative coef on equality should NOT be Negative_coefficient"
  | _ -> Alcotest.fail "expected Not_contradictory"

let test_verify_not_contradictory () =
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "h1"; "coefficient", `String "1" ];
    ];
  ] in
  match Farkas.verify (example1_ir ()) witness with
  | Not_contradictory { residual } ->
    Alcotest.(check bool) "residual mentions some var" true
      (String.contains residual 'n' || String.contains residual 'm'
       || String.contains residual '-' || String.contains residual '0')
  | _ -> Alcotest.fail "expected Not_contradictory"

let test_verify_bad_coefficient () =
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "h1"; "coefficient", `String "abc" ];
    ];
  ] in
  match Farkas.verify (example1_ir ()) witness with
  | Bad_coefficient { hypothesis = "h1"; raw = "abc" } -> ()
  | _ -> Alcotest.fail "expected Bad_coefficient"

let test_verify_malformed_witness () =
  let witness : Yojson.Safe.t = `String "not an object" in
  match Farkas.verify (example1_ir ()) witness with
  | Malformed_witness _ -> ()
  | _ -> Alcotest.fail "expected Malformed_witness"

let test_verify_empty_witness () =
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [];
  ] in
  match Farkas.verify (example1_ir ()) witness with
  | Malformed_witness _ -> ()
  | _ -> Alcotest.fail "expected Malformed_witness on empty list"

let test_verify_neg_goal_lookup () =
  (* Without h1/h3, but with neg_goal=1 alone: residual is
     11 - n, a linear (non-constant) form. Should be Not_contradictory. *)
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "neg_goal"; "coefficient", `String "1" ];
    ];
  ] in
  match Farkas.verify (example1_ir ()) witness with
  | Not_contradictory _ -> ()
  | _ -> Alcotest.fail "expected Not_contradictory on neg_goal alone"

(* --- LRA strict-witness verification --------------------------------- *)

let lra_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LRA";
  decidable_theory = None;
}

(** Build an LRA-tagged IR. *)
let make_lra_ir ?(hypotheses = []) (goal_shell : Ir.shell_term) : Ir.t =
  { (make_ir ~hypotheses goal_shell) with logic_classification = lra_logic }

(** Goal: 0 <= x. h1: 0 < x (strict implies non-strict). Under LRA
    the cert {neg_goal=1, h1=1} works because ¬Goal compiles to
    [Lt(x)] (form [x < 0]) and h1 compiles to [Lt(-x)] (form
    [-x < 0]); they cancel to residual 0 with [has_strict], which
    is the LRA contradiction. LIA would also verify (residual=2
    after the +1 trick), but via a different residual. *)
let lra_strict_pair_ir () =
  let x = Ir.Var { name = "x" } in
  let zero = Ir.Num_lit { value = "0"; ty = "Real" } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = App { symbol = "LT.lt"; type_args = []; args = [ zero; x ] };
  } in
  make_lra_ir
    ~hypotheses:[ h1 ]
    (App { symbol = "LE.le"; type_args = []; args = [ zero; x ] })

let test_verify_lra_strict_residual_zero () =
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "neg_goal"; "coefficient", `String "1" ];
      `Assoc [ "hypothesis", `String "h1";       "coefficient", `String "1" ];
    ];
  ] in
  match Farkas.verify (lra_strict_pair_ir ()) witness with
  | Verified -> ()
  | Not_contradictory { residual } ->
    Alcotest.fail (Printf.sprintf
      "expected Verified under LRA strict, got Not_contradictory(%s)"
      residual)
  | _ -> Alcotest.fail "expected Verified under LRA strict"

let test_verify_lra_strict_loose_mix () =
  (* Goal: x <= 1. h1: x <= 1. Under LRA, ¬Goal is strict
     (Lt(1 - x), no +1), and the cert {neg_goal=1, h1=1} yields
     residual 0 with one positively-weighted strict witness — LRA
     verdict is Verified. *)
  let x = Ir.Var { name = "x" } in
  let one = Ir.Num_lit { value = "1"; ty = "Real" } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = App { symbol = "LE.le"; type_args = []; args = [ x; one ] };
  } in
  let ir = make_lra_ir ~hypotheses:[ h1 ]
    (App { symbol = "LE.le"; type_args = []; args = [ x; one ] })
  in
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "neg_goal"; "coefficient", `String "1" ];
      `Assoc [ "hypothesis", `String "h1";       "coefficient", `String "1" ];
    ];
  ] in
  match Farkas.verify ir witness with
  | Verified -> ()
  | _ -> Alcotest.fail "expected Verified for LRA strict + loose"

let test_verify_lra_rejects_real_counterexample () =
  (* Goal: x <= 0, h1: x = 1/2. Over R the goal is FALSE under h1
     (1/2 <= 0 is false), so any cert claiming to prove it must be
     rejected. The LIA +1 trick would unsoundly accept this
     (residual = 1/2 > 0). LRA strict mode keeps the negation
     strict: residual = -1/2 with a positively-weighted strict
     witness still needs >= 0, so we get Not_contradictory. *)
  let x = Ir.Var { name = "x" } in
  let zero = Ir.Num_lit { value = "0"; ty = "Real" } in
  let half = Ir.Num_lit { value = "1/2"; ty = "Real" } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = Eq { ty = "Real"; left = x; right = half };
  } in
  let ir = make_lra_ir ~hypotheses:[ h1 ]
    (App { symbol = "LE.le"; type_args = []; args = [ x; zero ] })
  in
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "neg_goal"; "coefficient", `String "1" ];
      `Assoc [ "hypothesis", `String "h1";       "coefficient", `String "1" ];
    ];
  ] in
  match Farkas.verify ir witness with
  | Not_contradictory _ -> ()
  | Verified -> Alcotest.fail
    "LRA must reject the LIA +1-trick cert against a real counterexample"
  | _ -> Alcotest.fail "expected Not_contradictory under LRA"

let test_verify_lra_loose_only_matches_lia () =
  (* No strict witnesses involved: LRA mode behaves exactly like
     LIA. Goal: x < 2 in LRA, h1: x <= 1. ¬Goal is loose under both
     fragments (¬(x < y) ≡ y <= x). Residual = 1 > 0 — same path
     as LIA. *)
  let x = Ir.Var { name = "x" } in
  let one = Ir.Num_lit { value = "1"; ty = "Real" } in
  let two = Ir.Num_lit { value = "2"; ty = "Real" } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = App { symbol = "LE.le"; type_args = []; args = [ x; one ] };
  } in
  let ir = make_lra_ir ~hypotheses:[ h1 ]
    (App { symbol = "LT.lt"; type_args = []; args = [ x; two ] })
  in
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "neg_goal"; "coefficient", `String "1" ];
      `Assoc [ "hypothesis", `String "h1";       "coefficient", `String "1" ];
    ];
  ] in
  match Farkas.verify ir witness with
  | Verified -> ()
  | _ -> Alcotest.fail "expected Verified for LRA loose-only cert"

let test_verify_lra_strict_negative_coef_rejected () =
  (* A negative coefficient on a Lt witness is unsound for the same
     reason it's unsound on a Le witness. *)
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "h1"; "coefficient", `String "-1" ];
    ];
  ] in
  match Farkas.verify (lra_strict_pair_ir ()) witness with
  | Negative_coefficient { hypothesis = "h1"; _ } -> ()
  | _ -> Alcotest.fail "expected Negative_coefficient on strict h1"

let test_verify_with_rational_coefs () =
  (* Same Farkas combination, scaled by 2: coefs 2, 2, 2 ⇒ residual 2 ⇒ contradiction. *)
  let witness : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "h1"; "coefficient", `String "2" ];
      `Assoc [ "hypothesis", `String "h3"; "coefficient", `String "2" ];
      `Assoc [ "hypothesis", `String "neg_goal"; "coefficient", `String "2" ];
    ];
  ] in
  Alcotest.(check bool) "scaled cert verifies" true
    (Farkas.verify (example1_ir ()) witness = Verified);
  (* Same with 1/2 — residual is 1/2 > 0, still verifies. *)
  let half : Yojson.Safe.t = `Assoc [
    "coefficients", `List [
      `Assoc [ "hypothesis", `String "h1"; "coefficient", `String "1/2" ];
      `Assoc [ "hypothesis", `String "h3"; "coefficient", `String "1/2" ];
      `Assoc [ "hypothesis", `String "neg_goal"; "coefficient", `String "1/2" ];
    ];
  ] in
  Alcotest.(check bool) "fractional cert verifies" true
    (Farkas.verify (example1_ir ()) half = Verified)

let () =
  Alcotest.run "farkas" [
    "linearize", [
      Alcotest.test_case "var" `Quick test_linearize_var;
      Alcotest.test_case "num_lit" `Quick test_linearize_num_lit;
      Alcotest.test_case "add" `Quick test_linearize_add;
      Alcotest.test_case "const * var" `Quick test_linearize_const_mul;
      Alcotest.test_case "var * var rejected" `Quick test_linearize_var_mul_var_rejected;
      Alcotest.test_case "unknown symbol rejected" `Quick test_linearize_unknown_symbol;
    ];
    "compile_hypothesis", [
      Alcotest.test_case "LE.le" `Quick test_compile_le;
      Alcotest.test_case "Eq" `Quick test_compile_eq;
      Alcotest.test_case "Not(LE.le)" `Quick test_compile_not_le_int;
      Alcotest.test_case "LT.lt" `Quick test_compile_lt;
      Alcotest.test_case "LT.lt under LRA" `Quick test_compile_lt_lra;
      Alcotest.test_case "Not(LE.le) under LRA" `Quick test_compile_not_le_lra;
      Alcotest.test_case "Not(LT.lt) under LRA" `Quick test_compile_not_lt_lra;
      Alcotest.test_case "unsupported shape" `Quick test_compile_unsupported;
    ];
    "verify", [
      Alcotest.test_case "example1 cert verifies" `Quick test_verify_example1;
      Alcotest.test_case "unknown hypothesis" `Quick test_verify_unknown_hypothesis;
      Alcotest.test_case "negative coef on inequality" `Quick test_verify_negative_coefficient_on_le;
      Alcotest.test_case "negative coef on equality OK" `Quick test_verify_negative_coefficient_on_eq_allowed;
      Alcotest.test_case "not contradictory" `Quick test_verify_not_contradictory;
      Alcotest.test_case "bad coefficient string" `Quick test_verify_bad_coefficient;
      Alcotest.test_case "malformed witness" `Quick test_verify_malformed_witness;
      Alcotest.test_case "empty coefficient list" `Quick test_verify_empty_witness;
      Alcotest.test_case "neg_goal alone is non-contradictory" `Quick test_verify_neg_goal_lookup;
      Alcotest.test_case "rational coefficients" `Quick test_verify_with_rational_coefs;
    ];
    "verify (LRA strict)", [
      Alcotest.test_case "two strict witnesses, residual 0"
        `Quick test_verify_lra_strict_residual_zero;
      Alcotest.test_case "strict ¬Goal + loose hypothesis"
        `Quick test_verify_lra_strict_loose_mix;
      Alcotest.test_case "rejects LIA +1-trick on real counterexample"
        `Quick test_verify_lra_rejects_real_counterexample;
      Alcotest.test_case "loose-only LRA cert verifies"
        `Quick test_verify_lra_loose_only_matches_lia;
      Alcotest.test_case "negative coef on Lt rejected"
        `Quick test_verify_lra_strict_negative_coef_rejected;
    ];
  ]

(** End-to-end tests for [Adapter_z3].

    These tests spawn the z3 binary and require it to be on PATH.
    If z3 is not available, every test logs a skip and the suite
    exits 0 — CI without z3 stays green, but a developer wanting
    to actually exercise the adapter is expected to have z3
    installed.

    Coverage parallels [test_adapter_cvc4]: provable LIA goal
    yields a Tier 1 farkas cert (internal closer fires on z3's
    [unsat] verdict), beyond-closer-bound goals fall back to the
    Tier 0 oracle, sat returns [Sat_returned], unsupported IR
    surfaces [Unsupported_ir], and a minted cert verifies through
    the envelope. *)

open Proof_broker

let z3_available () : bool =
  Sys.command "which z3 > /dev/null 2>&1" = 0

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

let with_z3 f =
  if not (z3_available ()) then
    Printf.printf "[skip] z3 not on PATH\n"
  else f ()

let test_dispatch_unsat_mints_farkas_cert () =
  with_z3 @@ fun () ->
  let ir = example1_ir () in
  match Adapter_z3.dispatch ir with
  | Cert cert ->
    (* z3 has no proof trace consumed here (Phase 2.2 scope); the
       internal Farkas closer runs after z3's [unsat] verdict and
       discovers a witness for this LIA-Farkas-shaped goal, so the
       cert is upgraded from Tier 0 oracle to Tier 1 farkas. *)
    Alcotest.(check int) "tier=1" 1 cert.tier;
    Alcotest.(check string) "format=farkas" "farkas" cert.format;
    Alcotest.(check string) "backend=z3" "z3" cert.backend.name;
    let dispatch_hash = Hash.sha256_of_json (Codec.to_json ir) in
    Alcotest.(check string) "dispatch_context_hash addresses ir"
      dispatch_hash cert.dispatch_context_hash;
    let payload_kind = Certificate.payload_tier cert.payload in
    Alcotest.(check int) "payload encoding tier 1" 1 payload_kind;
    Alcotest.(check string) "fragment = LIA" "LIA"
      cert.refinement_record.fragment
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s: %s)"
         (Adapter.kind_of_failure f)
         (Adapter.detail_of_failure f))

(** When the internal closer can't find a Farkas witness within
    its bound, z3 falls back to the Tier 0 oracle cert. Same shape
    as the cvc4 test: [7n <= 6, n >= 1 ⊢ False] needs [c=(1, 7)]
    to close, exceeding the search box. z3 still says [unsat], so
    the dispatcher falls through the closer-fail branch into the
    oracle path. *)
let test_dispatch_unsat_beyond_closer_bound_falls_back_to_oracle () =
  with_z3 @@ fun () ->
  let n : Ir.shell_term = Var { name = "n" } in
  let one : Ir.shell_term = Num_lit { value = "1"; ty = "Int" } in
  let six : Ir.shell_term = Num_lit { value = "6"; ty = "Int" } in
  let seven : Ir.shell_term = Num_lit { value = "7"; ty = "Int" } in
  let seven_n : Ir.shell_term =
    App { symbol = "Int.mul"; type_args = []; args = [ seven; n ] }
  in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = App { symbol = "LE.le"; type_args = []; args = [ seven_n; six ] };
  } in
  let h2 : Ir.hypothesis = {
    name = "h2";
    shell = App { symbol = "LE.le"; type_args = []; args = [ one; n ] };
  } in
  let ir = make_ir
    ~free_vars:[ { name = "n"; ty = "Int" } ]
    ~hypotheses:[ h1; h2 ]
    (Const { name = "False" })
  in
  match Adapter_z3.dispatch ir with
  | Cert cert ->
    Alcotest.(check int) "tier=0" 0 cert.tier;
    Alcotest.(check string) "format=oracle" "oracle" cert.format;
    Alcotest.(check string) "backend=z3" "z3" cert.backend.name
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s: %s)"
         (Adapter.kind_of_failure f)
         (Adapter.detail_of_failure f))

let test_dispatch_sat_returns_failure () =
  with_z3 @@ fun () ->
  (* No hypotheses, goal n <= 10. n is unconstrained, so n=11 satisfies
     ¬(n <= 10), and z3 returns sat. *)
  let n = Ir.Var { name = "n" } in
  let ten = Ir.Num_lit { value = "10"; ty = "Int" } in
  let ir = make_ir
    ~free_vars:[ { name = "n"; ty = "Int" } ]
    (App { symbol = "LE.le"; type_args = []; args = [ n; ten ] })
  in
  match Adapter_z3.dispatch ir with
  | Failed Sat_returned -> ()
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Sat_returned, got %s"
         (Adapter.kind_of_failure f))
  | Cert _ ->
    Alcotest.fail "expected Sat_returned, got Cert (goal is not provable!)"

let test_dispatch_unsupported_ir () =
  (* Quantifier in the goal — Smtlib serializer rejects, dispatch
     should surface as Unsupported_ir. Doesn't actually need z3. *)
  let ir = make_ir
    (Forall { var = "x"; ty = "Int"; body = Var { name = "x" } })
  in
  match Adapter_z3.dispatch ir with
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
  with_z3 @@ fun () ->
  let ir = example1_ir () in
  match Adapter_z3.dispatch ir with
  | Cert cert ->
    (* With the internal Farkas closer wired in, z3 mints Tier 1 on
       this Farkas-shaped goal. The cert's dispatch_context_hash
       matches the IR, the envelope checks pass, and [Farkas.verify]
       re-checks the witness independently of z3 — so [verify]
       returns [Verified_farkas]. *)
    (match Verifier.verify cert ir with
     | Verified_farkas -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf "expected Verified_farkas, got %s"
            (Verifier.kind_of_reason other)))
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s)"
         (Adapter.kind_of_failure f))

(** Two-hypothesis LRA Farkas: [x >= 5, x <= 3 ⊢ False]. This shape
    triggers z3's clause-introducing th-lemma form
    [((_ th-lemma arith farkas 1 1) (or (not (<= x 3.0)) (not (>= x
    5.0))))], which is what [Z3_farkas.extract] handles natively.
    The minted cert's witness is built from z3's emitted
    coefficients, not from [Farkas_search] — and re-verifies
    independently via [Farkas.verify]. *)
let test_dispatch_lra_two_hyp_uses_native_extraction () =
  with_z3 @@ fun () ->
  let lra_logic : Ir.logic_classification = {
    order = "first_order";
    features_used = [];
    first_order_fragment = "LRA";
    decidable_theory = None;
  } in
  let x = Ir.Var { name = "x" } in
  (* Real-typed integer-form literals: Linear_arith.rat_of_string
     handles "3" / "5" exactly, but not the SMT-LIB-printed "3.0" /
     "5.0" forms. See [test_smtlib] for matching round-trip. *)
  let three = Ir.Num_lit { value = "3"; ty = "Real" } in
  let five = Ir.Num_lit { value = "5"; ty = "Real" } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = App { symbol = ">="; type_args = []; args = [ x; five ] };
  } in
  let h2 : Ir.hypothesis = {
    name = "h2";
    shell = App { symbol = "<="; type_args = []; args = [ x; three ] };
  } in
  let ir : Ir.t = {
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
  } in
  match Adapter_z3.dispatch ir with
  | Cert cert ->
    Alcotest.(check int) "tier=1" 1 cert.tier;
    Alcotest.(check string) "format=farkas" "farkas" cert.format;
    Alcotest.(check string) "fragment=LRA" "LRA"
      cert.refinement_record.fragment;
    (match Verifier.verify cert ir with
     | Verified_farkas -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf "expected Verified_farkas, got %s"
            (Verifier.kind_of_reason other)))
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s: %s)"
         (Adapter.kind_of_failure f)
         (Adapter.detail_of_failure f))

let () =
  Alcotest.run "adapter_z3" [
    "dispatch", [
      Alcotest.test_case "unsat on Farkas-shape mints Tier 1 farkas cert"
        `Quick test_dispatch_unsat_mints_farkas_cert;
      Alcotest.test_case "unsat beyond closer bound falls back to Tier 0 oracle"
        `Quick test_dispatch_unsat_beyond_closer_bound_falls_back_to_oracle;
      Alcotest.test_case "sat returns Sat_returned"
        `Quick test_dispatch_sat_returns_failure;
      Alcotest.test_case "unsupported IR shape"
        `Quick test_dispatch_unsupported_ir;
      Alcotest.test_case "minted cert verifies through envelope"
        `Quick test_minted_cert_passes_envelope_verifier;
      Alcotest.test_case "LRA two-hyp Farkas uses native extraction"
        `Quick test_dispatch_lra_two_hyp_uses_native_extraction;
    ];
  ]

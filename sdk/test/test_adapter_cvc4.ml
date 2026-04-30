(** End-to-end tests for [Adapter_cvc4].

    These tests spawn the cvc4 binary and require it to be on PATH.
    If cvc4 is not available, every test logs a skip and the suite
    exits 0 — CI without cvc4 stays green, but a developer wanting
    to actually exercise the adapter is expected to have cvc4
    installed.

    Coverage:
    * Provable LIA goal (example1 shape) → [Cert _] with Tier 0
      oracle payload, refinement_record records the
      method_specializations the SMT-LIB serializer applied.
    * Satisfiable goal (no contradiction) → [Failed Sat_returned].
    * Goal with unsupported shape (a quantifier) → [Failed
      (Unsupported_ir _)].
    * Cert addresses the IR by hash: re-running [Verifier.verify]
      on the result returns [Tier_check_deferred] (envelope
      verified, no Tier 0 soundness check exists). *)

open Proof_broker

let cvc4_available () : bool =
  Sys.command "which cvc4 > /dev/null 2>&1" = 0

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

let with_cvc4 f =
  if not (cvc4_available ()) then
    Printf.printf "[skip] cvc4 not on PATH\n"
  else f ()

let test_dispatch_unsat_mints_oracle_cert () =
  with_cvc4 @@ fun () ->
  let ir = example1_ir () in
  match Adapter_cvc4.dispatch ir with
  | Cert cert ->
    Alcotest.(check int) "tier=0" 0 cert.tier;
    Alcotest.(check string) "format=oracle" "oracle" cert.format;
    Alcotest.(check string) "backend=cvc4" "cvc4" cert.backend.name;
    let dispatch_hash = Hash.sha256_of_json (Codec.to_json ir) in
    Alcotest.(check string) "dispatch_context_hash addresses ir"
      dispatch_hash cert.dispatch_context_hash;
    let payload_kind = Certificate.payload_tier cert.payload in
    Alcotest.(check int) "payload encoding tier 0" 0 payload_kind;
    Alcotest.(check string) "fragment = LIA" "LIA"
      cert.refinement_record.fragment;
    Alcotest.(check bool) "refinement_record has at least 2 method specs"
      true
      (List.length cert.refinement_record.specializations >= 2)
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s: %s)"
         (Adapter.kind_of_failure f)
         (Adapter.detail_of_failure f))

let test_dispatch_sat_returns_failure () =
  with_cvc4 @@ fun () ->
  (* No hypotheses, goal n <= 10. n is unconstrained, so n=11 satisfies
     ¬(n <= 10), and cvc4 returns sat. *)
  let n = Ir.Var { name = "n" } in
  let ten = Ir.Num_lit { value = "10"; ty = "Int" } in
  let ir = make_ir
    ~free_vars:[ { name = "n"; ty = "Int" } ]
    (App { symbol = "LE.le"; type_args = []; args = [ n; ten ] })
  in
  match Adapter_cvc4.dispatch ir with
  | Failed Sat_returned -> ()
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Sat_returned, got %s"
         (Adapter.kind_of_failure f))
  | Cert _ ->
    Alcotest.fail "expected Sat_returned, got Cert (goal is not provable!)"

let test_dispatch_unsupported_ir () =
  (* Quantifier in the goal — Smtlib serializer rejects, dispatch
     should surface as Unsupported_ir. Doesn't actually need cvc4. *)
  let ir = make_ir
    (Forall { var = "x"; ty = "Int"; body = Var { name = "x" } })
  in
  match Adapter_cvc4.dispatch ir with
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
  with_cvc4 @@ fun () ->
  let ir = example1_ir () in
  match Adapter_cvc4.dispatch ir with
  | Cert cert ->
    (* The minted cert's dispatch_context_hash should match the IR
       it was minted against, so envelope verification passes;
       there's no Tier 0 soundness check, so [verify] returns
       [Tier_check_deferred 0]. Both outcomes count as "ok" in the
       FFI semantics. *)
    (match Verifier.verify cert ir with
     | Tier_check_deferred { tier = 0 } -> ()
     | other ->
       Alcotest.fail
         (Printf.sprintf "expected Tier_check_deferred(0), got %s"
            (Verifier.kind_of_reason other)))
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s)"
         (Adapter.kind_of_failure f))

let () =
  Alcotest.run "adapter_cvc4" [
    "dispatch", [
      Alcotest.test_case "unsat mints Tier 0 oracle cert"
        `Quick test_dispatch_unsat_mints_oracle_cert;
      Alcotest.test_case "sat returns Sat_returned"
        `Quick test_dispatch_sat_returns_failure;
      Alcotest.test_case "unsupported IR shape"
        `Quick test_dispatch_unsupported_ir;
      Alcotest.test_case "minted cert verifies through envelope"
        `Quick test_minted_cert_passes_envelope_verifier;
    ];
  ]

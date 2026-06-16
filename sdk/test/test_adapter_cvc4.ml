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

let test_dispatch_unsat_mints_farkas_cert () =
  with_cvc4 @@ fun () ->
  let ir = example1_ir () in
  match Adapter_cvc4.dispatch ir with
  | Cert cert ->
    (* cvc4 has no proof trace; the internal Farkas closer runs
       after cvc4's [unsat] verdict and discovers a witness for
       this LIA-Farkas-shaped goal, so the cert is upgraded from
       Tier 0 oracle to Tier 1 farkas. *)
    Alcotest.(check int) "tier=1" 1 cert.tier;
    Alcotest.(check string) "format=farkas" "farkas" cert.format;
    Alcotest.(check string) "backend=cvc4" "cvc4" cert.backend.name;
    let dispatch_hash = Hash.sha256_of_json (Codec.to_json ir) in
    Alcotest.(check string) "dispatch_context_hash addresses ir"
      dispatch_hash cert.dispatch_context_hash;
    let payload_kind = Certificate.payload_tier cert.payload in
    Alcotest.(check int) "payload encoding tier 1" 1 payload_kind;
    Alcotest.(check string) "fragment = LIA" "LIA"
      cert.refinement_record.fragment;
    (* The hand-built IR has no metadata, so refinement produces no
       specializations; that's correct for an IR already in LIA
       primitive shape. The metadata-rich path is exercised in the
       fixture-based test below. *)
    Alcotest.(check int) "refinement_record empty for primitive IR" 0
      (List.length cert.refinement_record.specializations)
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s: %s)"
         (Adapter.kind_of_failure f)
         (Adapter.detail_of_failure f))

(** When the internal closer can't find a Farkas witness within
    its bound, cvc4 falls back to the Tier 0 oracle cert. The
    canonical out-of-bound shape has a coefficient ratio above the
    closer's default [bound = 3]: [7n <= 6, n >= 1 ⊢ False] needs
    [c=(1, 7)] to close, which exceeds the search box. cvc4 still
    says [unsat] (it's a tiny LIA problem), so the dispatcher falls
    through the closer-fail branch into the oracle path. *)
let test_dispatch_unsat_beyond_closer_bound_falls_back_to_oracle () =
  with_cvc4 @@ fun () ->
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
  match Adapter_cvc4.dispatch ir with
  | Cert cert ->
    Alcotest.(check int) "tier=0" 0 cert.tier;
    Alcotest.(check string) "format=oracle" "oracle" cert.format
  | Failed f ->
    Alcotest.fail
      (Printf.sprintf "expected Cert, got Failed(%s: %s)"
         (Adapter.kind_of_failure f)
         (Adapter.detail_of_failure f))

(** Read [example1-lia-typeclass.json] (alpha-typed, full
    metadata) and dispatch it through cvc4. The refinement pass
    should commit to alpha → Int from type_metadata's
    [embeds_into:Int_for_universal_LIA] tag, then SMT-LIB
    serialization succeeds (it would have rejected [alpha]
    without refinement), and cvc4 returns unsat. The cert's
    refinement_record gets type_specialization (alpha → Int) +
    method_specialization entries (HAdd.hAdd → +, LE.le → <=,
    OfNat.ofNat → literal). *)
let test_dispatch_on_typeclass_fixture () =
  with_cvc4 @@ fun () ->
  let path = Filename.concat (Sys.getcwd ())
    "../../../../examples/example1-lia-typeclass.json" in
  let raw = In_channel.with_open_text path In_channel.input_all in
  let ir = Codec.of_json (Yojson.Safe.from_string raw) in
  match Adapter_cvc4.dispatch ir with
  | Cert cert ->
    let kinds =
      List.map
        (fun (s : Refinement_record.specialization) ->
          Refinement_record.specialization_kind_to_string s.kind)
        cert.refinement_record.specializations
    in
    Alcotest.(check bool) "type_specialization recorded" true
      (List.mem "type_specialization" kinds);
    Alcotest.(check bool) "method_specialization recorded" true
      (List.mem "method_specialization" kinds);
    let alpha_spec =
      List.find_opt
        (fun (s : Refinement_record.specialization) ->
          s.kind = Type_specialization && s.source = "alpha")
        cert.refinement_record.specializations
    in
    (match alpha_spec with
     | Some s ->
       Alcotest.(check string) "alpha → Int" "Int" s.target;
       Alcotest.(check bool) "alpha has soundness witness" true
         (Option.is_some s.soundness_witness)
     | None ->
       Alcotest.fail "expected alpha → Int type_specialization")
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
  (* Lambda in the goal — Smtlib serializer rejects, dispatch
     should surface as Unsupported_ir. Doesn't actually need cvc4. *)
  let ir = make_ir
    (Lambda { binders = [ { var = "x"; ty = "Int" } ]; body = Var { name = "x" } })
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
    (* With the internal Farkas closer wired in, cvc4 mints Tier 1
       on this Farkas-shaped goal. The cert's dispatch_context_hash
       matches the IR, the envelope checks pass, and [Farkas.verify]
       re-checks the witness independently of cvc4 — so [verify]
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

let () =
  Alcotest.run "adapter_cvc4" [
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
      Alcotest.test_case "typeclass fixture refines + dispatches"
        `Quick test_dispatch_on_typeclass_fixture;
    ];
  ]

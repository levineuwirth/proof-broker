(** End-to-end tests for [Adapter_vampire].

    Tests that spawn the [vampire] binary require it on PATH; if it
    is absent they log a skip and the suite still exits 0 (CI
    without Vampire stays green, mirroring [test_adapter_z3]'s z3
    gate). The serializer-boundary tests need no binary — they
    assert the typed [Unsupported_ir] failure the adapter returns
    before it ever spawns a process. *)

open Proof_broker

let vampire_available () : bool =
  Sys.command "which vampire > /dev/null 2>&1" = 0

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

(* --- serializer-boundary failures (no binary needed) ----------------- *)

let test_unsupported_ir_num_lit () =
  (* Num_lit is out of M1 Vampire scope; the adapter must surface a
     typed Unsupported_ir, not spawn vampire. *)
  let ir = make_ir (Num_lit { value = "3"; ty = "Int" }) in
  match Adapter_vampire.dispatch
          ~rewrite_trace_hash:(Pipeline.identity_trace_hash ir)
          ir with
  | Failed (Unsupported_ir { kind; _ }) ->
    Alcotest.(check string) "bad_literal kind" "bad_literal" kind
  | _ -> Alcotest.fail "expected Unsupported_ir for Num_lit goal"

let test_unsupported_ir_undeclared_thf () =
  (* example2-as-written shape: undeclared higher-order symbol. *)
  let ir =
    make_ir ~logic:ho_logic
      ~free_vars:[ { name = "g"; ty = "Nat -> Nat" };
                   { name = "P"; ty = "(Nat -> Nat) -> Prop" } ]
      (App { symbol = "P"; type_args = [];
             args = [ App { symbol = "Function.comp"; type_args = [];
                            args = [ Var { name = "g" } ] } ] })
  in
  match Adapter_vampire.dispatch
          ~rewrite_trace_hash:(Pipeline.identity_trace_hash ir)
          ir with
  | Failed (Unsupported_ir { kind; _ }) ->
    Alcotest.(check string) "unsupported_symbol kind"
      "unsupported_symbol" kind
  | _ -> Alcotest.fail "expected Unsupported_ir for undeclared THF symbol"

(* --- live dispatch (vampire on PATH) --------------------------------- *)

(* Provable FOF: from [p(a)] and [! x. p(x) => q(x)], conclude
   [q(a)]. Vampire returns SZS status Theorem. *)
let provable_ir () =
  make_ir
    ~hypotheses:[
      { name = "h1";
        shell = App { symbol = "p"; type_args = [];
                      args = [ Var { name = "a" } ] } };
      { name = "h2";
        shell = Forall {
          var = "x"; ty = "Nat";
          body = Implies {
            antecedent = App { symbol = "p"; type_args = [];
                               args = [ Var { name = "x" } ] };
            consequent = App { symbol = "q"; type_args = [];
                               args = [ Var { name = "x" } ] } } } };
    ]
    (App { symbol = "q"; type_args = []; args = [ Var { name = "a" } ] })

(* Non-theorem: [p(a)] alone does not entail [q(a)]; Vampire
   reports CounterSatisfiable. *)
let non_theorem_ir () =
  make_ir
    ~hypotheses:[
      { name = "h1";
        shell = App { symbol = "p"; type_args = [];
                      args = [ Var { name = "a" } ] } };
    ]
    (App { symbol = "q"; type_args = []; args = [ Var { name = "a" } ] })

let test_provable_tier3 () =
  if not (vampire_available ()) then
    Alcotest.skip ()
  else
    match (let __ir = (provable_ir ()) in
          Adapter_vampire.dispatch
            ~rewrite_trace_hash:(Pipeline.identity_trace_hash __ir) __ir) with
    | Cert c ->
      Alcotest.(check string) "backend vampire" "vampire" c.backend.name;
      (* The whole point of M2: this provable FOF goal's Vampire
         derivation passes the provenance gate, so the adapter
         mints Tier 3 (tstp-fof), not the Tier-0 fallback. *)
      Alcotest.(check int) "tier 3" 3 c.tier;
      Alcotest.(check string) "format tstp-fof" "tstp-fof" c.format;
      (match c.payload with
       | Tier3_proof_trace { trace_format; trace_dialect_features; _ } ->
         Alcotest.(check string) "trace_format" "tstp-fof" trace_format;
         Alcotest.(check bool) "honest provenance-only tag present" true
           (match trace_dialect_features with
            | Some fs -> List.mem "provenance_verified_only" fs
            | None -> false)
       | _ -> Alcotest.fail "expected Tier3_proof_trace payload");
      (* Cert must round-trip through the codec. *)
      let j = Certificate.to_json c in
      let c2 = Certificate.of_json j in
      Alcotest.(check int) "round-trip tier" 3 c2.tier;
      (* And re-verify exactly as Lean's runVerifyCertificate does:
         Verifier.verify (mint → verify round-trip) must accept it
         as Verified_tier3_provenance. *)
      (match Verifier.verify c (provable_ir ()) with
       | Verified_tier3_provenance -> ()
       | r ->
         Alcotest.fail
           ("Verifier.verify on minted cert = "
            ^ Verifier.kind_of_reason r))
    | Failed _ -> Alcotest.fail "expected a cert for a provable goal"

let test_non_theorem_sat () =
  if not (vampire_available ()) then
    Alcotest.skip ()
  else
    match (let __ir = (non_theorem_ir ()) in
          Adapter_vampire.dispatch
            ~rewrite_trace_hash:(Pipeline.identity_trace_hash __ir) __ir) with
    | Failed Sat_returned -> ()
    | Failed f ->
      Alcotest.fail
        ("expected Sat_returned, got " ^ Adapter.kind_of_failure f)
    | Cert _ -> Alcotest.fail "non-theorem must not yield a cert"

let () =
  Alcotest.run "adapter_vampire"
    [
      ( "serializer-boundary",
        [ Alcotest.test_case "num_lit → unsupported_ir" `Quick
            test_unsupported_ir_num_lit;
          Alcotest.test_case "undeclared THF → unsupported_ir" `Quick
            test_unsupported_ir_undeclared_thf ] );
      ( "live",
        [ Alcotest.test_case "provable → Tier 3" `Quick
            test_provable_tier3;
          Alcotest.test_case "non-theorem → Sat" `Quick
            test_non_theorem_sat ] );
    ]

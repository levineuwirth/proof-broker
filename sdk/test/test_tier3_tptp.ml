(** Unit tests for [Tier3_tptp] (provenance + structure verifier).

    The positive case is the verbatim Vampire 5.0.1 derivation from
    [test_tptp_proof]; the negative cases are minimal mutations of
    it, each isolating one soundness guard:
      * a leaf citing an input we never sent (smuggled axiom),
      * a prover-[introduced] formula inside the refutation,
      * an inference rule outside the reviewed allowlist,
      * the conjecture consumed by a non-negation inference,
      * no [$false] sink,
      * a dangling parent reference. *)

open Proof_broker

let base =
  "% SZS output start Proof for q\n\
   fof(f1,axiom,(\n  p(a)),\n  file('/tmp/q.p',h1)).\n\
   fof(f2,axiom,(\n  ! [X0] : (p(X0) => q(X0))),\n  file('/tmp/q.p',h2)).\n\
   fof(f3,conjecture,(\n  q(a)),\n  file('/tmp/q.p',goal)).\n\
   fof(f4,negated_conjecture,(\n  ~q(a)),\n\
   \  inference(negated_conjecture,[status(cth)],[f3])).\n\
   fof(f7,plain,(\n  p(a)),\n  inference(cnf_transformation,[],[f1])).\n\
   fof(f8,plain,(\n  ( ! [X0] : (~p(X0) | q(X0)) )),\n\
   \  inference(cnf_transformation,[],[f2])).\n\
   fof(f9,plain,(\n  ~q(a)),\n  inference(cnf_transformation,[],[f4])).\n\
   fof(f10,plain,(\n  q(a)),\n  inference(resolution,[],[f8,f7])).\n\
   fof(f11,plain,(\n  $false),\n\
   \  inference(forward_subsumption_resolution,[],[f10,f9])).\n\
   % SZS output end Proof for q\n"

let replace ~old ~by s = Str.global_replace (Str.regexp_string old) by s

let trivial_logic : Ir.logic_classification = {
  order = "first_order"; features_used = [];
  first_order_fragment = "FOL"; decidable_theory = None;
}

(* IR with hypotheses named h1, h2 and goal q(a) — the names the
   verifier expects to see at the [file(_, NAME)] leaves. *)
let ir () : Ir.t = {
  ir_version = "1.0";
  source_system = { name = "test"; version = "0.0" };
  tier = "goal";
  logic_classification = trivial_logic;
  goal = { shell = App { symbol = "q"; type_args = [];
                         args = [ Var { name = "a" } ] };
           payloads = None };
  context = {
    type_vars = []; free_vars = [];
    hypotheses = [
      { name = "h1";
        shell = App { symbol = "p"; type_args = [];
                      args = [ Var { name = "a" } ] } };
      { name = "h2";
        shell = Forall { var = "x"; ty = "Nat";
          body = Implies {
            antecedent = App { symbol = "p"; type_args = [];
                               args = [ Var { name = "x" } ] };
            consequent = App { symbol = "q"; type_args = [];
                               args = [ Var { name = "x" } ] } } } };
    ];
    library_slice = None };
  type_metadata = []; definitional_metadata = [];
  library_provenance = []; user_directives = None;
}

let verdict s = Tier3_tptp.verify (ir ()) s

let is_structural = function
  | Tier3_tptp.Structural_failure _ -> true | _ -> false

let test_verified_provenance () =
  match verdict base with
  | Verified_provenance -> ()
  | other ->
    Alcotest.fail ("expected Verified_provenance, got "
                   ^ Tier3_tptp.result_to_string other)

let test_smuggled_axiom () =
  let s = replace ~old:"file('/tmp/q.p',h2)"
            ~by:"file('/tmp/q.p',sneaky)" base in
  Alcotest.(check bool) "smuggled axiom → structural_failure" true
    (is_structural (verdict s))

let test_introduced_formula () =
  (* Add an introduced definition and route a reachable step
     through it. *)
  let s =
    replace ~old:"fof(f10,plain,(\n  q(a)),\n  inference(resolution,[],[f8,f7]))."
      ~by:"fof(d1,axiom,(\n  sP0 <=> p(a)),\n  introduced(definition,[])).\n\
           fof(f10,plain,(\n  q(a)),\n  inference(resolution,[],[f8,f7,d1]))."
      base
  in
  Alcotest.(check bool) "introduced formula → structural_failure" true
    (is_structural (verdict s))

let test_unrecognized_rule () =
  let s = replace ~old:"inference(resolution,[],[f8,f7])"
            ~by:"inference(quantum_magic,[],[f8,f7])" base in
  match verdict s with
  | Unrecognized_rule { rule; _ } ->
    Alcotest.(check string) "rule name surfaced" "quantum_magic" rule
  | other ->
    Alcotest.fail ("expected Unrecognized_rule, got "
                   ^ Tier3_tptp.result_to_string other)

let test_conjecture_not_negated () =
  (* f4 now derives from the conjecture via resolution, not a
     negation inference. *)
  let s = replace
            ~old:"inference(negated_conjecture,[status(cth)],[f3])"
            ~by:"inference(resolution,[],[f3])" base in
  Alcotest.(check bool) "conjecture via non-negation → structural_failure"
    true (is_structural (verdict s))

let test_no_false_sink () =
  let s = replace ~old:"  $false" ~by:"  q(a)" base in
  (match verdict s with
   | Structural_failure { detail; _ } ->
     Alcotest.(check bool) "names the missing sink" true
       (Str.string_match (Str.regexp ".*no \\$false.*") detail 0)
   | other ->
     Alcotest.fail ("expected Structural_failure, got "
                    ^ Tier3_tptp.result_to_string other))

let test_dangling_parent () =
  let s = replace ~old:"inference(resolution,[],[f8,f7])"
            ~by:"inference(resolution,[],[f8,f404])" base in
  Alcotest.(check bool) "dangling parent → structural_failure" true
    (is_structural (verdict s))

let () =
  Alcotest.run "tier3_tptp"
    [
      ( "verify",
        [ Alcotest.test_case "verified provenance" `Quick
            test_verified_provenance;
          Alcotest.test_case "smuggled axiom" `Quick test_smuggled_axiom;
          Alcotest.test_case "introduced formula" `Quick
            test_introduced_formula;
          Alcotest.test_case "unrecognized rule" `Quick
            test_unrecognized_rule;
          Alcotest.test_case "conjecture not negated" `Quick
            test_conjecture_not_negated;
          Alcotest.test_case "no $false sink" `Quick test_no_false_sink;
          Alcotest.test_case "dangling parent" `Quick
            test_dangling_parent ] );
    ]

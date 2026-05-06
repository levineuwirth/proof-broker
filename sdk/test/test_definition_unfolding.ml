(** Unit tests for the definition_unfolding pass.

    The pass requires [definitional_metadata] populated for each
    symbol it unfolds; this test fixture builds synthetic IR documents
    with the minimum metadata needed to exercise:

    * Single-parameter unfold (var arg).
    * Multi-parameter unfold with multiple [Var] args.
    * Capture-avoiding alpha rename.
    * App-symbol substitution when arg is [Var]/[Const].
    * Skip on higher-order arg (would need beta reduction).
    * No-op when concept_tag is not in user_directives.
    * Skipped_preconditions when no concept_tags are configured.
    * Fixpoint cascade when unfolding exposes another unfold. *)

open Proof_broker

(* --- IR scaffolding --------------------------------------------------- *)

let trivial_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "FOL";
  decidable_theory = None;
}
let trivial_source : Ir.source_system = { name = "test"; version = "0.0" }

let user_directives_with (tags : string list) : Ir.user_directives = {
  preferred_backend = None;
  tier_preference = None;
  rewriter_preferences = Some {
    enable_quotient_elimination = None;
    enable_definition_unfolding = Some tags;
    disable_passes = None;
  };
  budget = None;
}

(** [make_ir defn_meta concept_tags shell] builds a minimal IR with
    one goal shell, no hypotheses, the supplied [defn_meta] for the
    [definitional_metadata] map, and [user_directives] enabling the
    given [concept_tags]. *)
let make_ir
      ?(defn_meta : (string * Yojson.Safe.t) list = [])
      ?(concept_tags : string list = [])
      ?(hypotheses : Ir.shell_term list = [])
      (shell : Ir.shell_term)
  : Ir.t =
  let hyps =
    List.mapi
      (fun i s -> ({ name = Printf.sprintf "h%d" i; shell = s } : Ir.hypothesis))
      hypotheses
  in
  {
    ir_version = "1.0";
    source_system = trivial_source;
    tier = "goal";
    logic_classification = trivial_logic;
    goal = { shell; payloads = None };
    context = {
      type_vars = []; free_vars = []; hypotheses = hyps; library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = defn_meta;
    library_provenance = [];
    user_directives = (
      if concept_tags = [] then None
      else Some (user_directives_with concept_tags)
    );
  }

(* --- DefinitionalMetadata builders ----------------------------------- *)

(** [defined_function ~equation ~concept_tag] builds the JSON shape
    of a [Defn_DefinedFunction] entry, deferring the equation to
    [equation]'s shell encoding. The [abstract_signature] field is
    filled with a placeholder; the pass does not consume it. *)
let defined_function ~(equation : Ir.shell_term) ~(concept_tag : string)
  : Yojson.Safe.t =
  `Assoc [
    "kind", `String "defined_function";
    "abstract_signature", `String "(_)";
    "definitional_equation", Codec.shell_to_json equation;
    "concept_tag", `String concept_tag;
  ]

(* --- Term builders ---------------------------------------------------- *)

let v name : Ir.shell_term = Var { name }
let c_const name : Ir.shell_term = Const { name }
let mk_app symbol args : Ir.shell_term =
  App { symbol; type_args = []; args }
let mk_forall var ty body : Ir.shell_term = Forall { var; ty; body }
let mk_eq ty l r : Ir.shell_term = Eq { ty; left = l; right = r }
let mk_lambda binders body : Ir.shell_term = Lambda { binders; body }

(** [forall_chain params body] = ∀ p1 ... pn, body, with all binder
    types set to ["T"] (unused by the pass). *)
let forall_chain (params : string list) (body : Ir.shell_term) : Ir.shell_term =
  List.fold_right (fun p acc -> mk_forall p "T" acc) params body

(* --- Trace inspection ------------------------------------------------- *)

let extract_unfolds (entry : Trace.entry) : (string * string * string) list =
  match entry.inversion_data with
  | Some (`Assoc pairs) ->
    (match List.assoc_opt "unfolded_symbols" pairs with
     | Some (`List xs) ->
       List.map
         (fun j ->
           let p = match j with `Assoc p -> p | _ -> failwith "bad entry" in
           let s = match List.assoc "symbol" p with `String s -> s | _ -> "" in
           let v = match List.assoc "via" p with `String s -> s | _ -> "" in
           let st = match List.assoc "site" p with `String s -> s | _ -> "" in
           (s, v, st))
         xs
     | _ -> [])
  | _ -> []

(* --- Tests ------------------------------------------------------------ *)

(* identity : ∀ x, identity x = x *)
let identity_equation : Ir.shell_term =
  forall_chain [ "x" ] (mk_eq "T" (mk_app "identity" [ v "x" ]) (v "x"))

let identity_meta = defined_function
                      ~equation:identity_equation
                      ~concept_tag:"identity"

let test_simple_unfold () =
  let ir = make_ir
             ~defn_meta:[ "identity", identity_meta ]
             ~concept_tags:[ "identity" ]
             (mk_app "identity" [ v "y" ]) in
  let result = Definition_unfolding.run ir in
  Alcotest.(check (list (triple string string string)))
    "single unfold recorded"
    [ ("identity", "definitional_equation", "goal") ]
    (extract_unfolds result.trace);
  Alcotest.(check bool) "outcome=applied"
    true (result.trace.outcome = Some Applied);
  Alcotest.(check bool) "goal collapsed to y"
    true (result.ir.goal.shell = v "y")

let test_no_op_when_concept_tag_not_enabled () =
  let ir = make_ir
             ~defn_meta:[ "identity", identity_meta ]
             ~concept_tags:[ "function_composition" ]  (* not "identity" *)
             (mk_app "identity" [ v "y" ]) in
  let result = Definition_unfolding.run ir in
  Alcotest.(check int) "no unfolds"
    0 (List.length (extract_unfolds result.trace));
  Alcotest.(check bool) "outcome=No_op"
    true (result.trace.outcome = Some No_op);
  Alcotest.(check bool) "goal unchanged"
    true (result.ir.goal.shell = mk_app "identity" [ v "y" ])

let test_skipped_preconditions_when_no_tags () =
  let ir = make_ir
             ~defn_meta:[ "identity", identity_meta ]
             ~concept_tags:[]  (* user_directives absent *)
             (mk_app "identity" [ v "y" ]) in
  let result = Definition_unfolding.run ir in
  Alcotest.(check bool) "outcome=Skipped_preconditions"
    true (result.trace.outcome = Some Skipped_preconditions);
  Alcotest.(check bool) "before_hash = after_hash"
    true (result.trace.before_hash = result.trace.after_hash)

(* swap : ∀ a b, swap a b = pair b a *)
let swap_equation : Ir.shell_term =
  forall_chain [ "a"; "b" ]
    (mk_eq "T" (mk_app "swap" [ v "a"; v "b" ])
              (mk_app "pair" [ v "b"; v "a" ]))

let swap_meta = defined_function ~equation:swap_equation ~concept_tag:"swap"

let test_multi_param_unfold () =
  let ir = make_ir
             ~defn_meta:[ "swap", swap_meta ]
             ~concept_tags:[ "swap" ]
             (mk_app "swap" [ v "p"; v "q" ]) in
  let result = Definition_unfolding.run ir in
  Alcotest.(check bool) "goal becomes pair q p"
    true (result.ir.goal.shell = mk_app "pair" [ v "q"; v "p" ]);
  Alcotest.(check bool) "outcome=applied"
    true (result.trace.outcome = Some Applied)

(* compose : ∀ f g, compose f g = λ a, f (g a)
   Tests that App-symbol-position substitution works for Var args. *)
let compose_equation : Ir.shell_term =
  forall_chain [ "f"; "g" ]
    (mk_eq "T"
       (mk_app "compose" [ v "f"; v "g" ])
       (mk_lambda [ ({ var = "a"; ty = "T" } : Ir.binder) ]
          (mk_app "f" [ mk_app "g" [ v "a" ] ])))

let compose_meta = defined_function
                     ~equation:compose_equation
                     ~concept_tag:"function_composition"

let test_app_symbol_substitution_with_const () =
  (* compose F G  where F/G are Const symbols → should rewrite App
     symbols at f/g positions in the body. *)
  let ir = make_ir
             ~defn_meta:[ "compose", compose_meta ]
             ~concept_tags:[ "function_composition" ]
             (mk_app "compose" [ c_const "F"; c_const "G" ]) in
  let result = Definition_unfolding.run ir in
  let expected =
    mk_lambda [ ({ var = "a"; ty = "T" } : Ir.binder) ]
      (mk_app "F" [ mk_app "G" [ v "a" ] ])
  in
  Alcotest.(check bool) "App symbols substituted to F/G"
    true (result.ir.goal.shell = expected)

let test_skip_on_higher_order_arg () =
  (* compose (Lambda [x] body) G — first arg is a Lambda, would need
     beta reduction, so the unfold is skipped silently. *)
  let lambda_arg = mk_lambda [ ({ var = "x"; ty = "T" } : Ir.binder) ]
                     (mk_app "h" [ v "x" ]) in
  let ir = make_ir
             ~defn_meta:[ "compose", compose_meta ]
             ~concept_tags:[ "function_composition" ]
             (mk_app "compose" [ lambda_arg; c_const "G" ]) in
  let result = Definition_unfolding.run ir in
  Alcotest.(check int) "no unfolds recorded"
    0 (List.length (extract_unfolds result.trace));
  Alcotest.(check bool) "goal unchanged"
    true (result.ir.goal.shell = mk_app "compose" [ lambda_arg; c_const "G" ])

(* alpha-rename test:
     equation: ∀ x, takes_a x = ∀ a, eq T x a   (the body binds "a" inside)
     Substitute x := Var "a" — the binder Forall a should be alpha-renamed
     to avoid capturing the substituted-in `a`. *)
let bind_a_equation : Ir.shell_term =
  forall_chain [ "x" ]
    (mk_eq "T"
       (mk_app "binds_a" [ v "x" ])
       (mk_forall "a" "T"
          (mk_eq "T" (v "x") (v "a"))))

let bind_a_meta = defined_function ~equation:bind_a_equation ~concept_tag:"capture_test"

let test_capture_avoidance () =
  let ir = make_ir
             ~defn_meta:[ "binds_a", bind_a_meta ]
             ~concept_tags:[ "capture_test" ]
             (mk_app "binds_a" [ v "a" ]) in
  let result = Definition_unfolding.run ir in
  match result.ir.goal.shell with
  | Forall { var; body; _ } ->
    Alcotest.(check bool)
      "binder was alpha-renamed away from `a`"
      true (var <> "a");
    (match body with
     | Eq { left = Var { name = ll }; right = Var { name = rr }; _ } ->
       Alcotest.(check string) "left side is the substituted-in `a`"
         "a" ll;
       Alcotest.(check bool) "right side is the renamed binder, not `a`"
         true (rr <> "a" && rr = var)
     | _ -> Alcotest.fail "body shape unexpected")
  | _ -> Alcotest.fail "expected Forall at goal"

(* Cascade test: identity (identity x) — first iteration unfolds the
   inner identity, second iteration unfolds the outer. Both should
   land in one [run] call. *)
let test_fixpoint_cascade () =
  let ir = make_ir
             ~defn_meta:[ "identity", identity_meta ]
             ~concept_tags:[ "identity" ]
             (mk_app "identity" [ mk_app "identity" [ v "y" ] ]) in
  let result = Definition_unfolding.run ir in
  Alcotest.(check int) "two unfolds recorded"
    2 (List.length (extract_unfolds result.trace));
  Alcotest.(check bool) "goal collapsed to y"
    true (result.ir.goal.shell = v "y")

let test_hypothesis_site () =
  let ir = make_ir
             ~defn_meta:[ "identity", identity_meta ]
             ~concept_tags:[ "identity" ]
             ~hypotheses:[ mk_app "identity" [ v "p" ] ]
             (v "g") in
  let result = Definition_unfolding.run ir in
  let unfolds = extract_unfolds result.trace in
  Alcotest.(check (list string)) "site is hypothesis[0]"
    [ "hypothesis[0]" ] (List.map (fun (_, _, s) -> s) unfolds)

let extract_unfold_indices (entry : Trace.entry) : int list =
  match entry.inversion_data with
  | Some (`Assoc pairs) ->
    (match List.assoc_opt "unfolded_symbols" pairs with
     | Some (`List xs) ->
       List.map
         (fun j ->
           let p = match j with `Assoc p -> p | _ -> failwith "bad entry" in
           match List.assoc_opt "index" p with
           | Some (`Int i) -> i
           | _ -> failwith "missing index")
         xs
     | _ -> [])
  | _ -> []

let test_inversion_records_indexed () =
  (* Two unfolds of the same symbol must have distinct indices so
     the lifting layer can address each occurrence independently. *)
  let ir = make_ir
             ~defn_meta:[ "identity", identity_meta ]
             ~concept_tags:[ "identity" ]
             (mk_app "identity" [ mk_app "identity" [ v "y" ] ]) in
  let result = Definition_unfolding.run ir in
  Alcotest.(check (list int)) "indices are dense [0; 1]"
    [ 0; 1 ] (extract_unfold_indices result.trace)

let test_pass_metadata () =
  let result = Definition_unfolding.run (make_ir (v "p")) in
  Alcotest.(check string) "pass name"
    "definition_unfolding" result.trace.pass;
  Alcotest.(check string) "version"
    "1.0" result.trace.version

let () =
  Alcotest.run "definition_unfolding" [
    "core", [
      Alcotest.test_case "simple unfold (var arg)" `Quick test_simple_unfold;
      Alcotest.test_case "multi-param unfold" `Quick test_multi_param_unfold;
      Alcotest.test_case "App-symbol sub with Const" `Quick test_app_symbol_substitution_with_const;
      Alcotest.test_case "skip on higher-order arg" `Quick test_skip_on_higher_order_arg;
      Alcotest.test_case "capture-avoiding alpha rename" `Quick test_capture_avoidance;
    ];
    "config", [
      Alcotest.test_case "no-op when tag not enabled" `Quick test_no_op_when_concept_tag_not_enabled;
      Alcotest.test_case "skipped_preconditions when no tags" `Quick test_skipped_preconditions_when_no_tags;
    ];
    "trace_shape", [
      Alcotest.test_case "fixpoint cascade in one run" `Quick test_fixpoint_cascade;
      Alcotest.test_case "hypothesis site tag" `Quick test_hypothesis_site;
      Alcotest.test_case "pass metadata" `Quick test_pass_metadata;
      Alcotest.test_case "inversion records carry dense indices"
        `Quick test_inversion_records_indexed;
    ];
  ]

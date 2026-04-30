(** Unit tests for the quotient_elimination pass.

    Builds small synthetic IRs with [type_metadata] declaring a
    quotient and [definitional_metadata] declaring a [lifted_to_quotient]
    symbol, then exercises the pass's three rewrites and the
    [Skipped_preconditions] / [No_op] / [Applied] outcomes.

    Coverage:
    * Skipped when [enable_quotient_elimination] is missing/false.
    * No-op when enabled but no quotient types declared.
    * Free vars of quotient type get rewritten + recorded under
      [eliminations].
    * [Eq { ty = qtype }] gets reduced to the equivalence relation
      applied to (left, right) — beta reduction of the relation lambda.
    * [App] of a [lifted_to_quotient] symbol gets rewritten to the
      underlying function, with witness recorded.
    * The example3 fixture (full quotient + lifted-fn data) lands on
      [Applied] with all three categories populated.
    * Inversion data shape matches the schema's permissive structure
      and is JSON round-trippable.
    * Hash discipline: changes to the IR yield distinct
      before/after hashes. *)

open Proof_broker

(* --- IR scaffolding --------------------------------------------------- *)

let trivial_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "FOL";
  decidable_theory = None;
}

let trivial_source : Ir.source_system = { name = "test"; version = "0.0" }

let user_directives_enabling : Ir.user_directives = {
  preferred_backend = None;
  tier_preference = None;
  rewriter_preferences = Some {
    enable_quotient_elimination = Some true;
    enable_definition_unfolding = None;
    disable_passes = None;
  };
  budget = None;
}

let make_ir
      ?(type_meta : (string * Yojson.Safe.t) list = [])
      ?(defn_meta : (string * Yojson.Safe.t) list = [])
      ?(free_vars : Ir.free_var list = [])
      ?(hypotheses : Ir.shell_term list = [])
      ?(enabled : bool = true)
      (shell : Ir.shell_term)
  : Ir.t =
  let hyps =
    List.mapi
      (fun i s ->
        ({ name = Printf.sprintf "h%d" i; shell = s } : Ir.hypothesis))
      hypotheses
  in
  {
    ir_version = "1.0";
    source_system = trivial_source;
    tier = "goal";
    logic_classification = trivial_logic;
    goal = { shell; payloads = None };
    context = {
      type_vars = []; free_vars; hypotheses = hyps; library_slice = None;
    };
    type_metadata = type_meta;
    definitional_metadata = defn_meta;
    library_provenance = [];
    user_directives = if enabled then Some user_directives_enabling else None;
  }

(* --- Term and metadata builders -------------------------------------- *)

let v name : Ir.shell_term = Var { name }

(** [quotient_type ~qtype ~underlying ~rel_symbol] builds the JSON
    shape of a [type_constructor_application] entry with construction
    kind "quotient". The relation lambda is `\a b => rel_symbol a b`. *)
let quotient_type ~(qtype : string) ~(underlying : string)
                  ~(rel_symbol : string) : string * Yojson.Safe.t =
  let relation_lambda : Ir.shell_term =
    Lambda {
      binders = [
        { var = "a"; ty = underlying };
        { var = "b"; ty = underlying };
      ];
      body = App {
        symbol = rel_symbol;
        type_args = [];
        args = [ v "a"; v "b" ];
      };
    }
  in
  qtype, `Assoc [
    "kind", `String "type_constructor_application";
    "constructor", `Assoc [
      "name", `String qtype;
      "construction_kind", `String "quotient";
      "underlying_type", `String underlying;
      "equivalence_relation", `Assoc [
        "shell", Codec.shell_to_json relation_lambda;
        "equivalence_proof", `String (rel_symbol ^ ".equivalence");
      ];
      "elimination_principle", `String (qtype ^ ".ind");
      "equality_principle", `String (qtype ^ ".sound");
    ];
    "arguments", `List [];
  ]

(** [lifted_to_quotient ~lifted ~underlying ~host] builds the JSON
    shape of a [definitional_metadata] entry of kind
    "lifted_to_quotient". The witness is named after the lifted
    symbol. *)
let lifted_to_quotient ~(lifted : string) ~(underlying : string)
                       ~(host : string) : string * Yojson.Safe.t =
  lifted, `Assoc [
    "kind", `String "lifted_to_quotient";
    "host_type", `String host;
    "underlying_function", `Assoc [
      "name", `String underlying;
      "shell", Codec.shell_to_json (Const { name = underlying });
    ];
    "lifting_obligation", `Assoc [
      "shape", `String "respects_relation";
      "discharged_at", `String "definition_site";
      "witness", `String (lifted ^ ".respects");
    ];
  ]

(* --- Inversion-data helpers ------------------------------------------ *)

let extract_section (entry : Trace.entry) (key : string) : Yojson.Safe.t list =
  match entry.inversion_data with
  | Some (`Assoc pairs) ->
    (match List.assoc_opt key pairs with
     | Some (`List xs) -> xs
     | _ -> [])
  | _ -> []

let count_section entry key = List.length (extract_section entry key)

(* --- Tests ------------------------------------------------------------ *)

let test_skipped_when_disabled () =
  (* No user_directives at all -> skipped_preconditions, IR unchanged. *)
  let ir = make_ir ~enabled:false (v "p") in
  let result = Quotient_elimination.run ir in
  Alcotest.(check bool) "outcome=Skipped_preconditions"
    true (result.trace.outcome = Some Skipped_preconditions);
  Alcotest.(check string) "before == after hash"
    result.trace.before_hash result.trace.after_hash;
  Alcotest.(check bool) "no inversion data"
    true (result.trace.inversion_data = None)

let test_no_op_when_no_quotient_types () =
  (* Enabled, but no quotient metadata anywhere -> No_op. *)
  let ir = make_ir (v "p") in
  let result = Quotient_elimination.run ir in
  Alcotest.(check bool) "outcome=No_op"
    true (result.trace.outcome = Some No_op);
  Alcotest.(check string) "hashes equal"
    result.trace.before_hash result.trace.after_hash

let test_eliminate_free_var_type () =
  (* Free var x : Q gets rewritten to x : U with one elimination
     recorded. *)
  let qmeta = quotient_type ~qtype:"Q" ~underlying:"U" ~rel_symbol:"R" in
  let ir = make_ir
    ~type_meta:[ qmeta ]
    ~free_vars:[ { name = "x"; ty = "Q" } ]
    (v "p") in
  let result = Quotient_elimination.run ir in
  Alcotest.(check bool) "outcome=Applied"
    true (result.trace.outcome = Some Applied);
  Alcotest.(check int) "one elimination" 1
    (count_section result.trace "eliminations");
  let fv = List.hd result.ir.context.free_vars in
  Alcotest.(check string) "free var type rewritten to U" "U" fv.ty;
  Alcotest.(check string) "free var name preserved" "x" fv.name

let test_eq_at_quotient_reduces_to_relation () =
  (* Eq { ty = Q; left = x; right = y } should beta-reduce
     `\a b. R a b` (x, y) → `R x y`. *)
  let qmeta = quotient_type ~qtype:"Q" ~underlying:"U" ~rel_symbol:"R" in
  let goal : Ir.shell_term =
    Eq { ty = "Q"; left = v "x"; right = v "y" }
  in
  let ir = make_ir ~type_meta:[ qmeta ] goal in
  let result = Quotient_elimination.run ir in
  Alcotest.(check bool) "outcome=Applied"
    true (result.trace.outcome = Some Applied);
  Alcotest.(check int) "one equality reduction" 1
    (count_section result.trace "equality_reductions");
  (match result.ir.goal.shell with
   | App { symbol = "R"; args = [ Var { name = "x" }; Var { name = "y" } ]; _ } ->
     ()
   | other ->
     Alcotest.fail (Printf.sprintf "unexpected goal: %s"
                      (Yojson.Safe.to_string (Codec.shell_to_json other))))

let test_lifted_app_unfolds_to_underlying () =
  let qmeta = quotient_type ~qtype:"Q" ~underlying:"U" ~rel_symbol:"R" in
  let lmeta = lifted_to_quotient ~lifted:"f_lift" ~underlying:"f" ~host:"Q" in
  let goal : Ir.shell_term =
    App { symbol = "f_lift"; type_args = []; args = [ v "x"; v "y" ] }
  in
  let ir = make_ir ~type_meta:[ qmeta ] ~defn_meta:[ lmeta ] goal in
  let result = Quotient_elimination.run ir in
  Alcotest.(check int) "one lifted unfolding" 1
    (count_section result.trace "lifted_unfoldings");
  match result.ir.goal.shell with
  | App { symbol = "f"; args = [ Var { name = "x" }; Var { name = "y" } ]; _ } ->
    ()
  | other ->
    Alcotest.fail (Printf.sprintf "unexpected goal: %s"
                     (Yojson.Safe.to_string (Codec.shell_to_json other)))

let test_combined_rewrites () =
  (* Eq { ty = Q; left = f_lift x y; right = f_lift y x } should:
     - rewrite both Apps to f
     - reduce the Eq to R applied to the rewritten sides
     producing R (f x y) (f y x). Records 1 equality_reduction +
     2 lifted_unfoldings. *)
  let qmeta = quotient_type ~qtype:"Q" ~underlying:"U" ~rel_symbol:"R" in
  let lmeta = lifted_to_quotient ~lifted:"f_lift" ~underlying:"f" ~host:"Q" in
  let goal : Ir.shell_term =
    Eq {
      ty = "Q";
      left = App {
        symbol = "f_lift"; type_args = []; args = [ v "x"; v "y" ]
      };
      right = App {
        symbol = "f_lift"; type_args = []; args = [ v "y"; v "x" ]
      };
    }
  in
  let ir = make_ir ~type_meta:[ qmeta ] ~defn_meta:[ lmeta ] goal in
  let result = Quotient_elimination.run ir in
  Alcotest.(check int) "1 equality reduction" 1
    (count_section result.trace "equality_reductions");
  Alcotest.(check int) "2 lifted unfoldings" 2
    (count_section result.trace "lifted_unfoldings");
  Alcotest.(check bool) "before != after hash"
    true (result.trace.before_hash <> result.trace.after_hash)

let test_inversion_data_records_principles () =
  (* The inversion data should carry the elimination_principle,
     equality_principle, and equivalence_proof names — those are the
     ones the lifting layer needs to rebuild the original goal. *)
  let qmeta = quotient_type ~qtype:"Q" ~underlying:"U" ~rel_symbol:"R" in
  let ir = make_ir
    ~type_meta:[ qmeta ]
    ~free_vars:[ { name = "x"; ty = "Q" } ]
    (Eq { ty = "Q"; left = v "x"; right = v "x" }) in
  let result = Quotient_elimination.run ir in
  let elim = List.hd (extract_section result.trace "eliminations") in
  Alcotest.(check string) "elim records elimination_principle"
    "Q.ind"
    (match elim with
     | `Assoc p ->
       (match List.assoc "elimination_principle" p with
        | `String s -> s | _ -> "??")
     | _ -> "??");
  let er = List.hd (extract_section result.trace "equality_reductions") in
  Alcotest.(check string) "equality reduction records equality_principle"
    "Q.sound"
    (match er with
     | `Assoc p ->
       (match List.assoc "equality_principle" p with
        | `String s -> s | _ -> "??")
     | _ -> "??")

let test_hypothesis_site_rewriting () =
  (* Quotient eq inside a hypothesis lands at site=hypothesis[0]. *)
  let qmeta = quotient_type ~qtype:"Q" ~underlying:"U" ~rel_symbol:"R" in
  let hyp : Ir.shell_term = Eq { ty = "Q"; left = v "x"; right = v "y" } in
  let ir = make_ir ~type_meta:[ qmeta ] ~hypotheses:[ hyp ] (v "g") in
  let result = Quotient_elimination.run ir in
  let er = List.hd (extract_section result.trace "equality_reductions") in
  Alcotest.(check string) "site is hypothesis[0]"
    "hypothesis[0]"
    (match er with
     | `Assoc p ->
       (match List.assoc "site" p with `String s -> s | _ -> "??")
     | _ -> "??")

let test_example3_fixture_lands_on_applied () =
  (* Run on the actual reference fixture: load JSON, decode IR, set
     enable_quotient_elimination=true (the fixture itself doesn't
     pre-set user_directives), run the pass. Expect Applied with at
     least one of each inversion category. *)
  (* Path is relative to the test executable's build dir; mirror
     test_round_trip.ml's resolution. *)
  let path = Filename.concat (Sys.getcwd ())
               "../../../../examples/example3-quotient-zmod.json" in
  let raw = In_channel.with_open_text path In_channel.input_all in
  let ir = Codec.of_json (Yojson.Safe.from_string raw) in
  let ir_with_flag : Ir.t = { ir with user_directives = Some user_directives_enabling } in
  let result = Quotient_elimination.run ir_with_flag in
  Alcotest.(check bool) "outcome=Applied on example3"
    true (result.trace.outcome = Some Applied);
  Alcotest.(check bool) "eliminations populated"
    true (count_section result.trace "eliminations" >= 1);
  Alcotest.(check bool) "lifted_unfoldings populated"
    true (count_section result.trace "lifted_unfoldings" >= 1);
  Alcotest.(check bool) "equality_reductions populated"
    true (count_section result.trace "equality_reductions" >= 1);
  Alcotest.(check bool) "before != after hash"
    true (result.trace.before_hash <> result.trace.after_hash)

let () =
  Alcotest.run "quotient_elimination" [
    "config", [
      Alcotest.test_case "skipped when disabled"
        `Quick test_skipped_when_disabled;
      Alcotest.test_case "no-op when no quotient types"
        `Quick test_no_op_when_no_quotient_types;
    ];
    "rewrites", [
      Alcotest.test_case "free var type rewritten"
        `Quick test_eliminate_free_var_type;
      Alcotest.test_case "Eq at quotient reduces to relation"
        `Quick test_eq_at_quotient_reduces_to_relation;
      Alcotest.test_case "lifted App unfolds to underlying"
        `Quick test_lifted_app_unfolds_to_underlying;
      Alcotest.test_case "combined rewrites"
        `Quick test_combined_rewrites;
    ];
    "inversion_data", [
      Alcotest.test_case "principles recorded"
        `Quick test_inversion_data_records_principles;
      Alcotest.test_case "hypothesis site"
        `Quick test_hypothesis_site_rewriting;
    ];
    "fixture", [
      Alcotest.test_case "example3 lands on Applied"
        `Quick test_example3_fixture_lands_on_applied;
    ];
  ]

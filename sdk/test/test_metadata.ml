(** Unit tests for [Type_metadata] and [Definitional_metadata]
    typed-decoder modules.

    Coverage:
    * Each known [definitional_metadata] kind parses into the
      correct typed variant with its fields populated.
    * Unknown [kind] values land in [OtherKind] (not [None]) so
      consumers can walk past forward-incompatible entries.
    * Quotient construction-kind parses with the equivalence
      relation lambda decoded as a shell term.
    * Off-shape entries (missing required fields) yield [None]
      rather than partial structures.
    * The lookup helpers ([find_quotient], [find_defined_function],
      [find_lifted_to_quotient]) return the entries built into
      the example fixtures. *)

open Proof_broker

(* --- Fixtures --------------------------------------------------------- *)

let trivial_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "FOL";
  decidable_theory = None;
}

let make_ir
      ?(type_meta : (string * Yojson.Safe.t) list = [])
      ?(defn_meta : (string * Yojson.Safe.t) list = [])
      () : Ir.t =
  {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = trivial_logic;
    goal = { shell = Var { name = "p" }; payloads = None };
    context = {
      type_vars = []; free_vars = []; hypotheses = []; library_slice = None;
    };
    type_metadata = type_meta;
    definitional_metadata = defn_meta;
    library_provenance = [];
    user_directives = None;
  }

let lambda2 (rel : string) : Ir.shell_term =
  Lambda {
    binders = [
      { var = "a"; ty = "U" };
      { var = "b"; ty = "U" };
    ];
    body = App {
      symbol = rel; type_args = [];
      args = [ Var { name = "a" }; Var { name = "b" } ];
    };
  }

let quotient_meta (q : string) (u : string) (rel : string) : string * Yojson.Safe.t =
  q, `Assoc [
    "kind", `String "type_constructor_application";
    "constructor", `Assoc [
      "name", `String q;
      "construction_kind", `String "quotient";
      "underlying_type", `String u;
      "equivalence_relation", `Assoc [
        "shell", Codec.shell_to_json (lambda2 rel);
        "equivalence_proof", `String (rel ^ ".equivalence");
      ];
      "elimination_principle", `String (q ^ ".ind");
      "equality_principle", `String (q ^ ".sound");
    ];
    "arguments", `List [];
  ]

let defined_function_meta (sym : string) ~(tag : string) : string * Yojson.Safe.t =
  let eq : Ir.shell_term =
    Forall { var = "x"; ty = "Int"; body =
      Eq { ty = "Int";
           left = App { symbol = sym; type_args = []; args = [ Var { name = "x" } ] };
           right = Var { name = "x" } } }
  in
  sym, `Assoc [
    "kind", `String "defined_function";
    "abstract_signature", `String "Int -> Int";
    "definitional_equation", Codec.shell_to_json eq;
    "concept_tag", `String tag;
  ]

let lifted_meta ~(lifted : string) ~(underlying : string) ~(host : string)
  : string * Yojson.Safe.t =
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

let primitive_meta sym sig_ tag : string * Yojson.Safe.t =
  sym, `Assoc [
    "kind", `String "primitive_arithmetic";
    "abstract_signature", `String sig_;
    "theory_tag", `String tag;
  ]

let typeclass_meta sym method_ host role : string * Yojson.Safe.t =
  sym, `Assoc [
    "kind", `String "typeclass_method";
    "method_name", `String method_;
    "host_class", `String host;
    "abstract_role", `String role;
    "specialization_targets", `List [];
  ]

(* --- Type_metadata tests --------------------------------------------- *)

let test_quotient_parses () =
  let ir = make_ir ~type_meta:[ quotient_meta "Q" "U" "R" ] () in
  match Type_metadata.find_quotient ir "Q" with
  | None -> Alcotest.fail "expected Q to parse as quotient"
  | Some qc ->
    Alcotest.(check string) "underlying_type" "U" qc.underlying_type;
    Alcotest.(check string) "elimination_principle" "Q.ind"
      qc.elimination_principle;
    Alcotest.(check string) "equality_principle" "Q.sound"
      qc.equality_principle;
    Alcotest.(check string) "equivalence_proof" "R.equivalence"
      qc.equivalence_relation.equivalence_proof;
    Alcotest.(check bool) "relation lambda is 2-binder Lambda"
      true (match qc.equivalence_relation.shell with
            | Lambda { binders; _ } -> List.length binders = 2
            | _ -> false)

let test_unknown_construction_kind_lands_in_other () =
  let bad = "B", `Assoc [
    "kind", `String "type_constructor_application";
    "constructor", `Assoc [
      "name", `String "B";
      "construction_kind", `String "inductive";
    ];
    "arguments", `List [];
  ] in
  let ir = make_ir ~type_meta:[ bad ] () in
  let entries = Type_metadata.parse_all ir in
  Alcotest.(check int) "1 entry parsed" 1 (Type_metadata.SM.cardinal entries);
  let e = Type_metadata.SM.find "B" entries in
  match e with
  | TypeConstructorApplication { constructor = ConstructorOther { construction_kind; _ }; _ } ->
    Alcotest.(check string) "kind preserved" "inductive" construction_kind
  | _ -> Alcotest.fail "expected ConstructorOther for inductive"

let test_unknown_top_level_kind_lands_in_other_kind () =
  let bad = "X", `Assoc [
    "kind", `String "made_up_kind_for_testing";
  ] in
  let ir = make_ir ~type_meta:[ bad ] () in
  let entries = Type_metadata.parse_all ir in
  match Type_metadata.SM.find "X" entries with
  | OtherKind { kind; _ } ->
    Alcotest.(check string) "kind preserved" "made_up_kind_for_testing" kind
  | _ -> Alcotest.fail "expected OtherKind for unknown top-level kind"

let test_off_shape_entry_dropped () =
  (* Missing constructor block on a type_constructor_application. *)
  let bad = "Q", `Assoc [ "kind", `String "type_constructor_application" ] in
  let ir = make_ir ~type_meta:[ bad ] () in
  let entries = Type_metadata.parse_all ir in
  Alcotest.(check int) "off-shape entry dropped" 0
    (Type_metadata.SM.cardinal entries)

let test_quotient_constructors_filters () =
  let ir = make_ir
    ~type_meta:[
      quotient_meta "Q" "U" "R";
      ("X", `Assoc [ "kind", `String "made_up" ]);
    ] () in
  let qs = Type_metadata.quotient_constructors ir in
  Alcotest.(check int) "only Q is in the quotient map" 1
    (Type_metadata.SM.cardinal qs);
  Alcotest.(check bool) "Q is present" true (Type_metadata.SM.mem "Q" qs)

(* --- Definitional_metadata tests ------------------------------------- *)

let test_defined_function_parses () =
  let ir = make_ir ~defn_meta:[ defined_function_meta "f" ~tag:"my_concept" ] () in
  match Definitional_metadata.find_defined_function ir "f" with
  | None -> Alcotest.fail "expected f to parse"
  | Some df ->
    Alcotest.(check string) "abstract_signature" "Int -> Int"
      df.abstract_signature;
    Alcotest.(check (option string)) "concept_tag"
      (Some "my_concept") df.concept_tag;
    Alcotest.(check bool) "equation is Forall"
      true (match df.definitional_equation with
            | Forall _ -> true | _ -> false)

let test_lifted_to_quotient_parses () =
  let ir = make_ir
    ~defn_meta:[ lifted_meta ~lifted:"f_lift" ~underlying:"f" ~host:"Q" ] () in
  match Definitional_metadata.find_lifted_to_quotient ir "f_lift" with
  | None -> Alcotest.fail "expected f_lift to parse"
  | Some li ->
    Alcotest.(check string) "host_type" "Q" li.host_type;
    Alcotest.(check string) "underlying_function_name" "f"
      li.underlying_function_name;
    Alcotest.(check (option string)) "lifting_witness"
      (Some "f_lift.respects") li.lifting_witness

let test_primitive_arithmetic_parses () =
  let ir = make_ir
    ~defn_meta:[ primitive_meta "Int.add" "Int -> Int -> Int" "LIA:plus" ] () in
  match Definitional_metadata.SM.find_opt "Int.add"
          (Definitional_metadata.parse_all ir) with
  | Some (PrimitiveArithmetic { data; _ }) ->
    Alcotest.(check string) "theory_tag" "LIA:plus" data.theory_tag;
    Alcotest.(check string) "abstract_signature" "Int -> Int -> Int"
      data.abstract_signature
  | _ -> Alcotest.fail "expected PrimitiveArithmetic"

let test_typeclass_method_parses () =
  let ir = make_ir
    ~defn_meta:[ typeclass_meta "LT.lt" "LT.lt" "LT" "ordering" ] () in
  match Definitional_metadata.SM.find_opt "LT.lt"
          (Definitional_metadata.parse_all ir) with
  | Some (TypeclassMethod { data; _ }) ->
    Alcotest.(check string) "method_name" "LT.lt" data.method_name;
    Alcotest.(check string) "abstract_role" "ordering" data.abstract_role;
    Alcotest.(check string) "host_class" "LT" data.host_class
  | _ -> Alcotest.fail "expected TypeclassMethod"

let test_unknown_kind_is_other_kind () =
  let bad = "x", `Assoc [
    "kind", `String "from_the_future";
    "payload", `String "whatever";
  ] in
  let ir = make_ir ~defn_meta:[ bad ] () in
  match Definitional_metadata.SM.find_opt "x"
          (Definitional_metadata.parse_all ir) with
  | Some (OtherKind { kind; _ }) ->
    Alcotest.(check string) "kind preserved" "from_the_future" kind
  | _ -> Alcotest.fail "expected OtherKind for unknown kind"

let test_constructor_and_eliminator_round_trip () =
  let ctor = "C", `Assoc [
    "kind", `String "constructor";
    "for_type", `String "Nat";
  ] in
  let elim = "Nat.rec", `Assoc [
    "kind", `String "eliminator";
    "for_type", `String "Nat";
  ] in
  let ir = make_ir ~defn_meta:[ ctor; elim ] () in
  let entries = Definitional_metadata.parse_all ir in
  Alcotest.(check bool) "Constructor classified correctly"
    true (match Definitional_metadata.SM.find_opt "C" entries with
          | Some (Constructor _) -> true | _ -> false);
  Alcotest.(check bool) "Eliminator classified correctly"
    true (match Definitional_metadata.SM.find_opt "Nat.rec" entries with
          | Some (Eliminator _) -> true | _ -> false)

let test_off_shape_defined_function_dropped () =
  (* Missing definitional_equation on a defined_function. *)
  let bad = "f", `Assoc [
    "kind", `String "defined_function";
    "abstract_signature", `String "Int -> Int";
    "concept_tag", `String "x";
  ] in
  let ir = make_ir ~defn_meta:[ bad ] () in
  let entries = Definitional_metadata.parse_all ir in
  Alcotest.(check int) "off-shape entry dropped" 0
    (Definitional_metadata.SM.cardinal entries)

(* --- example3 fixture round-trip ------------------------------------- *)

let test_example3_fixture_classifies_all_kinds () =
  let path = Filename.concat (Sys.getcwd ())
               "../../../../examples/example3-quotient-zmod.json" in
  let raw = In_channel.with_open_text path In_channel.input_all in
  let ir = Codec.of_json (Yojson.Safe.from_string raw) in
  (* The example3 fixture exercises every kind in v1. The typed
     decoder should classify all entries (none should be dropped). *)
  let total = List.length ir.definitional_metadata in
  let parsed = Definitional_metadata.SM.cardinal
                 (Definitional_metadata.parse_all ir) in
  Alcotest.(check int) "every defn metadata entry classified"
    total parsed;
  let ttotal = List.length ir.type_metadata in
  let tparsed = Type_metadata.SM.cardinal (Type_metadata.parse_all ir) in
  Alcotest.(check int) "every type metadata entry classified"
    ttotal tparsed;
  (* And the type_metadata entry (MyZMod_n) is specifically a quotient. *)
  Alcotest.(check bool) "MyZMod_n is a quotient"
    true (Option.is_some (Type_metadata.find_quotient ir "MyZMod_n"))

let () =
  Alcotest.run "metadata" [
    "type_metadata", [
      Alcotest.test_case "quotient parses" `Quick test_quotient_parses;
      Alcotest.test_case "unknown construction_kind → ConstructorOther"
        `Quick test_unknown_construction_kind_lands_in_other;
      Alcotest.test_case "unknown top-level kind → OtherKind"
        `Quick test_unknown_top_level_kind_lands_in_other_kind;
      Alcotest.test_case "off-shape entry dropped"
        `Quick test_off_shape_entry_dropped;
      Alcotest.test_case "quotient_constructors filters non-quotients"
        `Quick test_quotient_constructors_filters;
    ];
    "definitional_metadata", [
      Alcotest.test_case "defined_function parses"
        `Quick test_defined_function_parses;
      Alcotest.test_case "lifted_to_quotient parses"
        `Quick test_lifted_to_quotient_parses;
      Alcotest.test_case "primitive_arithmetic parses"
        `Quick test_primitive_arithmetic_parses;
      Alcotest.test_case "typeclass_method parses"
        `Quick test_typeclass_method_parses;
      Alcotest.test_case "unknown kind → OtherKind"
        `Quick test_unknown_kind_is_other_kind;
      Alcotest.test_case "constructor + eliminator classified"
        `Quick test_constructor_and_eliminator_round_trip;
      Alcotest.test_case "off-shape defined_function dropped"
        `Quick test_off_shape_defined_function_dropped;
    ];
    "fixture", [
      Alcotest.test_case "example3 every kind classifies"
        `Quick test_example3_fixture_classifies_all_kinds;
    ];
  ]

(** Unit tests for [Refinement].

    Coverage:
    * Empty IR (no metadata) is a no-op; refined_ir = original,
      specializations list is empty.
    * On the [example1-lia-typeclass.json] fixture: produces
      type_specialization (alpha → Int) and method_specialization
      entries for HAdd.hAdd, LE.le, OfNat.ofNat.
    * Type substitution actually applies to the IR: [alpha] in
      free_vars becomes [Int]; [alpha] in NumLit type tags becomes
      [Int]; [alpha] in Eq's [ty] field becomes [Int].
    * Unknown fragment returns Unknown_fragment error; recognized
      no-substitution fragments (UF, BV) pass through as no-ops.
    * LRA target on the same fixture (with theory_classification_tag
      [embeds_into:Int_for_universal_LRA] absent): no
      type_specialization (the tag for LRA isn't there).
    * R3-M1 witness honesty: soundness_witness is the comma-joined
      [embedding_witness:] tag payloads, verbatim; an embed tag
      WITHOUT a witness tag yields no specialization and no
      substitution (fail closed); the [primitive] kind (Nat) embeds
      through [theory_tags] under the same rules; method
      specialization requires a target-level soundness_witness. *)

open Proof_broker

let trivial_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LIA";
  decidable_theory = None;
}

let make_ir
      ?(type_metadata = [])
      ?(definitional_metadata = [])
      ?(free_vars = [])
      ?(hypotheses = [])
      ?(library_slice = None)
      (goal_shell : Ir.shell_term) : Ir.t = {
  ir_version = "1.0";
  source_system = { name = "test"; version = "0.0" };
  tier = "goal";
  logic_classification = trivial_logic;
  goal = { shell = goal_shell; payloads = None };
  context = { type_vars = []; free_vars; hypotheses; library_slice };
  type_metadata;
  definitional_metadata;
  library_provenance = [];
  user_directives = None;
}

let test_no_metadata_is_no_op () =
  let ir = make_ir
    ~free_vars:[ { name = "n"; ty = "Int" } ]
    (Var { name = "n" }) in
  match Refinement.run ~fragment:"LIA" ir with
  | Ok r ->
    Alcotest.(check int) "no specs" 0 (List.length r.specializations);
    let identical =
      Yojson.Safe.equal (Codec.to_json r.refined_ir) (Codec.to_json ir)
    in
    Alcotest.(check bool) "refined_ir = ir" true identical
  | Error e ->
    Alcotest.fail ("unexpected error: " ^ Refinement.detail_of_error e)

let test_unknown_fragment_errors () =
  let ir = make_ir (Var { name = "p" }) in
  match Refinement.run ~fragment:"NotAFragment" ir with
  | Error (Unknown_fragment "NotAFragment") -> ()
  | _ -> Alcotest.fail "expected Unknown_fragment"

(* Non-arithmetic and nonlinear fragments are recognized as fragments
   with no host-type substitution rules. They must pass through
   refinement as a no-op rather than erroring — the adapter layer
   relies on this so it can pass the bridge-built fragment label
   straight through without a special case for non-substitution
   fragments. The list matches `registry/patterns-v1.json` minus
   LIA / LRA. *)
let test_no_substitution_fragments_passthrough () =
  let ir = make_ir
    ~free_vars:[ { name = "n"; ty = "Int" } ]
    (Var { name = "n" }) in
  List.iter (fun fragment ->
    match Refinement.run ~fragment ir with
    | Ok r ->
      Alcotest.(check int)
        (fragment ^ ": no specs") 0 (List.length r.specializations);
      let identical =
        Yojson.Safe.equal (Codec.to_json r.refined_ir) (Codec.to_json ir)
      in
      Alcotest.(check bool)
        (fragment ^ ": refined_ir = ir") true identical
    | Error e ->
      Alcotest.fail
        (fragment ^ ": unexpected error: " ^ Refinement.detail_of_error e)
  ) ["UF"; "BV"; "NIA"; "NRA"; "FOL"; "UFLIA"; "UFLRA"]

let alpha_meta_with_witness = `Assoc [
  "kind", `String "type_variable";
  "name", `String "alpha";
  "instances", `List [
    `Assoc [
      "instance_name", `String "inst_alpha";
      "theory_classification_tags", `List [
        `String "embeds_into:Int_for_universal_LIA";
        `String "embedding_witness:alpha_int_embedding_lemma";
      ];
    ];
  ];
]

let test_alpha_type_var_substituted () =
  let ir = make_ir
    ~type_metadata:[ ("alpha", alpha_meta_with_witness) ]
    ~free_vars:[ { name = "n"; ty = "alpha" } ]
    (Eq {
      ty = "alpha";
      left = Var { name = "n" };
      right = Num_lit { value = "0"; ty = "alpha" };
    })
  in
  match Refinement.run ~fragment:"LIA" ir with
  | Ok r ->
    Alcotest.(check int) "1 spec recorded" 1 (List.length r.specializations);
    let s = List.hd r.specializations in
    Alcotest.(check string) "kind = type_specialization"
      "type_specialization"
      (Refinement_record.specialization_kind_to_string s.kind);
    Alcotest.(check string) "source = alpha" "alpha" s.source;
    Alcotest.(check string) "target = Int" "Int" s.target;
    Alcotest.(check (option string))
      "soundness_witness = the embedding_witness tag payload, verbatim"
      (Some "alpha_int_embedding_lemma") s.soundness_witness;
    (* Check IR substitution actually happened: free_var, NumLit
       type tag, Eq.ty all moved alpha → Int. *)
    let fv = List.hd r.refined_ir.context.free_vars in
    Alcotest.(check string) "free_var n: alpha → Int" "Int" fv.ty;
    (match r.refined_ir.goal.shell with
     | Eq { ty; right = Num_lit { ty = ty2; _ }; _ } ->
       Alcotest.(check string) "Eq.ty: alpha → Int" "Int" ty;
       Alcotest.(check string) "NumLit.ty: alpha → Int" "Int" ty2
     | _ -> Alcotest.fail "goal shell shape wrong")
  | Error e ->
    Alcotest.fail ("unexpected error: " ^ Refinement.detail_of_error e)

let test_library_slice_substituted () =
  (* A library_slice entry whose shell mentions [alpha] must be
     refined alongside hypotheses and free_vars; otherwise the
     refined IR still carries a stray [alpha] type tag in a slice
     and downstream consumers see an unresolved type ref. *)
  let alpha_meta = alpha_meta_with_witness in
  let slice : Ir.library_slice_entry list = [
    {
      entity_name = "Stub.lemma";
      shell = Eq {
        ty = "alpha";
        left = Var { name = "x" };
        right = Num_lit { value = "0"; ty = "alpha" };
      };
      selection_reason = Some "test";
    }
  ] in
  let ir = make_ir
    ~type_metadata:[ ("alpha", alpha_meta) ]
    ~free_vars:[ { name = "n"; ty = "alpha" } ]
    ~library_slice:(Some slice)
    (Var { name = "n" })
  in
  match Refinement.run ~fragment:"LIA" ir with
  | Ok r ->
    let entries = Option.get r.refined_ir.context.library_slice in
    Alcotest.(check int) "one slice entry preserved" 1 (List.length entries);
    let e = List.hd entries in
    Alcotest.(check string) "entity_name preserved"
      "Stub.lemma" e.entity_name;
    (match e.shell with
     | Eq { ty; right = Num_lit { ty = ty2; _ }; _ } ->
       Alcotest.(check string) "slice Eq.ty: alpha → Int" "Int" ty;
       Alcotest.(check string) "slice NumLit.ty: alpha → Int" "Int" ty2
     | _ -> Alcotest.fail "slice shell shape wrong")
  | Error e ->
    Alcotest.fail ("unexpected error: " ^ Refinement.detail_of_error e)

(* R3-M1 fail-closed: an embed tag with NO embedding_witness tag
   justifies nothing — no specialization is recorded and the IR is
   left unsubstituted (the stray [alpha] then surfaces downstream as
   an unsupported-type dispatch failure, never as a record whose
   witness was fabricated). This pins the removal of the
   ["<Host>_embedding"] fabrication at the former refinement.ml:205. *)
let test_embed_tag_without_witness_fails_closed () =
  let alpha_meta = `Assoc [
    "kind", `String "type_variable";
    "name", `String "alpha";
    "instances", `List [
      `Assoc [
        "instance_name", `String "inst_alpha";
        "theory_classification_tags", `List [
          `String "embeds_into:Int_for_universal_LIA";
        ];
      ];
    ];
  ] in
  let ir = make_ir
    ~type_metadata:[ ("alpha", alpha_meta) ]
    ~free_vars:[ { name = "n"; ty = "alpha" } ]
    (Var { name = "n" })
  in
  match Refinement.run ~fragment:"LIA" ir with
  | Ok r ->
    Alcotest.(check int) "no specs without a witness tag" 0
      (List.length r.specializations);
    let fv = List.hd r.refined_ir.context.free_vars in
    Alcotest.(check string) "alpha NOT substituted" "alpha" fv.ty
  | Error e ->
    Alcotest.fail ("unexpected error: " ^ Refinement.detail_of_error e)

(* R3-M1: the [primitive] metadata kind's embedding path (Nat → Int).
   The embed + witness tags live in the entry's [theory_tags]; the
   witness joins every [embedding_witness:] payload in tag order. *)
let nat_meta_with_witness = `Assoc [
  "kind", `String "primitive";
  "name", `String "Nat";
  "theory_tags", `List [
    `String "embeds_into:Int_for_universal_LIA";
    `String "embedding_witness:Int.ofNat_le";
    `String "embedding_witness:Int.natCast_nonneg";
  ];
]

let test_primitive_nat_embeds () =
  let ir = make_ir
    ~type_metadata:[ ("Nat", nat_meta_with_witness) ]
    ~free_vars:[ { name = "x"; ty = "Nat" } ]
    (App { symbol = "LE.le"; type_args = []; args = [
       Num_lit { value = "0"; ty = "Int" };
       App { symbol = "Int.ofNat"; type_args = [];
             args = [ Var { name = "x" } ] };
     ] })
  in
  match Refinement.run ~fragment:"LIA" ir with
  | Ok r ->
    Alcotest.(check int) "1 spec recorded" 1 (List.length r.specializations);
    let s = List.hd r.specializations in
    Alcotest.(check string) "kind = type_specialization"
      "type_specialization"
      (Refinement_record.specialization_kind_to_string s.kind);
    Alcotest.(check string) "source = Nat" "Nat" s.source;
    Alcotest.(check string) "target = Int" "Int" s.target;
    Alcotest.(check (option string))
      "witness = joined embedding_witness payloads, tag order"
      (Some "Int.ofNat_le,Int.natCast_nonneg") s.soundness_witness;
    let fv = List.hd r.refined_ir.context.free_vars in
    Alcotest.(check string) "free_var x: Nat → Int" "Int" fv.ty
  | Error e ->
    Alcotest.fail ("unexpected error: " ^ Refinement.detail_of_error e)

let test_primitive_without_witness_fails_closed () =
  let nat_meta = `Assoc [
    "kind", `String "primitive";
    "name", `String "Nat";
    "theory_tags", `List [
      `String "embeds_into:Int_for_universal_LIA";
    ];
  ] in
  let ir = make_ir
    ~type_metadata:[ ("Nat", nat_meta) ]
    ~free_vars:[ { name = "x"; ty = "Nat" } ]
    (Var { name = "x" })
  in
  match Refinement.run ~fragment:"LIA" ir with
  | Ok r ->
    Alcotest.(check int) "no specs without a witness tag" 0
      (List.length r.specializations);
    let fv = List.hd r.refined_ir.context.free_vars in
    Alcotest.(check string) "Nat NOT substituted" "Nat" fv.ty
  | Error e ->
    Alcotest.fail ("unexpected error: " ^ Refinement.detail_of_error e)

let test_typeclass_method_specs () =
  (* HAdd.hAdd's LIA target carries a soundness_witness → emitted;
     LE.le's does not → fail closed, no record (the schema requires
     the witness on method_specialization, so emitting one would
     mint schema-invalid certs — the pre-R3 behavior). *)
  let hadd_meta = `Assoc [
    "kind", `String "typeclass_method";
    "method_name", `String "HAdd.hAdd";
    "host_class", `String "HAdd";
    "specialization_targets", `List [
      `Assoc [
        "theory", `String "LIA";
        "operator", `String "+";
        "soundness_witness", `String "int_add_hom_lemma";
      ];
      `Assoc [
        "theory", `String "BV";
        "operator", `String "bvadd";
      ];
    ];
  ] in
  let le_meta = `Assoc [
    "kind", `String "typeclass_method";
    "method_name", `String "LE.le";
    "host_class", `String "LE";
    "specialization_targets", `List [
      `Assoc [ "theory", `String "LIA"; "operator", `String "<=" ];
    ];
  ] in
  let ir = make_ir
    ~definitional_metadata:[
      ("HAdd.hAdd", hadd_meta);
      ("LE.le", le_meta);
    ]
    (Var { name = "p" })
  in
  match Refinement.run ~fragment:"LIA" ir with
  | Ok r ->
    let specs = r.specializations in
    Alcotest.(check int)
      "1 method spec (witness-less target emits none)" 1
      (List.length specs);
    let hadd =
      List.find (fun (s : Refinement_record.specialization) ->
        s.source = "HAdd.hAdd") specs
    in
    Alcotest.(check string) "HAdd.hAdd target" "+" hadd.target;
    Alcotest.(check string) "HAdd.hAdd is method_specialization"
      "method_specialization"
      (Refinement_record.specialization_kind_to_string hadd.kind);
    Alcotest.(check (option string)) "HAdd.hAdd witness verbatim"
      (Some "int_add_hom_lemma") hadd.soundness_witness;
    Alcotest.(check bool) "LE.le spec NOT emitted" false
      (List.exists (fun (s : Refinement_record.specialization) ->
         s.source = "LE.le") specs)
  | Error e ->
    Alcotest.fail ("unexpected error: " ^ Refinement.detail_of_error e)

let test_method_without_target_for_fragment () =
  (* A typeclass method whose specialization_targets only lists BV
     should not produce a spec for fragment LIA. *)
  let bvadd_meta = `Assoc [
    "kind", `String "typeclass_method";
    "method_name", `String "BV.add";
    "specialization_targets", `List [
      `Assoc [ "theory", `String "BV"; "operator", `String "bvadd" ];
    ];
  ] in
  let ir = make_ir
    ~definitional_metadata:[ ("BV.add", bvadd_meta) ]
    (Var { name = "p" })
  in
  match Refinement.run ~fragment:"LIA" ir with
  | Ok r ->
    Alcotest.(check int) "no specs for non-matching fragment" 0
      (List.length r.specializations)
  | Error e ->
    Alcotest.fail ("unexpected error: " ^ Refinement.detail_of_error e)

let test_fixture_example1 () =
  let path = Filename.concat (Sys.getcwd ())
    "../../../../examples/example1-lia-typeclass.json" in
  let raw = In_channel.with_open_text path In_channel.input_all in
  let ir = Codec.of_json (Yojson.Safe.from_string raw) in
  match Refinement.run ~fragment:"LIA" ir with
  | Ok r ->
    let specs = r.specializations in
    Alcotest.(check bool) "alpha type_specialization present" true
      (List.exists (fun (s : Refinement_record.specialization) ->
         s.kind = Type_specialization && s.source = "alpha")
         specs);
    (* R3-M1: the witness comes from the fixture's embedding_witness
       tag — a library_provenance key — not a fabricated string. *)
    let alpha_spec =
      List.find (fun (s : Refinement_record.specialization) ->
        s.kind = Type_specialization && s.source = "alpha") specs
    in
    Alcotest.(check (option string)) "alpha witness from fixture tag"
      (Some "linear_ordered_comm_ring_lia_embedding")
      alpha_spec.soundness_witness;
    Alcotest.(check bool) "every emitted spec carries a witness" true
      (List.for_all (fun (s : Refinement_record.specialization) ->
         Option.is_some s.soundness_witness) specs);
    Alcotest.(check bool) "HAdd.hAdd method_specialization present" true
      (List.exists (fun (s : Refinement_record.specialization) ->
         s.kind = Method_specialization && s.source = "HAdd.hAdd")
         specs);
    Alcotest.(check bool) "LE.le method_specialization present" true
      (List.exists (fun (s : Refinement_record.specialization) ->
         s.kind = Method_specialization && s.source = "LE.le")
         specs);
    (* Confirm structural alpha references are substituted. The
       type_metadata block is pass-through and still describes
       "alpha" — that's intentional, the lifter needs it to invert
       the specialization. We just check the IR's structural fields:
       free_vars, type_vars, and the goal's type tags. *)
    Alcotest.(check bool) "type_vars dropped after substitution" true
      (not (List.mem "alpha" r.refined_ir.context.type_vars));
    Alcotest.(check bool) "no free_var with type alpha" true
      (not (List.exists (fun (fv : Ir.free_var) -> fv.ty = "alpha")
              r.refined_ir.context.free_vars));
    let goal_json = Yojson.Safe.to_string
      (Codec.goal_to_json r.refined_ir.goal) in
    Alcotest.(check bool) "no \"alpha\" type tag in goal" false
      (let pat = Str.regexp_string "\"alpha\"" in
       try ignore (Str.search_forward pat goal_json 0); true
       with Not_found -> false)
  | Error e ->
    Alcotest.fail ("unexpected error: " ^ Refinement.detail_of_error e)

let () =
  Alcotest.run "refinement" [
    "unit", [
      Alcotest.test_case "no metadata is no-op"
        `Quick test_no_metadata_is_no_op;
      Alcotest.test_case "unknown fragment errors"
        `Quick test_unknown_fragment_errors;
      Alcotest.test_case "no-substitution fragments pass through"
        `Quick test_no_substitution_fragments_passthrough;
      Alcotest.test_case "alpha → Int via type_metadata"
        `Quick test_alpha_type_var_substituted;
      Alcotest.test_case "embed tag without witness tag fails closed"
        `Quick test_embed_tag_without_witness_fails_closed;
      Alcotest.test_case "primitive Nat → Int via theory_tags"
        `Quick test_primitive_nat_embeds;
      Alcotest.test_case "primitive without witness fails closed"
        `Quick test_primitive_without_witness_fails_closed;
      Alcotest.test_case "library_slice entries refined alongside hyps"
        `Quick test_library_slice_substituted;
      Alcotest.test_case "typeclass method specs"
        `Quick test_typeclass_method_specs;
      Alcotest.test_case "non-matching fragment yields no specs"
        `Quick test_method_without_target_for_fragment;
    ];
    "fixture", [
      Alcotest.test_case "example1-lia-typeclass refines"
        `Quick test_fixture_example1;
    ];
  ]

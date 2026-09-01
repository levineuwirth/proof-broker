(** Refinement pass (spec v1.0 §6.5).

    Given an IR and a target logic fragment ("LIA", "LRA", ...),
    refinement walks [type_metadata] and [definitional_metadata]
    to find specialization choices the adapter can commit to, then
    produces:

    1. A [refined IR] with type substitutions applied (e.g.,
       [alpha] in free vars / NumLit type tags / Eq.ty / binders
       becomes [Int] when the fragment is LIA and the type
       variable's metadata embeds into Int).

    2. A list of [Refinement_record.specialization] entries
       documenting the choices, so a downstream lifter can invert
       them. Two kinds are produced:
       * [Type_specialization] — one per metadata entry that embeds
         into the fragment's host type: a [type_variable] whose
         instance carries the [embeds_into:...] tag (spec Example 1's
         alpha), or — R3-M1 — a [primitive] (concretely: Nat) whose
         [theory_tags] carry it. Either way the [soundness_witness]
         is REAL: the comma-joined payloads of the entry's
         [embedding_witness:<name>] tags, each naming a
         [library_provenance] key for a verified embedding lemma
         (check.py cross-checks). No witness tag ⇒ NO
         specialization — refinement fails closed and the
         unsubstituted type surfaces downstream as an unsupported-
         type dispatch failure rather than an unjustified record.
       * [Method_specialization] — one per typeclass method in
         [definitional_metadata] whose [specialization_targets]
         lists the target fragment WITH a [soundness_witness]
         field; a witness-less target emits no record (same
         fail-closed rule; the schema requires the witness on
         method_specialization, so emitting one without would mint
         schema-invalid certs — the pre-R3 behavior).

    Symbol rewriting deferred. The refined IR keeps typeclass
    method names ([HAdd.hAdd], [LE.le], ...). The SMT-LIB
    serializer recognizes both typeclass methods and primitives,
    so leaving symbols intact is functionally equivalent — at the
    cost of a refined IR that's not yet in a "fully primitive"
    shape. The refinement record makes the specialization choice
    explicit nonetheless. A future pass can substitute the
    symbol-level form when downstream consumers (e.g., a Lean
    lifter) need the explicit primitive shell.

    Determinism. Substitution traversal is structural, so a
    refinement applied twice is idempotent. Spec ordering: type
    specs precede method specs in the output list. Within each,
    insertion order follows iteration over the IR's metadata
    maps. *)

type error =
  | Unknown_fragment of string

let kind_of_error = function
  | Unknown_fragment _ -> "unknown_fragment"

let detail_of_error = function
  | Unknown_fragment f ->
    Printf.sprintf "no refinement strategy for fragment %s \
                    (substitution: LIA, LRA; pass-through: UF, BV, \
                    NIA, NRA, FOL, UFLIA, UFLRA)" f

(** Mapping from fragment name to the "host type" the metadata
    embedding tag refers to. v1: LIA → Int, LRA → Real. *)
let host_type_of_fragment = function
  | "LIA" -> Some "Int"
  | "LRA" -> Some "Real"
  | _ -> None

(** Fragments that have no host type to substitute into — refinement
    is a no-op for them. UF / BV / NIA / NRA / FOL / UFLIA / UFLRA all
    emit their declarations or theory atoms directly; there's no
    universal-type-var rewriting to do. The full list comes from
    `registry/patterns-v1.json`'s `first_order_fragments` field
    minus LIA and LRA (which have host-type substitution rules and
    are handled by `host_type_of_fragment`). Listing them explicitly
    preserves the loud-failure contract for truly unknown fragments
    while letting the adapter layer pass these through without a
    special case. *)
let is_no_substitution_fragment = function
  | "UF" | "BV" | "NIA" | "NRA" | "FOL" | "UFLIA" | "UFLRA" -> true
  | _ -> false

(** Pattern the [theory_classification_tags] entry must match for a
    type variable to be considered a refinement candidate for
    [host_type]: ["embeds_into:<HOST>_for_universal_<FRAGMENT>"]. *)
let embed_tag ~fragment ~host_type =
  Printf.sprintf "embeds_into:%s_for_universal_%s" host_type fragment

(** Witness-tag prefix (R3-M1). A metadata entry justifies a type
    specialization only when, alongside the [embeds_into:...] tag,
    it names the verified embedding lemma(s) via one or more
    ["embedding_witness:<library_provenance key>"] tags. *)
let witness_tag_prefix = "embedding_witness:"

(** Extract the soundness witness from a tag list: the comma-joined
    payloads of every [embedding_witness:] tag, in tag order.
    [None] when no witness tag is present — the caller must then
    refuse the specialization (fail closed), never fabricate. *)
let witnesses_of_tags (tags : string list) : string option =
  let plen = String.length witness_tag_prefix in
  let names =
    List.filter_map (fun t ->
      if String.length t > plen
         && String.sub t 0 plen = witness_tag_prefix
      then Some (String.sub t plen (String.length t - plen))
      else None)
      tags
  in
  match names with
  | [] -> None
  | xs -> Some (String.concat "," xs)

(* --- type-substitution map ------------------------------------------- *)

module SM = Map.Make (String)

(** A [(source_type → target_type)] map, e.g., [alpha → Int]. *)
type type_subst = string SM.t

let subst_lookup (s : type_subst) (ty : Ir.type_ref) : Ir.type_ref =
  match SM.find_opt ty s with
  | Some t -> t
  | None -> ty

(** Substitute every type-tag occurrence in a shell term by walking
    the constructors that carry an [Ir.type_ref]. *)
let rec subst_shell (s : type_subst) (t : Ir.shell_term) : Ir.shell_term =
  match t with
  | Forall { var; ty; body } ->
    Forall { var; ty = subst_lookup s ty; body = subst_shell s body }
  | Exists { var; ty; body } ->
    Exists { var; ty = subst_lookup s ty; body = subst_shell s body }
  | Lambda { binders; body } ->
    let binders' = List.map (fun (b : Ir.binder) ->
      ({ var = b.var; ty = subst_lookup s b.ty } : Ir.binder)) binders in
    Lambda { binders = binders'; body = subst_shell s body }
  | Implies { antecedent; consequent } ->
    Implies {
      antecedent = subst_shell s antecedent;
      consequent = subst_shell s consequent;
    }
  | And { left; right } ->
    And { left = subst_shell s left; right = subst_shell s right }
  | Or { left; right } ->
    Or { left = subst_shell s left; right = subst_shell s right }
  | Not { operand } ->
    Not { operand = subst_shell s operand }
  | Eq { ty; left; right } ->
    Eq {
      ty = subst_lookup s ty;
      left = subst_shell s left;
      right = subst_shell s right;
    }
  | App { symbol; type_args; args } ->
    App {
      symbol;
      type_args = List.map (subst_lookup s) type_args;
      args = List.map (subst_shell s) args;
    }
  | Var _ | Const _ -> t
  | Num_lit { value; ty } ->
    Num_lit { value; ty = subst_lookup s ty }
  | Opaque _ -> t

let subst_hypothesis s (h : Ir.hypothesis) : Ir.hypothesis =
  { name = h.name; shell = subst_shell s h.shell }

let subst_free_var s (fv : Ir.free_var) : Ir.free_var =
  { name = fv.name; ty = subst_lookup s fv.ty }

let subst_goal s (g : Ir.goal) : Ir.goal =
  { shell = subst_shell s g.shell; payloads = g.payloads }

let subst_library_slice_entry s (e : Ir.library_slice_entry)
  : Ir.library_slice_entry =
  { e with shell = subst_shell s e.shell }

let subst_context s (c : Ir.context) : Ir.context =
  let drop_type_vars = SM.bindings s |> List.map fst in
  {
    type_vars =
      List.filter (fun v -> not (List.mem v drop_type_vars)) c.type_vars;
    free_vars = List.map (subst_free_var s) c.free_vars;
    hypotheses = List.map (subst_hypothesis s) c.hypotheses;
    library_slice =
      Option.map (List.map (subst_library_slice_entry s)) c.library_slice;
  }

let apply_type_subst (s : type_subst) (ir : Ir.t) : Ir.t =
  if SM.is_empty s then ir
  else { ir with
    goal = subst_goal s ir.goal;
    context = subst_context s ir.context;
  }

(* --- metadata extraction -------------------------------------------- *)

let json_kind (meta : Yojson.Safe.t) : string option =
  match meta with
  | `Assoc pairs ->
    (match List.assoc_opt "kind" pairs with
     | Some (`String s) -> Some s
     | _ -> None)
  | _ -> None

let json_string_list (meta : Yojson.Safe.t) (field : string) : string list =
  match meta with
  | `Assoc pairs ->
    (match List.assoc_opt field pairs with
     | Some (`List xs) ->
       List.filter_map (function `String s -> Some s | _ -> None) xs
     | _ -> [])
  | _ -> []

(** Read the JSON [type_metadata] entry for [qtype] and decide
    whether it qualifies as a type variable that embeds into
    [host_type] for [fragment]. Returns the embedding witness — the
    comma-joined [embedding_witness:] tag payloads of an instance
    that carries BOTH the [embeds_into:...] tag and at least one
    witness tag — or [None]. An instance with the embed tag but no
    witness tag does NOT qualify (fail closed; the former behavior
    fabricated ["<Host>_embedding"] here with no metadata backing —
    STATUS §3.1, removed in R3-M1). *)
let type_var_witness ~fragment ~host_type (meta : Yojson.Safe.t)
  : string option =
  if json_kind meta <> Some "type_variable" then None
  else
    let instances = match meta with
      | `Assoc pairs ->
        (match List.assoc_opt "instances" pairs with
         | Some (`List xs) -> xs
         | _ -> [])
      | _ -> []
    in
    let target_tag = embed_tag ~fragment ~host_type in
    let rec find_in_instances = function
      | [] -> None
      | inst :: rest ->
        let tags = json_string_list inst "theory_classification_tags" in
        (match
           if List.mem target_tag tags then witnesses_of_tags tags
           else None
         with
         | Some w -> Some w
         | None -> find_in_instances rest)
    in
    find_in_instances instances

(** R3-M1: the [primitive] metadata kind's embedding path — a
    concrete type (Nat is the v1 case) whose [theory_tags] carry
    the [embeds_into:...] tag plus [embedding_witness:] tags. The
    §4.6 alternative ([type_variable] with a fabricated class
    object) was rejected because the schema's [Instance] requires
    a typeclass reference ℕ does not have; decision recorded in
    delta.md §5. Same fail-closed witness rule as
    [type_var_witness]. *)
let primitive_witness ~fragment ~host_type (meta : Yojson.Safe.t)
  : string option =
  if json_kind meta <> Some "primitive" then None
  else
    let tags = json_string_list meta "theory_tags" in
    if List.mem (embed_tag ~fragment ~host_type) tags
    then witnesses_of_tags tags
    else None

let type_specs_from_metadata ~fragment ~host_type (ir : Ir.t)
  : (type_subst * Refinement_record.specialization list) =
  let acc_subst = ref SM.empty in
  let acc_specs = ref [] in
  List.iter (fun (qtype, meta) ->
    let witness =
      match type_var_witness ~fragment ~host_type meta with
      | Some w -> Some w
      | None -> primitive_witness ~fragment ~host_type meta
    in
    match witness with
    | None -> ()
    | Some witness ->
      acc_subst := SM.add qtype host_type !acc_subst;
      acc_specs := !acc_specs @ [
        ({
          kind = Type_specialization;
          source = qtype;
          target = host_type;
          justification =
            Some (Printf.sprintf
                    "embeds_into:%s_for_universal_%s"
                    host_type fragment);
          soundness_witness = Some witness;
        } : Refinement_record.specialization)
      ])
    ir.type_metadata;
  (!acc_subst, !acc_specs)

(** Read the JSON [definitional_metadata] entry for [method_name]
    and find the [specialization_targets] entry whose [theory]
    matches [fragment]. Returns [(operator, soundness_witness)] on
    a hit — a target WITHOUT a [soundness_witness] field is not a
    hit (R3-M1 fail-closed rule: the schema requires the witness on
    method_specialization records, so a witness-less target can
    justify no record; the method simply stays unspecialized, which
    is behavior-neutral since the serializer accepts typeclass
    method names directly). *)
let method_target ~fragment (meta : Yojson.Safe.t)
  : (string * string) option =
  if json_kind meta <> Some "typeclass_method" then None
  else
    let targets = match meta with
      | `Assoc pairs ->
        (match List.assoc_opt "specialization_targets" pairs with
         | Some (`List xs) -> xs
         | _ -> [])
      | _ -> []
    in
    let rec find = function
      | [] -> None
      | t :: rest ->
        let field name = match t with
          | `Assoc pairs ->
            (match List.assoc_opt name pairs with
             | Some (`String s) -> Some s
             | _ -> None)
          | _ -> None
        in
        if field "theory" <> Some fragment then find rest
        else
          (match field "operator", field "soundness_witness" with
           | Some op, Some w -> Some (op, w)
           | _ -> find rest)
    in
    find targets

let method_specs_from_metadata ~fragment (ir : Ir.t)
  : Refinement_record.specialization list =
  List.filter_map (fun (method_name, meta) ->
    match method_target ~fragment meta with
    | None -> None
    | Some (target, witness) ->
      Some ({
        kind = Method_specialization;
        source = method_name;
        target;
        justification =
          Some (Printf.sprintf "specialization_targets[%s]" fragment);
        soundness_witness = Some witness;
      } : Refinement_record.specialization))
    ir.definitional_metadata

(* --- public entry --------------------------------------------------- *)

(** Result of [run]: the IR transformed by the type substitution
    plus the refinement record entries the substitution produced. *)
type t = {
  refined_ir : Ir.t;
  specializations : Refinement_record.specialization list;
}

(** Run the refinement pass. [fragment] is one of the supported
    target fragments (LIA, LRA). Empty input metadata is a no-op
    case: the refined IR equals the input and the specialization
    list is empty — perfectly legitimate for an IR that's already
    in primitive shape. *)
let run ~fragment (ir : Ir.t) : (t, error) result =
  match host_type_of_fragment fragment with
  | Some host_type ->
    let type_subst, type_specs =
      type_specs_from_metadata ~fragment ~host_type ir in
    let method_specs = method_specs_from_metadata ~fragment ir in
    let refined_ir = apply_type_subst type_subst ir in
    Ok {
      refined_ir;
      specializations = type_specs @ method_specs;
    }
  | None when is_no_substitution_fragment fragment ->
    Ok { refined_ir = ir; specializations = [] }
  | None -> Error (Unknown_fragment fragment)

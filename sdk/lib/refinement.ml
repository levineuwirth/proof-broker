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
       * [Type_specialization] — one per type variable whose
         metadata says it embeds into the fragment's host type.
         The [soundness_witness] is the embedding lemma name from
         [theory_classification_tags] (the [embeds_into:LEMMA] tag
         is taken as the canonical witness).
       * [Method_specialization] — one per typeclass method in
         [definitional_metadata] whose [specialization_targets]
         lists the target fragment.

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

(** Read the JSON [type_metadata] entry for [qtype] and decide
    whether it qualifies as a type variable that embeds into
    [host_type] for [fragment]. Returns the embedding witness
    (the lemma name extracted from the [embeds_into:...] tag) on
    success, [None] otherwise. *)
let type_var_witness ~fragment ~host_type (meta : Yojson.Safe.t)
  : string option =
  let kind = match meta with
    | `Assoc pairs ->
      (match List.assoc_opt "kind" pairs with
       | Some (`String s) -> Some s
       | _ -> None)
    | _ -> None
  in
  if kind <> Some "type_variable" then None
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
        let tags = match inst with
          | `Assoc pairs ->
            (match List.assoc_opt "theory_classification_tags" pairs with
             | Some (`List xs) ->
               List.filter_map
                 (function `String s -> Some s | _ -> None) xs
             | _ -> [])
          | _ -> []
        in
        if List.mem target_tag tags then
          (* Witness: the embedding lemma. The tag itself is the
             canonical reference; downstream lifters look up the
             lemma by this name in library_provenance. *)
          Some (Printf.sprintf "%s_embedding" host_type)
        else find_in_instances rest
    in
    find_in_instances instances

let type_specs_from_metadata ~fragment ~host_type (ir : Ir.t)
  : (type_subst * Refinement_record.specialization list) =
  let acc_subst = ref SM.empty in
  let acc_specs = ref [] in
  List.iter (fun (qtype, meta) ->
    match type_var_witness ~fragment ~host_type meta with
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
    matches [fragment]. Returns the [operator] string on a hit. *)
let method_target ~fragment (meta : Yojson.Safe.t) : string option =
  let kind = match meta with
    | `Assoc pairs ->
      (match List.assoc_opt "kind" pairs with
       | Some (`String s) -> Some s
       | _ -> None)
    | _ -> None
  in
  if kind <> Some "typeclass_method" then None
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
        let theory = match t with
          | `Assoc pairs ->
            (match List.assoc_opt "theory" pairs with
             | Some (`String s) -> Some s
             | _ -> None)
          | _ -> None
        in
        if theory <> Some fragment then find rest
        else
          (match t with
           | `Assoc pairs ->
             (match List.assoc_opt "operator" pairs with
              | Some (`String op) -> Some op
              | _ -> None)
           | _ -> None)
    in
    find targets

let method_specs_from_metadata ~fragment (ir : Ir.t)
  : Refinement_record.specialization list =
  List.filter_map (fun (method_name, meta) ->
    match method_target ~fragment meta with
    | None -> None
    | Some target ->
      Some ({
        kind = Method_specialization;
        source = method_name;
        target;
        justification =
          Some (Printf.sprintf "specialization_targets[%s]" fragment);
        soundness_witness = None;
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

(** Quotient elimination pass (spec v1.0 §5.1, example 3 §11.3).

    Reduces a goal stated at a quotient type to a goal at the
    underlying type, leaving behind enough inversion data for the
    lifting layer to wrap the resulting proof in the appropriate
    elimination/equality principle structure.

    Three concurrent rewrites, applied bottom-up over the goal and
    each hypothesis:

    1. [App { symbol = lifted; ... }] where [lifted] has
       [kind = "lifted_to_quotient"] becomes
       [App { symbol = underlying_function.name; ... }].
    2. [Eq { ty = qtype; left; right }] where [qtype] has
       [construction_kind = "quotient"] becomes the equivalence
       relation applied to [left] and [right] (beta-reducing the
       relation's two-binder lambda body via [Substitution.subst]).
    3. [free_vars] / [Forall] / [Exists] / [Lambda] binders whose
       type is a quotient type get their type rewritten to the
       quotient's [underlying_type].

    Goal-shaped predicates [App f [x : qtype, ...]] are *not*
    rewritten: that would require lifting the predicate through
    [Quot.ind], which is materially harder than the equality case.
    The pass leaves them untouched and depends on
    [Substitution.subst] / type-rewriting only firing on syntactic
    matches; this is consistent with the "skip-don't-miscompile"
    discipline the other v1 passes follow.

    Soundness obligation. Each rewrite preserves provability under
    the home system's foundational logic:
      * Replacing a lifted-to-quotient application with the
        underlying function is the [Quot.lift] beta rule for that
        symbol, witnessed by the [lifting_obligation.witness].
      * Replacing equality at a quotient with the equivalence
        relation is the [Quot.sound] / [Quot.exact] direction,
        witnessed by [equality_principle] and [equivalence_proof].
      * Rewriting a free variable's quotient type to the underlying
        type corresponds to introducing a representative under the
        [elimination_principle].
    The lifting layer reverses all three using the inversion data.

    Configuration. Reads
    [user_directives.rewriter_preferences.enable_quotient_elimination]
    (a [bool]). When [None] or [Some false] the pass is
    [Skipped_preconditions]; the IR is returned unchanged.

    Out of scope for v1: nested quotients in argument positions,
    higher-order arguments to lifted functions (the underlying-fn
    substitution only rewrites symbol slots), goals not in equality
    form. Such IRs run through this pass and produce an [Applied] or
    [No_op] entry over the parts the pass does recognize, leaving
    other parts untouched. *)

module SS = Set.Make (String)
module SM = Map.Make (String)

(* --- type-metadata reader -------------------------------------------- *)

(** Information harvested from [type_metadata[qtype]] for a single
    quotient type. [equivalence_relation_lambda] is the body lambda
    parsed back into [Ir.shell_term]; [equivalence_proof],
    [elimination_principle], [equality_principle] are name strings
    consumed only by the inversion data. *)
type quotient_info = {
  qtype : string;
  underlying_type : string;
  equivalence_relation_lambda : Ir.shell_term;
  equivalence_proof : string;
  elimination_principle : string;
  equality_principle : string;
}

let json_string_field (j : Yojson.Safe.t) (k : string) : string option =
  match j with
  | `Assoc pairs ->
    (match List.assoc_opt k pairs with
     | Some (`String s) -> Some s
     | _ -> None)
  | _ -> None

let json_field (j : Yojson.Safe.t) (k : string) : Yojson.Safe.t option =
  match j with
  | `Assoc pairs -> List.assoc_opt k pairs
  | _ -> None

(** Parse a single [type_metadata] entry into a [quotient_info] iff it
    declares construction_kind = "quotient" with all the required
    fields. Anything off-shape returns [None] — the pass silently
    skips, never raises. *)
let parse_quotient_info (qtype : string) (meta : Yojson.Safe.t)
  : quotient_info option =
  match json_string_field meta "kind" with
  | Some "type_constructor_application" ->
    (match json_field meta "constructor" with
     | Some ctor ->
       (match json_string_field ctor "construction_kind" with
        | Some "quotient" ->
          let underlying = json_string_field ctor "underlying_type" in
          let elim = json_string_field ctor "elimination_principle" in
          let equality = json_string_field ctor "equality_principle" in
          let eqv = json_field ctor "equivalence_relation" in
          (match underlying, elim, equality, eqv with
           | Some u, Some e, Some q, Some eqv_obj ->
             let proof = json_string_field eqv_obj "equivalence_proof" in
             let shell =
               match json_field eqv_obj "shell" with
               | Some s ->
                 (try Some (Codec.shell_of_json s)
                  with Codec.Decode_error _ -> None)
               | None -> None
             in
             (match shell, proof with
              | Some lam, Some pr ->
                Some {
                  qtype;
                  underlying_type = u;
                  equivalence_relation_lambda = lam;
                  equivalence_proof = pr;
                  elimination_principle = e;
                  equality_principle = q;
                }
              | _ -> None)
           | _ -> None)
        | _ -> None)
     | None -> None)
  | _ -> None

(** Build [qtype_name -> quotient_info] from [ir.type_metadata]. Only
    entries that fully parse are included; everything else is dropped
    silently. *)
let collect_quotient_types (ir : Ir.t) : quotient_info SM.t =
  List.fold_left
    (fun acc (name, meta) ->
      match parse_quotient_info name meta with
      | Some qi -> SM.add name qi acc
      | None -> acc)
    SM.empty ir.type_metadata

(* --- definitional-metadata reader for lifted_to_quotient ------------- *)

(** Information for a single lifted-to-quotient symbol. The lifting
    witness is the proof that the underlying function respects the
    relation; the lifting layer needs it to invert the unfolding. *)
type lifted_info = {
  lifted_symbol : string;
  underlying_symbol : string;
  lifting_witness : string option;  (* "witness" field is optional in v1
                                       fixtures; we treat absence as
                                       "no witness recorded". *)
}

let parse_lifted_info (lifted : string) (meta : Yojson.Safe.t)
  : lifted_info option =
  match json_string_field meta "kind" with
  | Some "lifted_to_quotient" ->
    (match json_field meta "underlying_function" with
     | Some uf ->
       (match json_string_field uf "name" with
        | Some name ->
          let witness =
            match json_field meta "lifting_obligation" with
            | Some lo -> json_string_field lo "witness"
            | None -> None
          in
          Some {
            lifted_symbol = lifted;
            underlying_symbol = name;
            lifting_witness = witness;
          }
        | None -> None)
     | None -> None)
  | _ -> None

let collect_lifted_symbols (ir : Ir.t) : lifted_info SM.t =
  List.fold_left
    (fun acc (name, meta) ->
      match parse_lifted_info name meta with
      | Some li -> SM.add name li acc
      | None -> acc)
    SM.empty ir.definitional_metadata

(* --- inversion-data accumulators ------------------------------------- *)

type elimination_record = {
  e_var : string;
  e_from_type : string;
  e_to_type : string;
  e_elimination_principle : string;
  e_equivalence_proof : string;
}

type equality_reduction_record = {
  er_site : string;
  er_from_type : string;
  er_equality_principle : string;
  er_equivalence_proof : string;
}

type lifted_unfolding_record = {
  lu_site : string;
  lu_lifted : string;
  lu_underlying : string;
  lu_witness : string option;
}

type acc = {
  mutable eliminations : elimination_record list;
  mutable equality_reductions : equality_reduction_record list;
  mutable lifted_unfoldings : lifted_unfolding_record list;
}

let new_acc () : acc =
  { eliminations = []; equality_reductions = []; lifted_unfoldings = [] }

(* --- type rewriting on free_vars / binders --------------------------- *)

let rewrite_type (qtypes : quotient_info SM.t) (ty : Ir.type_ref)
  : Ir.type_ref =
  match SM.find_opt ty qtypes with
  | Some qi -> qi.underlying_type
  | None -> ty

(** Beta-reduce a 2-arg equivalence relation lambda applied to
    [left, right]. Falls back to [None] if the relation isn't a
    2-binder lambda; callers should leave the [Eq] untouched in that
    case. Substitution is capture-avoiding; [Substitution.subst]
    handles binder collisions when [left] / [right] contain free
    variables that shadow the relation's body. *)
let beta_reduce_relation (relation : Ir.shell_term)
    (left : Ir.shell_term) (right : Ir.shell_term)
  : Ir.shell_term option =
  match relation with
  | Lambda { binders; body } when List.length binders = 2 ->
    let env =
      List.fold_left2
        (fun acc (b : Ir.binder) v ->
          Substitution.StringMap.add b.var v acc)
        Substitution.StringMap.empty binders [ left; right ]
    in
    Some (Substitution.subst env body)
  | _ -> None

(** Bottom-up rewrite of one shell term at a single site. [acc]
    accumulates inversion data; the returned term has lifted →
    underlying substitutions and [Eq]-at-quotient → relation
    rewrites applied. *)
let rec rewrite_shell
    ~(qtypes : quotient_info SM.t)
    ~(lifted : lifted_info SM.t)
    ~(site : string)
    ~(acc : acc)
    (t : Ir.shell_term) : Ir.shell_term =
  match t with
  | Var _ | Const _ | Num_lit _ | Opaque _ -> t
  | Forall { var; ty; body } ->
    let ty' = rewrite_type qtypes ty in
    let body' = rewrite_shell ~qtypes ~lifted ~site ~acc body in
    Forall { var; ty = ty'; body = body' }
  | Exists { var; ty; body } ->
    let ty' = rewrite_type qtypes ty in
    let body' = rewrite_shell ~qtypes ~lifted ~site ~acc body in
    Exists { var; ty = ty'; body = body' }
  | Lambda { binders; body } ->
    let binders' = List.map
      (fun (b : Ir.binder) ->
        ({ var = b.var; ty = rewrite_type qtypes b.ty } : Ir.binder))
      binders
    in
    let body' = rewrite_shell ~qtypes ~lifted ~site ~acc body in
    Lambda { binders = binders'; body = body' }
  | Implies { antecedent; consequent } ->
    Implies {
      antecedent = rewrite_shell ~qtypes ~lifted ~site ~acc antecedent;
      consequent = rewrite_shell ~qtypes ~lifted ~site ~acc consequent;
    }
  | And { left; right } ->
    And {
      left = rewrite_shell ~qtypes ~lifted ~site ~acc left;
      right = rewrite_shell ~qtypes ~lifted ~site ~acc right;
    }
  | Or { left; right } ->
    Or {
      left = rewrite_shell ~qtypes ~lifted ~site ~acc left;
      right = rewrite_shell ~qtypes ~lifted ~site ~acc right;
    }
  | Not { operand } ->
    Not { operand = rewrite_shell ~qtypes ~lifted ~site ~acc operand }
  | Eq { ty; left; right } ->
    let left' = rewrite_shell ~qtypes ~lifted ~site ~acc left in
    let right' = rewrite_shell ~qtypes ~lifted ~site ~acc right in
    (match SM.find_opt ty qtypes with
     | Some qi ->
       (match beta_reduce_relation qi.equivalence_relation_lambda left' right' with
        | Some t' ->
          acc.equality_reductions <- {
            er_site = site;
            er_from_type = ty;
            er_equality_principle = qi.equality_principle;
            er_equivalence_proof = qi.equivalence_proof;
          } :: acc.equality_reductions;
          t'
        | None ->
          (* Relation isn't 2-binder; leave Eq untouched. Skip the
             reduction rather than miscompile. *)
          Eq { ty; left = left'; right = right' })
     | None ->
       Eq { ty; left = left'; right = right' })
  | App { symbol; type_args; args } ->
    let args' =
      List.map (rewrite_shell ~qtypes ~lifted ~site ~acc) args
    in
    (match SM.find_opt symbol lifted with
     | Some li ->
       acc.lifted_unfoldings <- {
         lu_site = site;
         lu_lifted = symbol;
         lu_underlying = li.underlying_symbol;
         lu_witness = li.lifting_witness;
       } :: acc.lifted_unfoldings;
       App {
         symbol = li.underlying_symbol;
         type_args;
         args = args';
       }
     | None ->
       App { symbol; type_args; args = args' })

(* --- inversion-data serialization ------------------------------------ *)

let elimination_to_json (e : elimination_record) : Yojson.Safe.t =
  `Assoc [
    "var", `String e.e_var;
    "from_type", `String e.e_from_type;
    "to_type", `String e.e_to_type;
    "elimination_principle", `String e.e_elimination_principle;
    "equivalence_proof", `String e.e_equivalence_proof;
  ]

let equality_reduction_to_json (e : equality_reduction_record)
  : Yojson.Safe.t =
  `Assoc [
    "site", `String e.er_site;
    "from_type", `String e.er_from_type;
    "equality_principle", `String e.er_equality_principle;
    "equivalence_proof", `String e.er_equivalence_proof;
  ]

let lifted_unfolding_to_json (e : lifted_unfolding_record)
  : Yojson.Safe.t =
  let fields = [
    "site", `String e.lu_site;
    "lifted", `String e.lu_lifted;
    "underlying", `String e.lu_underlying;
  ] in
  match e.lu_witness with
  | None -> `Assoc fields
  | Some w -> `Assoc (fields @ [ "witness", `String w ])

let inversion_data_to_json (acc : acc) : Yojson.Safe.t =
  `Assoc [
    "eliminations",
    `List (List.map elimination_to_json (List.rev acc.eliminations));
    "equality_reductions",
    `List (List.map equality_reduction_to_json
             (List.rev acc.equality_reductions));
    "lifted_unfoldings",
    `List (List.map lifted_unfolding_to_json
             (List.rev acc.lifted_unfoldings));
  ]

(* --- driver ---------------------------------------------------------- *)

(** Read [enable_quotient_elimination : bool] from
    [ir.user_directives.rewriter_preferences]; returns [false] when
    any field is missing. *)
let is_enabled (ir : Ir.t) : bool =
  match ir.user_directives with
  | None -> false
  | Some ud ->
    (match ud.rewriter_preferences with
     | None -> false
     | Some rp ->
       (match rp.enable_quotient_elimination with
        | Some true -> true
        | _ -> false))

type result = {
  ir : Ir.t;
  trace : Trace.entry;
}

let run (ir : Ir.t) : result =
  let before_hash = Hash.sha256_of_json (Codec.to_json ir) in
  if not (is_enabled ir) then
    {
      ir;
      trace = {
        pass = "quotient_elimination";
        version = "1.0";
        before_hash;
        after_hash = before_hash;
        configuration = None;
        outcome = Some Skipped_preconditions;
        inversion_data = None;
        diagnostics = Some "enable_quotient_elimination not set";
      };
    }
  else
    let qtypes = collect_quotient_types ir in
    let lifted = collect_lifted_symbols ir in
    let acc = new_acc () in

    (* Free vars: rewrite types and record an elimination per
       quotient-typed var. *)
    let free_vars' =
      List.map
        (fun (fv : Ir.free_var) ->
          match SM.find_opt fv.ty qtypes with
          | Some qi ->
            acc.eliminations <- {
              e_var = fv.name;
              e_from_type = fv.ty;
              e_to_type = qi.underlying_type;
              e_elimination_principle = qi.elimination_principle;
              e_equivalence_proof = qi.equivalence_proof;
            } :: acc.eliminations;
            ({ fv with ty = qi.underlying_type } : Ir.free_var)
          | None -> fv)
        ir.context.free_vars
    in

    (* Goal and hypotheses: rewrite shells, type-rewriting binders. *)
    let goal_shell' =
      rewrite_shell ~qtypes ~lifted ~site:"goal" ~acc ir.goal.shell
    in
    let new_goal : Ir.goal = { ir.goal with shell = goal_shell' } in
    let hyps' =
      List.mapi
        (fun i (h : Ir.hypothesis) ->
          let site = Printf.sprintf "hypothesis[%d]" i in
          let shell' = rewrite_shell ~qtypes ~lifted ~site ~acc h.shell in
          ({ h with shell = shell' } : Ir.hypothesis))
        ir.context.hypotheses
    in
    let new_context : Ir.context =
      { ir.context with free_vars = free_vars'; hypotheses = hyps' }
    in
    let new_ir : Ir.t = { ir with goal = new_goal; context = new_context } in

    let after_hash = Hash.sha256_of_json (Codec.to_json new_ir) in
    let any_change =
      acc.eliminations <> []
      || acc.equality_reductions <> []
      || acc.lifted_unfoldings <> []
    in
    let outcome : Trace.outcome = if any_change then Applied else No_op in
    let trace : Trace.entry = {
      pass = "quotient_elimination";
      version = "1.0";
      before_hash;
      after_hash;
      configuration = None;
      outcome = Some outcome;
      inversion_data = Some (inversion_data_to_json acc);
      diagnostics = None;
    } in
    { ir = new_ir; trace }

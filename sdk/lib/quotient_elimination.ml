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
    other parts untouched.

    Metadata sourcing. Type and definitional metadata are read
    through the typed [Type_metadata] / [Definitional_metadata]
    modules so this pass does not field-fish into the JSON
    pass-through directly. *)

(* The typed metadata modules each define their own [Map.Make(String)]
   under the name [SM]; we use them qualified ([Type_metadata.SM.find_opt]
   etc.) rather than aliasing locally because each functor application
   is a distinct generative type. *)
module Tm = Type_metadata
module Dm = Definitional_metadata

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

let rewrite_type
    (qtypes : Tm.quotient_constructor Tm.SM.t)
    (ty : Ir.type_ref) : Ir.type_ref =
  match Tm.SM.find_opt ty qtypes with
  | Some qc -> qc.underlying_type
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
    ~(qtypes : Tm.quotient_constructor Tm.SM.t)
    ~(lifted : Dm.lifted_to_quotient Dm.SM.t)
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
    (match Tm.SM.find_opt ty qtypes with
     | Some qc ->
       (match
          beta_reduce_relation qc.equivalence_relation.shell left' right'
        with
        | Some t' ->
          acc.equality_reductions <- {
            er_site = site;
            er_from_type = ty;
            er_equality_principle = qc.equality_principle;
            er_equivalence_proof = qc.equivalence_relation.equivalence_proof;
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
    (match Dm.SM.find_opt symbol lifted with
     | Some li ->
       acc.lifted_unfoldings <- {
         lu_site = site;
         lu_lifted = symbol;
         lu_underlying = li.underlying_function_name;
         lu_witness = li.lifting_witness;
       } :: acc.lifted_unfoldings;
       App {
         symbol = li.underlying_function_name;
         type_args;
         args = args';
       }
     | None ->
       App { symbol; type_args; args = args' })

(* --- inversion-data serialization ------------------------------------ *)

let elimination_to_json ~index (e : elimination_record) : Yojson.Safe.t =
  `Assoc [
    "index", `Int index;
    "var", `String e.e_var;
    "from_type", `String e.e_from_type;
    "to_type", `String e.e_to_type;
    "elimination_principle", `String e.e_elimination_principle;
    "equivalence_proof", `String e.e_equivalence_proof;
  ]

let equality_reduction_to_json ~index (e : equality_reduction_record)
  : Yojson.Safe.t =
  `Assoc [
    "index", `Int index;
    "site", `String e.er_site;
    "from_type", `String e.er_from_type;
    "equality_principle", `String e.er_equality_principle;
    "equivalence_proof", `String e.er_equivalence_proof;
  ]

let lifted_unfolding_to_json ~index (e : lifted_unfolding_record)
  : Yojson.Safe.t =
  let fields = [
    "index", `Int index;
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
    `List (List.mapi (fun i e -> elimination_to_json ~index:i e)
             (List.rev acc.eliminations));
    "equality_reductions",
    `List (List.mapi (fun i e -> equality_reduction_to_json ~index:i e)
             (List.rev acc.equality_reductions));
    "lifted_unfoldings",
    `List (List.mapi (fun i e -> lifted_unfolding_to_json ~index:i e)
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
    let qtypes = Tm.quotient_constructors ir in
    let lifted = Dm.lifted_symbols ir in
    let acc = new_acc () in

    (* Free vars: rewrite types and record an elimination per
       quotient-typed var. *)
    let free_vars' =
      List.map
        (fun (fv : Ir.free_var) ->
          match Tm.SM.find_opt fv.ty qtypes with
          | Some qc ->
            acc.eliminations <- {
              e_var = fv.name;
              e_from_type = fv.ty;
              e_to_type = qc.underlying_type;
              e_elimination_principle = qc.elimination_principle;
              e_equivalence_proof = qc.equivalence_relation.equivalence_proof;
            } :: acc.eliminations;
            ({ fv with ty = qc.underlying_type } : Ir.free_var)
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

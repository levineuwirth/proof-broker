(** Rocq-side Alethe walker. R-4: clausal layer + arithmetic +
    n-ary multi-literal resolution. *)

module Alethe = Proof_broker.Alethe

type proof = Alethe.proof

let parse_trace (s : string) : (proof, string) result =
  try Ok (Alethe.parse s)
  with
  | Alethe.Parse_error msg ->
    Error ("alethe parse: " ^ msg)
  | exn ->
    Error ("alethe parse: unexpected exception: " ^ Printexc.to_string exn)

(* =========================================================
   Reference resolution. Strict lookup from Coq's standard
   library (lib_ref): raises if any of these is missing, which
   would indicate a Coq installation too old to have num.* /
   core.* refs registered. All names match those used by
   [term_mode.ml].
   ========================================================= *)

let constr_of_ref (name : string) : EConstr.t =
  EConstr.of_constr
    (UnivGen.constr_of_monomorphic_global (Global.env ())
       (Rocqlib.lib_ref name))

(* Resolve a symbol the Rocqlib [core.*] table does NOT register,
   by trying a list of candidate fully-qualified (or short) names
   through the Coq nametab. The first that resolves wins. Raises
   [Walker_error] (NOT a bare [Not_found] anomaly) if none do, so
   the walker's own error handler catches it and the tactic fails
   cleanly into the [lia] fallback rather than crashing coqc.
   Candidate lists absorb the Coq→rocq-prover library rename
   (Coq.* / Stdlib.* / Corelib.* / bare prelude name). *)
let constr_of_first_path (candidates : string list) : EConstr.t =
  let rec try_each = function
    | [] ->
      raise (Failure
               (Printf.sprintf
                  "alethe walker: none of these paths resolved: %s"
                  (String.concat ", " candidates)))
    | path :: rest ->
      (match Nametab.locate (Libnames.qualid_of_string path) with
       | gref ->
         EConstr.of_constr
           (UnivGen.constr_of_monomorphic_global (Global.env ()) gref)
       | exception Not_found -> try_each rest)
  in
  try_each candidates

let r_xH    = lazy (constr_of_ref "num.pos.xH")
let r_xO    = lazy (constr_of_ref "num.pos.xO")
let r_xI    = lazy (constr_of_ref "num.pos.xI")
let r_Z0    = lazy (constr_of_ref "num.Z.Z0")
let r_Zpos  = lazy (constr_of_ref "num.Z.Zpos")
let r_Zneg  = lazy (constr_of_ref "num.Z.Zneg")
let r_Z     = lazy (constr_of_ref "num.Z.type")
let r_Zadd  = lazy (constr_of_ref "num.Z.add")
let r_Zsub  = lazy (constr_of_ref "num.Z.sub")
let r_Zopp  = lazy (constr_of_ref "num.Z.opp")
let r_Zmul  = lazy (constr_of_ref "num.Z.mul")
let r_Zle   = lazy (constr_of_ref "num.Z.le")
let r_Zlt   = lazy (constr_of_ref "num.Z.lt")
let r_Zge   = lazy (constr_of_ref "num.Z.ge")
let r_Zgt   = lazy (constr_of_ref "num.Z.gt")
let r_eq    = lazy (constr_of_ref "core.eq.type")
let r_not   = lazy (constr_of_ref "core.not.type")
let r_and   = lazy (constr_of_ref "core.and.type")
let r_or    = lazy (constr_of_ref "core.or.type")
let r_True  = lazy (constr_of_ref "core.True.type")
let r_False = lazy (constr_of_ref "core.False.type")
(* None of the [or] eliminator/introductions are in the [core.*]
   lib_ref table — [core.or.ind], [core.or.introl], [core.or.intror]
   are all absent (verified via CI; only the [core.or.type] inductive
   itself is registered). Same asymmetry as [False_ind] below. All
   three are prelude-exported under their short names, always in scope
   regardless of the Coq→rocq-prover rename, so route them through the
   same rename-robust candidate-path Nametab lookup. *)
let r_or_ind =
  lazy (constr_of_first_path
          [ "or_ind";
            "Corelib.Init.Logic.or_ind";
            "Stdlib.Init.Logic.or_ind";
            "Coq.Init.Logic.or_ind";
            "Init.Logic.or_ind" ])
let r_or_introl =
  lazy (constr_of_first_path
          [ "or_introl";
            "Corelib.Init.Logic.or_introl";
            "Stdlib.Init.Logic.or_introl";
            "Coq.Init.Logic.or_introl";
            "Init.Logic.or_introl" ])
let r_or_intror =
  lazy (constr_of_first_path
          [ "or_intror";
            "Corelib.Init.Logic.or_intror";
            "Stdlib.Init.Logic.or_intror";
            "Coq.Init.Logic.or_intror";
            "Init.Logic.or_intror" ])
(* Stdlib doesn't register False's eliminator in the [core.*]
   table (neither [core.False.ind] nor [core.False.elim] — both
   verified absent via CI). Asymmetric with [core.or.ind]. Fall
   back to a nametab lookup over rename-robust candidate paths;
   the short prelude-exported [False_ind] is the most likely hit. *)
let r_False_ind =
  lazy (constr_of_first_path
          [ "False_ind";
            "Corelib.Init.Logic.False_ind";
            "Stdlib.Init.Logic.False_ind";
            "Coq.Init.Logic.False_ind";
            "Init.Logic.False_ind" ])

(* [Init.Logic] eliminators / constructors / lemmas are NOT in the
   [core.*] lib_ref table in this rocq-prover build (see R-4: only
   the [Register]'d type defs resolve via [constr_of_ref]). Resolve
   them by short prelude name, falling back through the rename-robust
   qualified paths. R-5's equality cluster ([eq_refl] constructor,
   [eq_sym]/[eq_trans]/[f_equal] lemmas) all go through here. *)
let logic_ref (short : string) : EConstr.t Lazy.t =
  lazy (constr_of_first_path
          [ short;
            "Corelib.Init.Logic." ^ short;
            "Stdlib.Init.Logic." ^ short;
            "Coq.Init.Logic." ^ short;
            "Init.Logic." ^ short ])

let r_eq_refl  = logic_ref "eq_refl"
let r_eq_sym   = logic_ref "eq_sym"
let r_eq_trans = logic_ref "eq_trans"
let r_f_equal  = logic_ref "f_equal"
let r_eq_ind   = logic_ref "eq_ind"
let r_conj     = logic_ref "conj"
let r_proj1    = logic_ref "proj1"
let r_True_I   = logic_ref "I"

(* [propositional_extensionality : forall P Q:Prop, (P<->Q) -> P=Q]
   and [NNPP : forall p, ~~p -> p] — needed by [equiv_simplify]
   (R-8), which proves propositional-equality tautologies. propext
   is an axiom from [PropExtensionality]; NNPP is derived from
   [classic] (so it pulls [classic], not a new axiom). Neither is a
   [core.*] lib_ref — resolved by name, short form first. *)
let r_propext =
  lazy (constr_of_first_path
          [ "propositional_extensionality";
            "Stdlib.Logic.PropExtensionality.propositional_extensionality";
            "Coq.Logic.PropExtensionality.propositional_extensionality";
            "PropExtensionality.propositional_extensionality" ])
let r_NNPP =
  lazy (constr_of_first_path
          [ "NNPP";
            "Stdlib.Logic.Classical_Prop.NNPP";
            "Coq.Logic.Classical_Prop.NNPP";
            "Classical_Prop.NNPP" ])

(* [classic : forall P:Prop, P \/ ~P] — the excluded-middle axiom
   from [Classical_Prop]. The boolean-cleanup cluster (R-7) is the
   first walker code to leave the intuitionistic fragment: turning
   [a -> b] into [~a \/ b] is classically valid only. This widens
   the axiom footprint from empty to [{classic}] — the standard
   classical baseline, no new trust delta (mirror of the Lean
   arc's [Classical.em] step at #47). Not a [core.*] lib_ref;
   resolved by name, short form first (works once the calling .v
   has [Require Import]ed Classical_Prop). *)
let r_classic =
  lazy (constr_of_first_path
          [ "classic";
            "Stdlib.Logic.Classical_Prop.classic";
            "Coq.Logic.Classical_Prop.classic";
            "Classical_Prop.classic" ])

let force = Lazy.force

(* =========================================================
   Z literal construction. Mirrors term_mode's pattern: walk
   the Z.t value into the unary/positive constructor tree.
   ========================================================= *)

let rec positive_of_z (n : Z.t) : EConstr.t =
  if Z.equal n Z.one then force r_xH
  else
    let two = Z.of_int 2 in
    let r = Z.rem n two in
    let half = Z.div n two in
    if Z.equal r Z.zero then
      EConstr.mkApp (force r_xO, [| positive_of_z half |])
    else
      EConstr.mkApp (force r_xI, [| positive_of_z half |])

let z_lit (n : Z.t) : EConstr.t =
  match Z.sign n with
  | 0 -> force r_Z0
  | s when s > 0 -> EConstr.mkApp (force r_Zpos, [| positive_of_z n |])
  | _ -> EConstr.mkApp (force r_Zneg, [| positive_of_z (Z.abs n) |])

(** Parse an Alethe integer-shaped atom: either a plain integer
    ["-3"]/["3"] or a rational-denominator-1 form ["3/1"]/["-3/1"]
    (cvc5's alethe-2024 printer normalizes integers as rationals). *)
let parse_int_atom (s : string) : Z.t option =
  let s = String.trim s in
  if s = "" then None
  else
    let num_str =
      match String.split_on_char '/' s with
      | [ n ] -> Some n
      | [ n; "1" ] -> Some n
      | _ -> None
    in
    match num_str with
    | None -> None
    | Some n -> (try Some (Z.of_string n) with _ -> None)

(* =========================================================
   Walker types.

   Lean used a StateRefT monad for the proven-step map. Coq
   plugin convention is OCaml refs / mutable Hashtbls; the
   walker phase is purely OCaml (no Proofview), only the
   final goal-assignment crosses into Proofview.
   ========================================================= *)

exception Walker_error of string

type walker_ctx = {
  vars : EConstr.t Names.Id.Map.t;
  (* The goal env + the live evar_map ref. Carried in the context
     (rather than threaded through every translation call) so the
     [=] case can [Retyping.get_type_of] the LHS to instantiate
     polymorphic [eq] at the right element type — no longer
     hardcoded to [Z] as in R-2/R-3. The ref is the same one
     [walk_proof] mutates for la_generic evars, so deref it at use. *)
  env : Environ.env;
  sigma_ref : Evd.evar_map ref;
}

type walker_state = {
  proven : (string, EConstr.t * Alethe.Sexp.t list) Hashtbl.t;
}

let make_state () : walker_state =
  { proven = Hashtbl.create 64 }

let store_step (st : walker_state) (id : string) (e : EConstr.t)
    (clause : Alethe.Sexp.t list) : unit =
  Hashtbl.replace st.proven id (e, clause)

let lookup_step (st : walker_state) (id : string)
    : EConstr.t * Alethe.Sexp.t list =
  match Hashtbl.find_opt st.proven id with
  | Some pc -> pc
  | None ->
    raise (Walker_error
             (Printf.sprintf "step '%s' not proven yet" id))

(** Build a walker context from the goal's local context. Every
    named hypothesis / free var becomes an atom binding;
    anonymous locals are skipped (Alethe atoms always have names). *)
let make_context (env : Environ.env) (sigma_ref : Evd.evar_map ref)
    : walker_ctx =
  let named_ctx = Environ.named_context env in
  let vars =
    List.fold_left (fun acc decl ->
        let id = Context.Named.Declaration.get_id decl in
        Names.Id.Map.add id (EConstr.mkVar id) acc)
      Names.Id.Map.empty
      named_ctx
  in
  { vars; env; sigma_ref }

(* =========================================================
   Sexp -> Constr translation. LIA fragment.

   Mirrors Lean's [sexpToExpr] / [listToExpr] / [andOrChain].
   For [eq] we hardcode the type as [Z] for now — boolean
   equality (Prop = Prop) lands in R-7 alongside equiv1/equiv2.
   ========================================================= *)

let rec sexp_to_constr (ctx : walker_ctx) (s : Alethe.Sexp.t) : EConstr.t =
  match s with
  | Atom a -> atom_to_constr ctx a
  | List xs -> list_to_constr ctx xs

and atom_to_constr (ctx : walker_ctx) (s : string) : EConstr.t =
  if s = "true" then force r_True
  else if s = "false" then force r_False
  else
    match parse_int_atom s with
    | Some n -> z_lit n
    | None ->
      let id = Names.Id.of_string_soft s in
      (match Names.Id.Map.find_opt id ctx.vars with
       | Some e -> e
       | None ->
         raise (Walker_error
                  (Printf.sprintf
                     "unknown atom '%s' (not an integer literal, \
                      not in scope)" s)))

and list_to_constr (ctx : walker_ctx) (xs : Alethe.Sexp.t list) : EConstr.t =
  match xs with
  | [ Atom "+"; a; b ] ->
    EConstr.mkApp (force r_Zadd,
                   [| sexp_to_constr ctx a; sexp_to_constr ctx b |])
  | [ Atom "-"; a; b ] ->
    EConstr.mkApp (force r_Zsub,
                   [| sexp_to_constr ctx a; sexp_to_constr ctx b |])
  | [ Atom "-"; a ] ->
    EConstr.mkApp (force r_Zopp, [| sexp_to_constr ctx a |])
  | [ Atom "*"; a; b ] ->
    EConstr.mkApp (force r_Zmul,
                   [| sexp_to_constr ctx a; sexp_to_constr ctx b |])
  | [ Atom "<="; a; b ] ->
    EConstr.mkApp (force r_Zle,
                   [| sexp_to_constr ctx a; sexp_to_constr ctx b |])
  | [ Atom "<"; a; b ] ->
    EConstr.mkApp (force r_Zlt,
                   [| sexp_to_constr ctx a; sexp_to_constr ctx b |])
  | [ Atom ">="; a; b ] ->
    EConstr.mkApp (force r_Zge,
                   [| sexp_to_constr ctx a; sexp_to_constr ctx b |])
  | [ Atom ">"; a; b ] ->
    EConstr.mkApp (force r_Zgt,
                   [| sexp_to_constr ctx a; sexp_to_constr ctx b |])
  | [ Atom "="; a; b ] ->
    (* Polymorphic [eq] at the LHS's element type. R-2/R-3 hardcoded
       [Z] for the LIA scope; R-5 retypes the LHS so UF equality
       between arbitrary-typed terms ([x = y] over an opaque sort,
       [f x = f y], …) translates correctly. Z literals still retype
       to [Z], so the existing la_generic tests are unaffected.
       Boolean equality between Props arrives in R-7 (equiv1/2). *)
    let ea = sexp_to_constr ctx a in
    let eb = sexp_to_constr ctx b in
    let elem_ty = Retyping.get_type_of ctx.env !(ctx.sigma_ref) ea in
    EConstr.mkApp (force r_eq, [| elem_ty; ea; eb |])
  | [ Atom "not"; a ] ->
    EConstr.mkApp (force r_not, [| sexp_to_constr ctx a |])
  | (Atom "and") :: rest ->
    and_or_chain ctx (force r_and) (force r_True) rest
  | (Atom "or") :: rest ->
    and_or_chain ctx (force r_or) (force r_False) rest
  | (Atom "cl") :: rest ->
    (* `(cl)` is the empty clause = False. `(cl L)` is just L.
       `(cl L1 L2 ...)` is `L1 \/ L2 \/ ...` (right-associative). *)
    (match rest with
     | [] -> force r_False
     | [ lit ] -> sexp_to_constr ctx lit
     | _ -> and_or_chain ctx (force r_or) (force r_False) rest)
  | [ Atom "=>"; a; b ] ->
    let binder =
      Context.make_annot Names.Anonymous EConstr.ERelevance.relevant
    in
    EConstr.mkProd (binder, sexp_to_constr ctx a, sexp_to_constr ctx b)
  | (Atom f) :: (_ :: _ as args) ->
    (* Generic uninterpreted-function application (R-5). Reached
       only after every interpreted head above fails to match, so
       [f] is a UF symbol in scope (a goal-bound function var):
       translate the head and apply it to the translated args.
       Mirror of Lean's [sexpToExpr] applied-free-var fallback;
       lets [cong]'s [decompose_app] see a real application spine. *)
    let head = atom_to_constr ctx f in
    let arg_constrs = Array.of_list (List.map (sexp_to_constr ctx) args) in
    EConstr.mkApp (head, arg_constrs)
  | _ ->
    raise (Walker_error "unsupported Sexp shape (R-5 UF/LIA scope)")

and and_or_chain (ctx : walker_ctx) (conn : EConstr.t) (empty : EConstr.t)
    (xs : Alethe.Sexp.t list) : EConstr.t =
  match xs with
  | [] -> empty
  | [ lit ] -> sexp_to_constr ctx lit
  | lit :: rest ->
    let l_e = sexp_to_constr ctx lit in
    let rest_e = and_or_chain ctx conn empty rest in
    EConstr.mkApp (conn, [| l_e; rest_e |])

(* =========================================================
   Clause utilities. Mirror of Lean's [negateLit] / [isNotForm]
   / [clauseTypeOf].
   ========================================================= *)

let clause_type_of (ctx : walker_ctx) (lits : Alethe.Sexp.t list) : EConstr.t =
  sexp_to_constr ctx (Alethe.Sexp.List (Atom "cl" :: lits))

let negate_lit (s : Alethe.Sexp.t) : Alethe.Sexp.t =
  match s with
  | List [ Atom "not"; x ] -> x
  | other -> List [ Atom "not"; other ]

let is_not_form (s : Alethe.Sexp.t) : bool =
  match s with
  | List [ Atom "not"; _ ] -> true
  | _ -> false

(* =========================================================
   Resolution machinery (R-4).

   Mirror of Lean's [injectLit] / [casesClause] / [binaryResolve].
   The walker constructs the [Or.elim] / [or_ind] cascade
   directly: for each non-pivot literal of the premise, inject
   the literal-proof into the resolvent at the right position;
   at the pivot, case-split the other premise and close via
   [False_ind] on the complementary application.

   Binder construction uses [EConstr.Vars.subst_var] to abstract
   over named variables — the named-then-replace pattern handles
   de Bruijn shifting automatically as the recursion descends.
   ========================================================= *)

(** Abstract a [build_body] continuation over a fresh-named local
    [EConstr.mkVar id] into a [mkLambda]. The named-then-replace
    pattern is the cleanest way to build nested lambdas in plugin
    OCaml without manually tracking de Bruijn indices: build the
    body using [mkVar id], then [Vars.subst_var id] replaces the
    [mkVar] with [mkRel 1] and shifts existing Rels up. *)
let walker_var_counter = ref 0

let abstract_lam (sigma_ref : Evd.evar_map ref) (binder_name : string)
    (ty : EConstr.t) (build_body : EConstr.t -> EConstr.t) : EConstr.t =
  (* The substitution id MUST be globally unique across all live
     abstractions: nested [cases_clause] calls reuse [binder_name]
     ("hl"/"hr"), and [subst_var] replaces *every* [mkVar] of the
     given id. If two distinct binders shared an id, the inner
     [subst_var] would capture the outer binder's still-free [mkVar]
     too, collapsing two variables into one de Bruijn index (a
     positive literal proof and its negation merging — the
     "X applied to ~X" illegal-application bug). Suffix with a
     monotonic counter so our own binders never collide. *)
  incr walker_var_counter;
  let id =
    Names.Id.of_string
      (Printf.sprintf "_walker_%s_%d" binder_name !walker_var_counter)
  in
  let body_named = build_body (EConstr.mkVar id) in
  let body_closed = EConstr.Vars.subst_var !sigma_ref id body_named in
  let binder =
    Context.make_annot
      (Names.Name (Names.Id.of_string binder_name))
      EConstr.ERelevance.relevant
  in
  EConstr.mkLambda (binder, ty, body_closed)

(** Given a proof of `target[idx]`, build a proof of the whole
    clause `⋁target` via the right `Or.intro_l`/`Or.intro_r` chain. *)
let rec inject_lit (ctx : walker_ctx) (target : Alethe.Sexp.t list)
    (idx : int) (lit_proof : EConstr.t) : EConstr.t =
  match target, idx with
  | [ _ ], 0 -> lit_proof
  | (l :: rest), 0 ->
    let a_ty = sexp_to_constr ctx l in
    let b_ty = clause_type_of ctx rest in
    EConstr.mkApp (force r_or_introl, [| a_ty; b_ty; lit_proof |])
  | (l :: rest), k when k > 0 ->
    let a_ty = sexp_to_constr ctx l in
    let b_ty = clause_type_of ctx rest in
    let inner = inject_lit ctx rest (k - 1) lit_proof in
    EConstr.mkApp (force r_or_intror, [| a_ty; b_ty; inner |])
  | _ ->
    raise (Walker_error
             (Printf.sprintf
                "inject_lit: index %d out of range for a \
                 %d-literal clause" idx (List.length target)))

(** Case-analyse `clause_proof : ⋁lits`. For each disjunct, call
    `handler idx litProof` (which returns a proof of `result_ty`);
    chain the cases with `or_ind`. *)
let rec cases_clause (sigma_ref : Evd.evar_map ref) (ctx : walker_ctx)
    (clause_proof : EConstr.t) (lits : Alethe.Sexp.t list)
    (result_ty : EConstr.t)
    (handler : int -> EConstr.t -> EConstr.t) : EConstr.t =
  match lits with
  | [] -> raise (Walker_error "cases_clause on an empty clause")
  | [ _ ] -> handler 0 clause_proof
  | l :: rest ->
    let l_ty = sexp_to_constr ctx l in
    let rest_ty = clause_type_of ctx rest in
    let lam_l = abstract_lam sigma_ref "hl" l_ty (fun hl ->
      handler 0 hl)
    in
    let lam_r = abstract_lam sigma_ref "hr" rest_ty (fun hr ->
      cases_clause sigma_ref ctx hr rest result_ty
        (fun i p -> handler (i + 1) p))
    in
    EConstr.mkApp (force r_or_ind,
                   [| l_ty; rest_ty; result_ty;
                      lam_l; lam_r; clause_proof |])

(** Binary clausal resolution. Given `eA : ⋁A`, `eB : ⋁B` sharing
    a complementary literal pair, produce `(proof, R)` where
    `R = (A∖pivot) ++ (B∖pivot)` and `proof : ⋁R`. Pivot search
    is exhaustive (cvc5 doesn't emit pivot info). Throws if no
    complementary pair exists. *)
let binary_resolve (sigma_ref : Evd.evar_map ref) (ctx : walker_ctx)
    (e_a : EConstr.t) (a : Alethe.Sexp.t list)
    (e_b : EConstr.t) (b : Alethe.Sexp.t list)
    : EConstr.t * Alethe.Sexp.t list =
  let n_a = List.length a in
  let n_b = List.length b in
  let pivot =
    let rec find_i i =
      if i >= n_a then None
      else
        let lit_a = List.nth a i in
        let rec find_j j =
          if j >= n_b then find_i (i + 1)
          else if negate_lit lit_a = List.nth b j then Some (i, j)
          else find_j (j + 1)
        in find_j 0
    in find_i 0
  in
  match pivot with
  | None ->
    raise (Walker_error
             "resolution premises share no complementary literal — no pivot")
  | Some (i, j) ->
    let a_is_not = is_not_form (List.nth a i) in
    let erase_idx (xs : 'a list) (k : int) : 'a list =
      List.filteri (fun idx _ -> idx <> k) xs
    in
    let r = erase_idx a i @ erase_idx b j in
    let result_ty = clause_type_of ctx r in
    let a_len_minus_1 = n_a - 1 in
    let proof = cases_clause sigma_ref ctx e_a a result_ty (fun i' h_a' ->
      if i' = i then
        cases_clause sigma_ref ctx e_b b result_ty (fun j' h_b' ->
          if j' = j then
            (* Complementary pair: not-side applied to other → False *)
            let false_proof =
              if a_is_not
              then EConstr.mkApp (h_a', [| h_b' |])
              else EConstr.mkApp (h_b', [| h_a' |])
            in
            EConstr.mkApp (force r_False_ind,
                           [| result_ty; false_proof |])
          else
            let pos =
              a_len_minus_1 + (if j' < j then j' else j' - 1)
            in
            inject_lit ctx r pos h_b')
      else
        inject_lit ctx r (if i' < i then i' else i' - 1) h_a')
    in
    (proof, r)

(* =========================================================
   Rule elaborators (R-2 scope).

   * [elab_assume_literal]: match the assume's stated literal
     against a local hypothesis by defeq, return [mkVar] of the
     matched hypothesis.
   * [elab_false_step]: `(cl (not false))` → `fun (h : False) => h`.
   * [elab_or]: passthrough — restate the premise's proof under
     the step's flattened clause-literal list.
   * [elab_resolution]: n-ary resolution as a left-fold of
     [binary_resolve] over the premise list.
   ========================================================= *)

let elab_assume_literal (env : Environ.env)
    (sigma_ref : Evd.evar_map ref)
    (ctx : walker_ctx) (id : string) (literal : Alethe.Sexp.t)
    : EConstr.t =
  let stmt = sexp_to_constr ctx literal in
  let named_ctx = Environ.named_context env in
  let rec find = function
    | [] ->
      raise (Walker_error
               (Printf.sprintf
                  "assume '%s' states a literal with no matching \
                   local hypothesis" id))
    | decl :: rest ->
      let ty = EConstr.of_constr
                 (Context.Named.Declaration.get_type decl) in
      if Reductionops.is_conv env !sigma_ref ty stmt then
        EConstr.mkVar (Context.Named.Declaration.get_id decl)
      else
        find rest
  in
  find named_ctx

(** Arithmetic leaf rules ([la_generic] / [la_mult_neg]). The
    step's clause is a linear-arithmetic tautology — cvc5 treats
    these as proof leaves. The walker creates a fresh evar of the
    clause type; the outer [walker_test] / [tryAletheWalkerLIA]
    runs [lia] on each such evar via [tclINDEPENDENT] after the
    [Refine.refine]. Mirror of Lean's [omegaDischargeClause]. *)
let elab_la_generic (env : Environ.env)
    (sigma_ref : Evd.evar_map ref) (ctx : walker_ctx)
    (s : Alethe.step) : EConstr.t * Alethe.Sexp.t list =
  let clause_prop =
    sexp_to_constr ctx
      (Alethe.Sexp.List (Alethe.Sexp.Atom "cl" :: s.clause))
  in
  let new_sigma, evar =
    Evarutil.new_evar env !sigma_ref clause_prop
  in
  sigma_ref := new_sigma;
  (evar, s.clause)

(* =========================================================
   Equality cluster (R-5): refl / symm / trans / cong.

   Pure kernel-term reconstruction from [Init.Logic]'s
   [eq_refl] / [eq_sym] / [eq_trans] / [f_equal] — no decision
   procedure, no [Classical], so the proofs stay axiom-free
   (the [Print Assumptions] gate confirms). Mirror of Lean #45's
   [elabRefl] / [elabSymm] / [elabTrans] / [elabCong]; Coq has no
   [mkCongr] equivalent, so [cong] is open-coded as a per-argument
   [f_equal] rewrite chain (see [elab_cong]).
   ========================================================= *)

(** Decompose a proof's type, asserted to be an equality, into its
    [(element_ty, lhs, rhs)] components. [@eq A x y] decomposes to
    head [eq] + args [|A; x; y|]. *)
let eq_parts_of (ctx : walker_ctx) (e : EConstr.t)
    : EConstr.t * EConstr.t * EConstr.t =
  let sigma = !(ctx.sigma_ref) in
  let ty = Retyping.get_type_of ctx.env sigma e in
  let (_, args) = EConstr.decompose_app sigma ty in
  if Array.length args <> 3 then
    raise (Walker_error
             "equality rule: premise/term is not an equality (= a b)");
  (args.(0), args.(1), args.(2))

(** [refl]: leaf rule, no premises, clause [(cl (= t t))]. The two
    sides must be syntactically identical (the form cvc5 emits after
    preprocessing). Proof: [@eq_refl T t]. *)
let elab_refl (ctx : walker_ctx) (s : Alethe.step)
    : EConstr.t * Alethe.Sexp.t list =
  match s.clause with
  | [ List [ Atom "="; lhs; rhs ] ] ->
    if lhs <> rhs then
      raise (Walker_error
               "'refl' expects (= t t) with identical sides");
    let t = sexp_to_constr ctx lhs in
    let ty = Retyping.get_type_of ctx.env !(ctx.sigma_ref) t in
    (EConstr.mkApp (force r_eq_refl, [| ty; t |]), s.clause)
  | _ ->
    raise (Walker_error "'refl' expects clause (cl (= t t))")

(** [symm]: one premise [(= t u)], conclusion [(= u t)].
    Proof: [@eq_sym T t u premise]. *)
let elab_symm (ctx : walker_ctx) (st : walker_state) (s : Alethe.step)
    : EConstr.t * Alethe.Sexp.t list =
  match s.premises with
  | Some [ p ] ->
    let (e_p, _) = lookup_step st p in
    let (a_ty, a, b) = eq_parts_of ctx e_p in
    (EConstr.mkApp (force r_eq_sym, [| a_ty; a; b; e_p |]), s.clause)
  | _ ->
    raise (Walker_error "'symm' expects exactly one premise")

(** [trans]: premises [(= t1 t2)], [(= t2 t3)], …, conclusion
    [(= t1 tk)]. Left-fold of [@eq_trans] over the premise list;
    a single-premise [trans] passes through. *)
let elab_trans (ctx : walker_ctx) (st : walker_state) (s : Alethe.step)
    : EConstr.t * Alethe.Sexp.t list =
  match s.premises with
  | Some (p0 :: rest) ->
    let (e0, _) = lookup_step st p0 in
    let (a_ty, x0, y0) = eq_parts_of ctx e0 in
    (* acc = (proof : x0 = cur_y, cur_y). *)
    let acc = ref (e0, y0) in
    List.iter (fun pi ->
        let (e_i, _) = lookup_step st pi in
        let (_, _yi, zi) = eq_parts_of ctx e_i in
        let (acc_e, acc_y) = !acc in
        let proof =
          EConstr.mkApp (force r_eq_trans,
                         [| a_ty; x0; acc_y; zi; acc_e; e_i |])
        in
        acc := (proof, zi))
      rest;
    (fst !acc, s.clause)
  | _ ->
    raise (Walker_error "'trans' expects at least one premise")

(** [cong]: premises [(= a1 b1)], …, [(= an bn)], conclusion
    [(= (f a1 … an) (f b1 … bn))] for a common operator/UF head [f].

    Coq has no [mkCongr], so this is open-coded as a per-argument
    rewrite chain over a *fixed* operator (Alethe [cong] never
    changes the head): rewrite argument position [k] from [ak] to
    [bk] via [@f_equal arg_ty result_ty (fun x => f …prefix… x …suffix…)
    ak bk premise_k], then [eq_trans]-chain the links. The lambda
    fixes already-rewritten prefix args ([b]'s) and not-yet-rewritten
    suffix args ([a]'s), so link [k] proves
    [f b1..b(k-1) ak a(k+1)..an = f b1..b(k-1) bk a(k+1)..an]. The
    [eq_trans] endpoints are supplied in beta-reduced form so the
    chained proof's stated type stays clean; the [f_equal] links'
    own redex types are accepted by kernel conversion. *)
let elab_cong (ctx : walker_ctx) (st : walker_state) (s : Alethe.step)
    : EConstr.t * Alethe.Sexp.t list =
  match s.clause, s.premises with
  | [ List [ Atom "="; lhs_sexp; rhs_sexp ] ], Some pids ->
    let sigma = !(ctx.sigma_ref) in
    let lhs = sexp_to_constr ctx lhs_sexp in
    let rhs = sexp_to_constr ctx rhs_sexp in
    let (head_l, args_l) = EConstr.decompose_app sigma lhs in
    let (head_r, args_r) = EConstr.decompose_app sigma rhs in
    let n = Array.length args_l in
    if Array.length args_r <> n then
      raise (Walker_error
               (Printf.sprintf
                  "'cong' app-arity mismatch: LHS has %d args, RHS \
                   has %d" n (Array.length args_r)));
    if List.length pids <> n then
      raise (Walker_error
               (Printf.sprintf
                  "'cong' has %d premises but the application has %d \
                   arguments" (List.length pids) n));
    if not (Reductionops.is_conv ctx.env sigma head_l head_r) then
      raise (Walker_error
               "'cong' operator heads differ between LHS and RHS");
    if n = 0 then
      raise (Walker_error "'cong' over a nullary head has no arguments");
    let result_ty = Retyping.get_type_of ctx.env sigma lhs in
    let pids_arr = Array.of_list pids in
    (* [cur_args] mutates left-to-right: before rewriting position k
       it holds [b0..b(k-1) ak..a(n-1)]. *)
    let cur_args = Array.copy args_l in
    let acc = ref None in
    for k = 0 to n - 1 do
      let a_k = args_l.(k) in
      let b_k = args_r.(k) in
      let (e_k, _) = lookup_step st pids_arr.(k) in
      let arg_ty = Retyping.get_type_of ctx.env sigma a_k in
      (* lambda (fun x : arg_ty => f cur_args[k := x]); everything
         outside the binder lifts by 1 (no-op here — translated
         terms carry no de Bruijn Rels — but kept for correctness). *)
      let body_args =
        Array.mapi
          (fun i arg ->
            if i = k then EConstr.mkRel 1 else EConstr.Vars.lift 1 arg)
          cur_args
      in
      let lam_body =
        EConstr.mkApp (EConstr.Vars.lift 1 head_l, body_args)
      in
      let binder =
        Context.make_annot Names.Anonymous EConstr.ERelevance.relevant
      in
      let lam = EConstr.mkLambda (binder, arg_ty, lam_body) in
      let link =
        EConstr.mkApp (force r_f_equal,
                       [| arg_ty; result_ty; lam; a_k; b_k; e_k |])
      in
      let app_before = EConstr.mkApp (head_l, Array.copy cur_args) in
      cur_args.(k) <- b_k;
      let app_after = EConstr.mkApp (head_l, Array.copy cur_args) in
      (match !acc with
       | None -> acc := Some (link, app_before, app_after)
       | Some (acc_e, start, mid) ->
         let chained =
           EConstr.mkApp (force r_eq_trans,
                          [| result_ty; start; mid; app_after;
                             acc_e; link |])
         in
         acc := Some (chained, start, app_after))
    done;
    (match !acc with
     | Some (proof, _, _) -> (proof, s.clause)
     | None -> raise (Walker_error "'cong' produced no proof"))
  | _, _ ->
    raise (Walker_error
             "'cong' expects clause (cl (= LHS RHS)) with a premise list")

(* =========================================================
   Boolean-cleanup cluster (R-7): implies / equiv1 / equiv2 /
   not_and / and_neg.

   cvc5 emits these during SAT-side normalization of Tier-3
   traces — flattening implications, propositional equivalences,
   and conjunctions into clausal form for the resolution layer.
   Proofs are built by [classic] (excluded-middle) case-analysis
   on the relevant Props, then injected into the resulting clausal
   disjunction. Footprint grows to [{classic}] (the standard
   classical baseline) but no new trust axiom. Mirror of Lean
   #47's [elabImplies]/[elabEquiv1]/[elabEquiv2] + the De Morgan
   [buildNotAnd]/[buildAndNeg] recursive helpers.
   ========================================================= *)

(* Small constructors over the propositional connectives. *)
let mk_not (a : EConstr.t) : EConstr.t =
  EConstr.mkApp (force r_not, [| a |])
let mk_or (x : EConstr.t) (y : EConstr.t) : EConstr.t =
  EConstr.mkApp (force r_or, [| x; y |])
let mk_and (x : EConstr.t) (y : EConstr.t) : EConstr.t =
  EConstr.mkApp (force r_and, [| x; y |])
let mk_or_introl (a : EConstr.t) (b : EConstr.t) (pa : EConstr.t) : EConstr.t =
  EConstr.mkApp (force r_or_introl, [| a; b; pa |])
let mk_or_intror (a : EConstr.t) (b : EConstr.t) (pb : EConstr.t) : EConstr.t =
  EConstr.mkApp (force r_or_intror, [| a; b; pb |])
let mk_and_intro (a : EConstr.t) (b : EConstr.t) (pa : EConstr.t)
    (pb : EConstr.t) : EConstr.t =
  EConstr.mkApp (force r_conj, [| a; b; pa; pb |])
let mk_classic (a : EConstr.t) : EConstr.t =
  EConstr.mkApp (force r_classic, [| a |])
(* [@or_ind A B P fA fB hor] : P — eliminator order is motive args,
   then the two case functions, then the disjunction proof last
   (note: Lean's [Or.elim] takes the disjunction first). *)
let mk_or_ind (a : EConstr.t) (b : EConstr.t) (p : EConstr.t)
    (f_a : EConstr.t) (f_b : EConstr.t) (hor : EConstr.t) : EConstr.t =
  EConstr.mkApp (force r_or_ind, [| a; b; p; f_a; f_b; hor |])

(* Transport a proof of Prop [a] to Prop [b] along [h : a = b]
   (the [Eq.mp] analog), via [eq_ind] with the identity motive
   [fun X : Prop => X]. The [Prop] sort is recovered by retyping
   [a] rather than constructed directly. *)
let eq_mp (ctx : walker_ctx) (h : EConstr.t) (a : EConstr.t)
    (b : EConstr.t) (pa : EConstr.t) : EConstr.t =
  let prop = Retyping.get_type_of ctx.env !(ctx.sigma_ref) a in
  let binder =
    Context.make_annot Names.Anonymous EConstr.ERelevance.relevant
  in
  let motive = EConstr.mkLambda (binder, prop, EConstr.mkRel 1) in
  EConstr.mkApp (force r_eq_ind, [| prop; a; motive; pa; b; h |])

(* Transport backward: a proof of [b] to [a] along [h : a = b]
   ([Eq.mpr]). Same as [eq_mp] but seeded from [b] with [eq_sym h]. *)
let eq_mpr (ctx : walker_ctx) (h : EConstr.t) (a : EConstr.t)
    (b : EConstr.t) (pb : EConstr.t) : EConstr.t =
  let prop = Retyping.get_type_of ctx.env !(ctx.sigma_ref) b in
  let binder =
    Context.make_annot Names.Anonymous EConstr.ERelevance.relevant
  in
  let motive = EConstr.mkLambda (binder, prop, EConstr.mkRel 1) in
  let h_sym = EConstr.mkApp (force r_eq_sym, [| prop; a; b; h |]) in
  EConstr.mkApp (force r_eq_ind, [| prop; b; motive; pb; a; h_sym |])

(** [implies]: from premise [(=> a b)] proving [a -> b], derive
    [(cl (not a) b)] ≡ [~a \/ b]. Case-split [a] with [classic]:
    if [a], the premise gives [b] (right disjunct); if [~a], that
    is the left disjunct. *)
let elab_implies (ctx : walker_ctx) (st : walker_state)
    (s : Alethe.step) : EConstr.t * Alethe.Sexp.t list =
  match s.clause, s.premises with
  | [ List [ Atom "not"; a ]; b ], Some [ p ] ->
    let (imp_h, _) = lookup_step st p in
    let a_e = sexp_to_constr ctx a in
    let b_e = sexp_to_constr ctx b in
    let not_a = mk_not a_e in
    let result_ty = mk_or not_a b_e in
    let pos_case =
      abstract_lam ctx.sigma_ref "ha" a_e (fun ha ->
        mk_or_intror not_a b_e (EConstr.mkApp (imp_h, [| ha |])))
    in
    let neg_case =
      abstract_lam ctx.sigma_ref "hna" not_a (fun hna ->
        mk_or_introl not_a b_e hna)
    in
    (mk_or_ind a_e not_a result_ty pos_case neg_case (mk_classic a_e),
     s.clause)
  | _, _ ->
    raise (Walker_error
             "'implies' expects clause (cl (not a) b) with one \
              premise (=> a b)")

(** [equiv1]: from premise [(= a b)] (propositional equality),
    derive [(cl (not a) b)] ≡ [~a \/ b] — forward direction.
    Case-split [a]: if [a], transport via [eq_mp] to [b]; if [~a],
    left disjunct. *)
let elab_equiv1 (ctx : walker_ctx) (st : walker_state)
    (s : Alethe.step) : EConstr.t * Alethe.Sexp.t list =
  match s.clause, s.premises with
  | [ List [ Atom "not"; a ]; b ], Some [ p ] ->
    let (eq_h, _) = lookup_step st p in
    let a_e = sexp_to_constr ctx a in
    let b_e = sexp_to_constr ctx b in
    let not_a = mk_not a_e in
    let result_ty = mk_or not_a b_e in
    let pos_case =
      abstract_lam ctx.sigma_ref "ha" a_e (fun ha ->
        mk_or_intror not_a b_e (eq_mp ctx eq_h a_e b_e ha))
    in
    let neg_case =
      abstract_lam ctx.sigma_ref "hna" not_a (fun hna ->
        mk_or_introl not_a b_e hna)
    in
    (mk_or_ind a_e not_a result_ty pos_case neg_case (mk_classic a_e),
     s.clause)
  | _, _ ->
    raise (Walker_error
             "'equiv1' expects clause (cl (not a) b) with one \
              premise (= a b)")

(** [equiv2]: from premise [(= a b)], derive [(cl a (not b))] ≡
    [a \/ ~b] — backward direction. Case-split [b]: if [b],
    transport backward via [eq_mpr] to [a]; if [~b], right
    disjunct. *)
let elab_equiv2 (ctx : walker_ctx) (st : walker_state)
    (s : Alethe.step) : EConstr.t * Alethe.Sexp.t list =
  match s.clause, s.premises with
  | [ a; List [ Atom "not"; b ] ], Some [ p ] ->
    let (eq_h, _) = lookup_step st p in
    let a_e = sexp_to_constr ctx a in
    let b_e = sexp_to_constr ctx b in
    let not_b = mk_not b_e in
    let result_ty = mk_or a_e not_b in
    let pos_case =
      abstract_lam ctx.sigma_ref "hb" b_e (fun hb ->
        mk_or_introl a_e not_b (eq_mpr ctx eq_h a_e b_e hb))
    in
    let neg_case =
      abstract_lam ctx.sigma_ref "hnb" not_b (fun hnb ->
        mk_or_intror a_e not_b hnb)
    in
    (mk_or_ind b_e not_b result_ty pos_case neg_case (mk_classic b_e),
     s.clause)
  | _, _ ->
    raise (Walker_error
             "'equiv2' expects clause (cl a (not b)) with one \
              premise (= a b)")

(** De Morgan recursive helper. Given conjuncts [a1 … an] and a
    proof [h : ~(a1 /\ … /\ an)] (right-associated), build a proof
    of [~a1 \/ … \/ ~an]. Base case (singleton): [h] is already the
    desired negation. Recursive case: case-split [a1] via [classic];
    if it holds, partially apply [h] to a suspended conjunction
    (yielding [~(a2 /\ … /\ an)]) and recurse for the right
    disjunct; if [~a1], it is the left disjunct. *)
let rec build_not_and (ctx : walker_ctx) (lits : Alethe.Sexp.t list)
    (h : EConstr.t) : EConstr.t =
  match lits with
  | [] -> raise (Walker_error "'not_and' with empty conjunction")
  | [ _ ] -> h
  | a :: rest ->
    let a_e = sexp_to_constr ctx a in
    let not_a = mk_not a_e in
    let rest_and = and_or_chain ctx (force r_and) (force r_True) rest in
    let rest_negs =
      List.map (fun lit -> Alethe.Sexp.List [ Atom "not"; lit ]) rest
    in
    let rest_or_ty = clause_type_of ctx rest_negs in
    let result_ty = mk_or not_a rest_or_ty in
    let pos_case =
      abstract_lam ctx.sigma_ref "ha" a_e (fun ha ->
        (* h' : ~rest_and = fun hrest => h (conj ha hrest) *)
        let h_prime =
          abstract_lam ctx.sigma_ref "hrest" rest_and (fun hrest ->
            EConstr.mkApp (h, [| mk_and_intro a_e rest_and ha hrest |]))
        in
        mk_or_intror not_a rest_or_ty (build_not_and ctx rest h_prime))
    in
    let neg_case =
      abstract_lam ctx.sigma_ref "hna" not_a (fun hna ->
        mk_or_introl not_a rest_or_ty hna)
    in
    mk_or_ind a_e not_a result_ty pos_case neg_case (mk_classic a_e)

(** [not_and]: from premise [(not (and a1 … an))], derive
    [(cl (not a1) … (not an))] — De Morgan in clausal form. Strip
    the [(not _)] wrappers off the clause to recover the conjuncts,
    then [build_not_and] recurses on the conjunction. *)
let elab_not_and (ctx : walker_ctx) (st : walker_state)
    (s : Alethe.step) : EConstr.t * Alethe.Sexp.t list =
  match s.premises with
  | Some [ p ] ->
    let (h_p, _) = lookup_step st p in
    let inner =
      List.map
        (function
          | Alethe.Sexp.List [ Atom "not"; x ] -> x
          | _ ->
            raise (Walker_error
                     "'not_and' clause literal not in (not _) form"))
        s.clause
    in
    (build_not_and ctx inner h_p, s.clause)
  | _ ->
    raise (Walker_error "'not_and' expects exactly one premise")

(** Tautology recursive helper. Build a proof of
    [(a1 /\ … /\ an) \/ ~a1 \/ … \/ ~an] (right-associated in both
    connectives) for a non-empty literal list. Base case [n=1]:
    [classic a1]. Recursive case: case-split the inner recursive
    result ([rest_and \/ rest_negs]); if the conjunction side fires,
    case-split [a1] again to build the full conjunction (left) or
    inject the head negation (middle); if the rest_negs side fires,
    that is the tail. *)
let rec build_and_neg (ctx : walker_ctx) (lits : Alethe.Sexp.t list)
    : EConstr.t =
  match lits with
  | [] -> raise (Walker_error "'and_neg' with empty conjunction")
  | [ a ] -> mk_classic (sexp_to_constr ctx a)
  | a :: rest ->
    let a_e = sexp_to_constr ctx a in
    let not_a = mk_not a_e in
    let rest_and = and_or_chain ctx (force r_and) (force r_True) rest in
    let rest_negs =
      List.map (fun lit -> Alethe.Sexp.List [ Atom "not"; lit ]) rest
    in
    let rest_or_ty = clause_type_of ctx rest_negs in
    let rec_proof = build_and_neg ctx rest in
    let conj_e = mk_and a_e rest_and in
    let inner_or_ty = mk_or not_a rest_or_ty in
    let result_ty = mk_or conj_e inner_or_ty in
    let left_branch =
      abstract_lam ctx.sigma_ref "hRA" rest_and (fun h_ra ->
        let pos_branch =
          abstract_lam ctx.sigma_ref "ha" a_e (fun ha ->
            mk_or_introl conj_e inner_or_ty
              (mk_and_intro a_e rest_and ha h_ra))
        in
        let neg_branch =
          abstract_lam ctx.sigma_ref "hna" not_a (fun hna ->
            mk_or_intror conj_e inner_or_ty
              (mk_or_introl not_a rest_or_ty hna))
        in
        mk_or_ind a_e not_a result_ty pos_branch neg_branch
          (mk_classic a_e))
    in
    let right_branch =
      abstract_lam ctx.sigma_ref "hRO" rest_or_ty (fun h_ro ->
        mk_or_intror conj_e inner_or_ty
          (mk_or_intror not_a rest_or_ty h_ro))
    in
    mk_or_ind rest_and rest_or_ty result_ty left_branch right_branch
      rec_proof

(** [and_neg]: tautology rule, no premises. Derive the clause
    [(cl (and a1 … an) (not a1) … (not an))]. The negation literals
    are verified to match the conjuncts position-wise (a
    well-formedness check on the trace); proof built by
    [build_and_neg]. *)
let elab_and_neg (ctx : walker_ctx) (s : Alethe.step)
    : EConstr.t * Alethe.Sexp.t list =
  match s.clause with
  | List (Atom "and" :: conjs) :: neg_lits ->
    if conjs = [] then
      raise (Walker_error "'and_neg' with empty (and) head");
    if List.length conjs <> List.length neg_lits then
      raise (Walker_error
               (Printf.sprintf
                  "'and_neg' arity mismatch: %d conjuncts vs %d \
                   negation literals"
                  (List.length conjs) (List.length neg_lits)));
    List.iter2
      (fun neg_lit conj ->
        match neg_lit with
        | Alethe.Sexp.List [ Atom "not"; x ] ->
          if x <> conj then
            raise (Walker_error "'and_neg' literal mismatch with conjunct")
        | _ ->
          raise (Walker_error
                   "'and_neg' literal not in (not _) form"))
      neg_lits conjs;
    (build_and_neg ctx conjs, s.clause)
  | _ ->
    raise (Walker_error
             "'and_neg' expects clause (cl (and a1 … an) (not a1) … \
              (not an))")

(* =========================================================
   [equiv_simplify] cluster (R-8): propositional-equality
   tautology simplification.

   cvc5 emits [equiv_simplify] clauses [(cl (= lhs rhs))] where
   [lhs <-> rhs] is a propositional tautology — reflexivity,
   double negation, idempotence. Unlike the boolean-cleanup rules
   these are LEAVES: the proof is built from the clause's shape
   alone. Discharge is a structural pattern matcher (not [lia],
   which can't do propext+Iff; not [simp], which would drag opaque
   axiom growth into the footprint). Each supported pattern has a
   visible [propositional_extensionality (conj fwd bwd)] term so
   the audit trail stays transparent. Unsupported shapes throw →
   closer chain's [lia] fallback. Mirror of Lean #48.
   ========================================================= *)

(* [P -> Q] as a (non-dependent) arrow type. Translated Props carry
   no de Bruijn Rels, so no lift of [q] is needed — same as the
   [=>] translation case. *)
let mk_arrow (p : EConstr.t) (q : EConstr.t) : EConstr.t =
  let binder =
    Context.make_annot Names.Anonymous EConstr.ERelevance.relevant
  in
  EConstr.mkProd (binder, p, q)

(* [conj fwd bwd : (P->Q) /\ (Q->P)], which is convertible to
   [P <-> Q] ([iff] unfolds to that conjunction). *)
let mk_iff (p : EConstr.t) (q : EConstr.t) (fwd : EConstr.t)
    (bwd : EConstr.t) : EConstr.t =
  mk_and_intro (mk_arrow p q) (mk_arrow q p) fwd bwd

(* [@propositional_extensionality P Q iff_proof : P = Q]. *)
let mk_propext (p : EConstr.t) (q : EConstr.t) (iff_proof : EConstr.t)
    : EConstr.t =
  EConstr.mkApp (force r_propext, [| p; q; iff_proof |])

(** [(t = t) = True] via [propext (conj (fun _ => I) (fun _ => eq_refl t))].
    Constructive (both directions); footprint adds only propext. *)
let build_eq_refl_tautology (ctx : walker_ctx) (t : Alethe.Sexp.t)
    : EConstr.t =
  let t_e = sexp_to_constr ctx t in
  let t_ty = Retyping.get_type_of ctx.env !(ctx.sigma_ref) t_e in
  let eq_tt = EConstr.mkApp (force r_eq, [| t_ty; t_e; t_e |]) in
  let true_e = force r_True in
  let fwd =
    abstract_lam ctx.sigma_ref "h" eq_tt (fun _ -> force r_True_I)
  in
  let bwd =
    abstract_lam ctx.sigma_ref "h" true_e (fun _ ->
      EConstr.mkApp (force r_eq_refl, [| t_ty; t_e |]))
  in
  mk_propext eq_tt true_e (mk_iff eq_tt true_e fwd bwd)

(** [(~~a) = a] via [propext (conj (NNPP a) (fun ha hna => hna ha))].
    The forward [~~a -> a] is [NNPP] (classical); the backward
    [a -> ~~a] is constructive. Footprint: classic + propext. *)
let build_double_negation (ctx : walker_ctx) (a : Alethe.Sexp.t)
    : EConstr.t =
  let a_e = sexp_to_constr ctx a in
  let not_a = mk_not a_e in
  let nn_a = mk_not not_a in
  let fwd = EConstr.mkApp (force r_NNPP, [| a_e |]) in
  let bwd =
    abstract_lam ctx.sigma_ref "ha" a_e (fun ha ->
      abstract_lam ctx.sigma_ref "hna" not_a (fun hna ->
        EConstr.mkApp (hna, [| ha |])))
  in
  mk_propext nn_a a_e (mk_iff nn_a a_e fwd bwd)

(** [(a /\ a) = a] via [propext (conj (proj1) (fun ha => conj ha ha))].
    Constructive; footprint adds only propext. *)
let build_and_idem (ctx : walker_ctx) (a : Alethe.Sexp.t) : EConstr.t =
  let a_e = sexp_to_constr ctx a in
  let a_and_a = mk_and a_e a_e in
  let fwd = EConstr.mkApp (force r_proj1, [| a_e; a_e |]) in
  let bwd =
    abstract_lam ctx.sigma_ref "ha" a_e (fun ha ->
      mk_and_intro a_e a_e ha ha)
  in
  mk_propext a_and_a a_e (mk_iff a_and_a a_e fwd bwd)

(** [(a \/ a) = a] via [propext (conj (or_ind id id) or_introl)].
    Constructive; footprint adds only propext. *)
let build_or_idem (ctx : walker_ctx) (a : Alethe.Sexp.t) : EConstr.t =
  let a_e = sexp_to_constr ctx a in
  let a_or_a = mk_or a_e a_e in
  let fwd =
    abstract_lam ctx.sigma_ref "h" a_or_a (fun h ->
      let id_l = abstract_lam ctx.sigma_ref "hL" a_e (fun h_l -> h_l) in
      let id_r = abstract_lam ctx.sigma_ref "hR" a_e (fun h_r -> h_r) in
      mk_or_ind a_e a_e a_e id_l id_r h)
  in
  let bwd = EConstr.mkApp (force r_or_introl, [| a_e; a_e |]) in
  mk_propext a_or_a a_e (mk_iff a_or_a a_e fwd bwd)

(** [equiv_simplify]: structural pattern matcher on the
    [(= lhs rhs)] clause. Each recognized pattern delegates to a
    per-pattern builder; unrecognized shapes throw with the
    supported-pattern list (the [lia] fallback then re-runs). *)
let elab_equiv_simplify (ctx : walker_ctx) (s : Alethe.step)
    : EConstr.t * Alethe.Sexp.t list =
  match s.clause with
  | [ List [ Atom "="; lhs; rhs ] ] ->
    let proof =
      match lhs, rhs with
      | List [ Atom "="; t1; t2 ], Atom "true" when t1 = t2 ->
        build_eq_refl_tautology ctx t1
      | List [ Atom "not"; List [ Atom "not"; a ] ], a' when a = a' ->
        build_double_negation ctx a
      | List [ Atom "and"; a1; a2 ], a' when a1 = a2 && a1 = a' ->
        build_and_idem ctx a1
      | List [ Atom "or"; a1; a2 ], a' when a1 = a2 && a1 = a' ->
        build_or_idem ctx a1
      | _, _ ->
        raise (Walker_error
                 "'equiv_simplify' pattern not recognized. Supported: \
                  (= (= t t) true) / (= (not (not a)) a) / \
                  (= (and a a) a) / (= (or a a) a)")
    in
    (proof, s.clause)
  | _ ->
    raise (Walker_error
             "'equiv_simplify' expects clause (cl (= lhs rhs))")

(* =========================================================
   [equiv_pos1] / [equiv_pos2] (R-10): 3-literal Boolean
   tautologies, no premises. The two positive-polarity halves of
   propositional-equivalence reasoning cvc5 emits alongside the
   R-7 boolean cluster (deferred from R-7 as they are nested
   case-splits). Built by nested [classic] case analysis with the
   R-7/R-8 [eq_mp]/[eq_mpr] transports; footprint [{classic}]
   (the transports go through axiom-free [eq_ind]). Mirror of
   Lean #50's [elabEquivPos1]/[elabEquivPos2].
   ========================================================= *)

(** [equiv_pos1]: clause [(cl (not (= a b)) a (not b))] ≡
    [~(a=b) \/ a \/ ~b]. Nested [classic]: case [a=b]; if not, left
    disjunct. If [a=b], case [b]; if [b], transport to [a] via
    [eq_mpr] for the middle disjunct; if [~b], the right disjunct. *)
let elab_equiv_pos1 (ctx : walker_ctx) (s : Alethe.step)
    : EConstr.t * Alethe.Sexp.t list =
  match s.clause with
  | [ List [ Atom "not"; List [ Atom "="; a; b ] ]; a';
      List [ Atom "not"; b' ] ] ->
    if a <> a' || b <> b' then
      raise (Walker_error "'equiv_pos1' argument mismatch in clause");
    let a_e = sexp_to_constr ctx a in
    let b_e = sexp_to_constr ctx b in
    let eq_ab = sexp_to_constr ctx (List [ Atom "="; a; b ]) in
    let not_eq = mk_not eq_ab in
    let not_b = mk_not b_e in
    let inner_ty = mk_or a_e not_b in
    let result_ty = mk_or not_eq inner_ty in
    let pos_outer =
      abstract_lam ctx.sigma_ref "eqH" eq_ab (fun eq_h ->
        let pos_inner =
          abstract_lam ctx.sigma_ref "hb" b_e (fun hb ->
            let a_proof = eq_mpr ctx eq_h a_e b_e hb in
            mk_or_intror not_eq inner_ty
              (mk_or_introl a_e not_b a_proof))
        in
        let neg_inner =
          abstract_lam ctx.sigma_ref "hnb" not_b (fun hnb ->
            mk_or_intror not_eq inner_ty
              (mk_or_intror a_e not_b hnb))
        in
        mk_or_ind b_e not_b result_ty pos_inner neg_inner
          (mk_classic b_e))
    in
    let neg_outer =
      abstract_lam ctx.sigma_ref "hne" not_eq (fun hne ->
        mk_or_introl not_eq inner_ty hne)
    in
    (mk_or_ind eq_ab not_eq result_ty pos_outer neg_outer
       (mk_classic eq_ab),
     s.clause)
  | _ ->
    raise (Walker_error
             "'equiv_pos1' expects clause (cl (not (= a b)) a (not b))")

(** [equiv_pos2]: clause [(cl (not (= a b)) (not a) b)] ≡
    [~(a=b) \/ ~a \/ b]. Mirror of [equiv_pos1]: if [a=b] and [a]
    holds, transport to [b] via [eq_mp] for the right disjunct; if
    [~a], the middle disjunct. *)
let elab_equiv_pos2 (ctx : walker_ctx) (s : Alethe.step)
    : EConstr.t * Alethe.Sexp.t list =
  match s.clause with
  | [ List [ Atom "not"; List [ Atom "="; a; b ] ];
      List [ Atom "not"; a' ]; b' ] ->
    if a <> a' || b <> b' then
      raise (Walker_error "'equiv_pos2' argument mismatch in clause");
    let a_e = sexp_to_constr ctx a in
    let b_e = sexp_to_constr ctx b in
    let eq_ab = sexp_to_constr ctx (List [ Atom "="; a; b ]) in
    let not_eq = mk_not eq_ab in
    let not_a = mk_not a_e in
    let inner_ty = mk_or not_a b_e in
    let result_ty = mk_or not_eq inner_ty in
    let pos_outer =
      abstract_lam ctx.sigma_ref "eqH" eq_ab (fun eq_h ->
        let pos_inner =
          abstract_lam ctx.sigma_ref "ha" a_e (fun ha ->
            let b_proof = eq_mp ctx eq_h a_e b_e ha in
            mk_or_intror not_eq inner_ty
              (mk_or_intror not_a b_e b_proof))
        in
        let neg_inner =
          abstract_lam ctx.sigma_ref "hna" not_a (fun hna ->
            mk_or_intror not_eq inner_ty
              (mk_or_introl not_a b_e hna))
        in
        mk_or_ind a_e not_a result_ty pos_inner neg_inner
          (mk_classic a_e))
    in
    let neg_outer =
      abstract_lam ctx.sigma_ref "hne" not_eq (fun hne ->
        mk_or_introl not_eq inner_ty hne)
    in
    (mk_or_ind eq_ab not_eq result_ty pos_outer neg_outer
       (mk_classic eq_ab),
     s.clause)
  | _ ->
    raise (Walker_error
             "'equiv_pos2' expects clause (cl (not (= a b)) (not a) b)")

let elab_false_step (_ctx : walker_ctx) (s : Alethe.step)
    : EConstr.t * Alethe.Sexp.t list =
  match s.clause with
  | [ List [ Atom "not"; Atom "false" ] ] ->
    (* Build [fun (h : False) => h] : False -> False. *)
    let binder =
      Context.make_annot
        (Names.Name (Names.Id.of_string "h"))
        EConstr.ERelevance.relevant
    in
    let proof =
      EConstr.mkLambda (binder, force r_False, EConstr.mkRel 1)
    in
    (proof, s.clause)
  | _ ->
    raise (Walker_error
             "'false' rule expects clause (cl (not false))")

let elab_or (st : walker_state) (s : Alethe.step)
    : EConstr.t * Alethe.Sexp.t list =
  match s.premises with
  | Some [ p ] ->
    let (proof, _) = lookup_step st p in
    (proof, s.clause)
  | _ ->
    raise (Walker_error
             "'or' rule expects exactly one premise")

(** [resolution]: n-ary clausal resolution. Alethe's [resolution]
    is a left-fold of binary resolutions over the premise list;
    each binary step cancels one complementary literal pair
    ([binary_resolve] finds the pivot — cvc5 does not list pivots
    explicitly). The result `(proof, clause)` carries the
    computed resolvent; for a closing step the resolvent is the
    empty clause and the proof has type [False]. *)
let elab_resolution (sigma_ref : Evd.evar_map ref)
    (ctx : walker_ctx) (st : walker_state)
    (s : Alethe.step) : EConstr.t * Alethe.Sexp.t list =
  match s.premises with
  | Some (p0 :: rest) ->
    let (e0, c0) = lookup_step st p0 in
    let acc = ref (e0, c0) in
    List.iter (fun pi ->
        let (ei, ci) = lookup_step st pi in
        let (cur_e, cur_c) = !acc in
        acc := binary_resolve sigma_ref ctx cur_e cur_c ei ci)
      rest;
    !acc
  | _ ->
    raise (Walker_error
             "'resolution' needs at least one premise")

(* =========================================================
   Dispatch + walk.
   ========================================================= *)

let elab_step (env : Environ.env) (sigma_ref : Evd.evar_map ref)
    (ctx : walker_ctx) (st : walker_state) (s : Alethe.step) : unit =
  let (proof, clause) =
    match s.rule with
    | "or" -> elab_or st s
    | "resolution" -> elab_resolution sigma_ref ctx st s
    | "false" -> elab_false_step ctx s
    | "la_generic" -> elab_la_generic env sigma_ref ctx s
    | "la_mult_neg" -> elab_la_generic env sigma_ref ctx s
    | "refl" -> elab_refl ctx s
    | "symm" -> elab_symm ctx st s
    | "trans" -> elab_trans ctx st s
    | "cong" -> elab_cong ctx st s
    (* Trust-tagged leaves (R-6). cvc5 emits [hole]
       (TRUST_THEORY_REWRITE-annotated) and [rare_rewrite] (RARE
       rewrite system) as "admit the conclusion" steps. Audit H1
       forbids trusting either tag: re-derive the clause from
       scratch via the same [lia]-discharge used for LIA leaves, so
       the proof goes through the kernel independently of cvc5's
       annotation. Clauses outside [lia]'s scope surface as the
       evar's [lia] subgoal failing → tactic failure → the closer
       chain's [lia] fallback re-runs. Never admit on tag. *)
    | "hole" -> elab_la_generic env sigma_ref ctx s
    | "rare_rewrite" -> elab_la_generic env sigma_ref ctx s
    (* Boolean-cleanup cluster (R-7) — classical (em) case-splits. *)
    | "implies" -> elab_implies ctx st s
    | "equiv1" -> elab_equiv1 ctx st s
    | "equiv2" -> elab_equiv2 ctx st s
    | "not_and" -> elab_not_and ctx st s
    | "and_neg" -> elab_and_neg ctx s
    (* Propositional-equality tautology simplification (R-8). *)
    | "equiv_simplify" -> elab_equiv_simplify ctx s
    (* 3-literal equivalence tautologies (R-10). *)
    | "equiv_pos1" -> elab_equiv_pos1 ctx s
    | "equiv_pos2" -> elab_equiv_pos2 ctx s
    | other ->
      raise (Walker_error
               (Printf.sprintf
                  "rule '%s' not yet supported (R-10 scope: \
                   assume / or / resolution (n-ary) / false / \
                   la_generic / la_mult_neg / refl / symm / trans / \
                   cong / hole / rare_rewrite / implies / equiv1 / \
                   equiv2 / not_and / and_neg / equiv_simplify / \
                   equiv_pos1 / equiv_pos2)"
                  other))
  in
  store_step st s.id proof clause

let walk_proof (env : Environ.env) (sigma_ref : Evd.evar_map ref)
    (ctx : walker_ctx) (p : proof) : EConstr.t =
  let st = make_state () in
  (* Phase 1: seed assumes against local hypotheses. *)
  List.iter (fun (id, lit) ->
      let e = elab_assume_literal env sigma_ref ctx id lit in
      store_step st id e [ lit ])
    p.assumes;
  (* Phase 2: walk steps in order. *)
  List.iter (elab_step env sigma_ref ctx st) p.steps;
  match List.rev p.steps with
  | [] ->
    raise (Walker_error
             "proof has no steps; a well-formed alethe-2024 \
              trace ends in an empty-clause resolution step")
  | last :: _ ->
    let (e, _) = lookup_step st last.id in
    e

(* =========================================================
   Tactic entry point.

   The walker generates a proof term whose leaves are either
   concrete (clausal rules) or evars (la_generic / la_mult_neg).
   After [Refine.refine] asserts the term against the goal mvar,
   any remaining subgoals are exactly those la_generic evars —
   discharged by [tclINDEPENDENT invoke_lia]. Mirror of Lean's
   [omegaDischargeClause]'s out-of-MetaM equivalent.
   ========================================================= *)

(** Invoke a registered Stdlib tactic by name — used to call
    [lia] on the subgoals [Refine.refine] produces from the
    walker's la_generic evars. Duplicates the pattern from
    [Pb_rocq_main.invoke_named_tactic] (avoiding a cross-module
    dependency at this stage of the arc). *)
let invoke_named_tactic (name : string) : unit Proofview.tactic =
  Proofview.Goal.enter (fun _ ->
    let raw = Procq.parse_string Ltac_plugin.Pltac.tactic name in
    let glob =
      Ltac_plugin.Tacintern.intern_pure_tactic
        (Ltac_plugin.Tacintern.make_empty_glob_sign ~strict:false) raw
    in
    Ltac_plugin.Tacinterp.eval_tactic glob)

(** Discharge a leaf evar (la_generic / la_mult_neg / hole /
    rare_rewrite). Plain [lia] closes the arithmetic-tautology
    leaves (disjunctions, comparisons — the R-3/R-6 shapes). Real
    cvc5 [hole] clauses, though, are often *propositional
    equalities* between arithmetic facts (e.g. [(n<=10) = ~(n>=11)],
    the double-negation [~~(n>=11) = (n>=11)], or [(n+m=10) =
    (n=10-m)]) — and Coq's [lia] does not prove [@eq Prop P Q]. So
    fall back to [propositional_extensionality], which reduces
    [P = Q] to [P <-> Q]; [lia] then proves the iff (it handles the
    full propositional combination of linear-arithmetic atoms).
    The propext branch is taken only when the leaf is genuinely a
    Prop-equality, so the arithmetic-only leaves stay axiom-free;
    the snapshot trace's holes pull [propositional_extensionality].
    A non-tautology leaf satisfies neither branch → the discharge
    fails → walker fails → fallback fires (audit H1). *)
let discharge_leaf () : unit Proofview.tactic =
  invoke_named_tactic
    "first [ lia | apply propositional_extensionality; lia ]"

(** Reduce a non-[False] goal [G] to [False] by classical
    contradiction, exposing [~G] as a fresh hypothesis the trace's
    [(assume _ (not G))] step matches against. Mirror of Lean's
    [MVarId.falseOrByContra]. Term-level [NNPP] would need an
    evar-under-binder; instead invoke the Ltac [apply NNPP; intro]
    (consistent with the plugin's tactic-invocation convention).
    [NNPP] derives from [classic], so this widens the footprint to
    [{classic}] — the same baseline the boolean cluster already
    needs. If [NNPP] is out of scope (Classical_Prop not loaded),
    the [apply] fails and the caller's [tclORELSE] falls to [lia]. *)
let by_contradiction () : unit Proofview.tactic =
  invoke_named_tactic "apply NNPP; intro"

(** Is this a refutation trace (final step concludes the empty
    clause [(cl)])? cvc5's actual output shape; a non-empty final
    clause is a direct per-rule unit trace. *)
let is_refutation_trace (p : proof) : bool =
  match List.rev p.steps with
  | last :: _ -> last.clause = []
  | [] -> false

(** Walk the proof into a term and assign it to the CURRENT goal:
    build the kernel term, check it is convertible with the goal
    type, [Refine.refine] it, and discharge any la_generic evars
    with [lia]. A [Walker_error] (raised by the pure walk) is caught
    inside the [Goal.enter] closure and converted to a [tclZEROMSG]
    — a tactic-level failure the caller's [tclORELSE] can catch
    (an OCaml exception escaping the closure could not be). *)
let walk_against_current_goal (p : proof) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let env = Proofview.Goal.env gl in
    let goal_ty = Proofview.Goal.concl gl in
    try
      let sigma_ref = ref (Proofview.Goal.sigma gl) in
      let ctx = make_context env sigma_ref in
      let proof_term = walk_proof env sigma_ref ctx p in
      let final_sigma = !sigma_ref in
      let term_ty = Retyping.get_type_of env final_sigma proof_term in
      if Reductionops.is_conv env final_sigma term_ty goal_ty then
        Proofview.tclTHEN
          (Refine.refine ~typecheck:true (fun _ ->
             (final_sigma, proof_term)))
          (Proofview.tclINDEPENDENT (discharge_leaf ()))
      else
        Tacticals.tclZEROMSG
          (Pp.str
             "alethe walker: walker produced a proof of the wrong \
              type for the current goal")
    with Walker_error msg ->
      Tacticals.tclZEROMSG (Pp.str ("alethe walker: " ^ msg)))

(** Walk a parsed proof into the goal. Shared between the
    production [Pb_rocq_main.try_alethe_walker_lia] path and the
    test-only [walker_test] tactic so both close goals through the
    same logic. Two trace shapes:

    * Refutation trace against a non-[False] goal — first
      [by_contradiction] to expose [~goal] and reduce to [False],
      then walk the [False] goal (the trace's [(assume _ (not goal))]
      matches the exposed hypothesis).
    * Otherwise (direct per-rule trace, or refutation against a
      [False] goal) — walk against the goal directly.

    Every failure mode is a tactic-level failure ([tclZEROMSG] /
    [by_contradiction]'s [apply] failing), so a caller's [tclORELSE]
    fallback fires cleanly. The walk is pure (no mvar assignment)
    until the final [Refine.refine], so a mid-walk failure never
    leaves a partial assignment. *)
let walk_proof_into_goal (p : proof) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let goal_ty = Proofview.Goal.concl gl in
    let goal_is_false =
      Reductionops.is_conv env sigma goal_ty (force r_False)
    in
    if is_refutation_trace p && not goal_is_false then
      Proofview.tclTHEN (by_contradiction ())
        (walk_against_current_goal p)
    else
      walk_against_current_goal p)

let walker_test (trace_str : string) : unit Proofview.tactic =
  match parse_trace trace_str with
  | Error msg ->
    Tacticals.tclZEROMSG (Pp.str ("alethe_walker_test: " ^ msg))
  | Ok p -> walk_proof_into_goal p

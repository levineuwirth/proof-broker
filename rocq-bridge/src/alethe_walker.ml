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
let r_or_introl = lazy (constr_of_ref "core.or.introl")
let r_or_intror = lazy (constr_of_ref "core.or.intror")
let r_or_ind    = lazy (constr_of_ref "core.or.ind")
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
let make_context (env : Environ.env) : walker_ctx =
  let named_ctx = Environ.named_context env in
  let vars =
    List.fold_left (fun acc decl ->
        let id = Context.Named.Declaration.get_id decl in
        Names.Id.Map.add id (EConstr.mkVar id) acc)
      Names.Id.Map.empty
      named_ctx
  in
  { vars }

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
    (* Polymorphic [eq] — hardcoded to Z for R-2's LIA scope.
       Boolean equality between Props arrives in R-7 (equiv1/2). *)
    EConstr.mkApp (force r_eq,
                   [| force r_Z;
                      sexp_to_constr ctx a;
                      sexp_to_constr ctx b |])
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
  | _ ->
    raise (Walker_error "unsupported Sexp shape (R-2 LIA scope)")

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
let abstract_lam (sigma_ref : Evd.evar_map ref) (binder_name : string)
    (ty : EConstr.t) (build_body : EConstr.t -> EConstr.t) : EConstr.t =
  let id = Names.Id.of_string ("_walker_" ^ binder_name) in
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
    | other ->
      raise (Walker_error
               (Printf.sprintf
                  "rule '%s' not yet supported (R-4 scope: \
                   assume / or / resolution (n-ary) / false / \
                   la_generic / la_mult_neg; subsequent PRs add \
                   equality / trust-tagged leaves / boolean \
                   cleanup / equiv_simplify / equiv_pos)"
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

let invoke_lia () : unit Proofview.tactic =
  invoke_named_tactic "lia"

let walker_test (trace_str : string) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let env = Proofview.Goal.env gl in
    let goal_ty = Proofview.Goal.concl gl in
    match parse_trace trace_str with
    | Error msg ->
      Tacticals.tclZEROMSG
        (Pp.str ("alethe_walker_test: " ^ msg))
    | Ok p ->
      (try
         let sigma_ref = ref (Proofview.Goal.sigma gl) in
         let ctx = make_context env in
         let proof_term = walk_proof env sigma_ref ctx p in
         let final_sigma = !sigma_ref in
         let term_ty =
           Retyping.get_type_of env final_sigma proof_term
         in
         if Reductionops.is_conv env final_sigma term_ty goal_ty then
           let refine_tac =
             Refine.refine ~typecheck:true (fun _ ->
               (final_sigma, proof_term))
           in
           Proofview.tclTHEN refine_tac
             (Proofview.tclINDEPENDENT (invoke_lia ()))
         else
           Tacticals.tclZEROMSG
             (Pp.str
                "alethe_walker_test: walker produced a proof of \
                 the wrong type for the current goal")
       with
       | Walker_error msg ->
         Tacticals.tclZEROMSG
           (Pp.str ("alethe_walker_test: " ^ msg))))

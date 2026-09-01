module Ir = Proof_broker.Ir
module Smtlib = Proof_broker.Smtlib

(* --- lib_ref-resolved Constr atoms ---------------------------------- *)

let constr_of_ref s =
  EConstr.of_constr
    (UnivGen.constr_of_monomorphic_global (Global.env ()) (Rocqlib.lib_ref s))

(* Some refs (notably the [reals.R.*] family) only exist when the
   user has imported the corresponding library. Wrapping in [option]
   so the reifier degrades to "no match" instead of crashing on a
   ref it tried to compare against speculatively — a LIA-only goal
   never needs [reals.R.type] but the head-match chain still touches
   it. *)
let safe_constr_of_ref s : EConstr.t option =
  try Some (constr_of_ref s) with _ -> None

(* Compare a term against an optional registered Constr; missing ref
   means "no match", same as a structural mismatch. *)
let eq_ref sigma a (lz : EConstr.t option Lazy.t) : bool =
  match Lazy.force lz with
  | Some c -> EConstr.eq_constr_nounivs sigma a c
  | None -> false

(* Z and positive constructors. *)
let r_Z0   = lazy (safe_constr_of_ref "num.Z.Z0")
let r_Zpos = lazy (safe_constr_of_ref "num.Z.Zpos")
let r_Zneg = lazy (safe_constr_of_ref "num.Z.Zneg")
let r_xH   = lazy (safe_constr_of_ref "num.pos.xH")
let r_xO   = lazy (safe_constr_of_ref "num.pos.xO")
let r_xI   = lazy (safe_constr_of_ref "num.pos.xI")
let r_Z    = lazy (safe_constr_of_ref "num.Z.type")

(* Z arithmetic + ordering. *)
let r_Zadd = lazy (safe_constr_of_ref "num.Z.add")
let r_Zsub = lazy (safe_constr_of_ref "num.Z.sub")
let r_Zmul = lazy (safe_constr_of_ref "num.Z.mul")
let r_Zopp = lazy (safe_constr_of_ref "num.Z.opp")
let r_Zle  = lazy (safe_constr_of_ref "num.Z.le")
let r_Zlt  = lazy (safe_constr_of_ref "num.Z.lt")
let r_Zge  = lazy (safe_constr_of_ref "num.Z.ge")
let r_Zgt  = lazy (safe_constr_of_ref "num.Z.gt")

(* R type + arithmetic + ordering + Z->R injection. R-typed numeric
   literals like [5%R] desugar to [IZR <Z literal>] in Rocq, so the
   literal walker just unwraps [IZR] and runs the existing Z flatten.
   Decimal-typed literals (e.g. [3.5%R], which use [Q2R] / [IPR]
   chains) are out of scope for this iteration; matches Lean's LRA
   reifier in [ProofBrokerMathlib.Tactic.lean] which also focuses on
   integer-flavored Real literals first. *)
let r_R       = lazy (safe_constr_of_ref "reals.R.type")
let r_Rplus   = lazy (safe_constr_of_ref "reals.R.Rplus")
let r_Rminus  = lazy (safe_constr_of_ref "reals.R.Rminus")
let r_Rmult   = lazy (safe_constr_of_ref "reals.R.Rmult")
let r_Ropp    = lazy (safe_constr_of_ref "reals.R.Ropp")
let r_Rle     = lazy (safe_constr_of_ref "reals.R.Rle")
let r_Rlt     = lazy (safe_constr_of_ref "reals.R.Rlt")
let r_Rge     = lazy (safe_constr_of_ref "reals.R.Rge")
let r_Rgt     = lazy (safe_constr_of_ref "reals.R.Rgt")
let r_IZR     = lazy (safe_constr_of_ref "reals.R.IZR")

(* Logic. *)
let r_eq    = lazy (safe_constr_of_ref "core.eq.type")
let r_and   = lazy (safe_constr_of_ref "core.and.type")
let r_or    = lazy (safe_constr_of_ref "core.or.type")
let r_ex    = lazy (safe_constr_of_ref "core.ex.type")
let r_not   = lazy (safe_constr_of_ref "core.not.type")
let r_True  = lazy (safe_constr_of_ref "core.True.type")
let r_False = lazy (safe_constr_of_ref "core.False.type")

let eq sigma a b = EConstr.eq_constr_nounivs sigma a b

exception Reify_error of string

let reify_error fmt =
  Printf.ksprintf (fun s -> raise (Reify_error s)) fmt

let pp_econstr env sigma t =
  Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t)

(* --- positive / Z literals ----------------------------------------- *)

let rec positive_to_z env sigma p : Z.t =
  let p = Reductionops.whd_all env sigma p in
  if eq_ref sigma p r_xH then Z.one
  else
    match EConstr.kind sigma p with
    | App (head, [| inner |]) when eq_ref sigma head r_xO ->
      Z.shift_left (positive_to_z env sigma inner) 1
    | App (head, [| inner |]) when eq_ref sigma head r_xI ->
      Z.add Z.one (Z.shift_left (positive_to_z env sigma inner) 1)
    | _ ->
      reify_error "expected positive (xH/xO/xI), got: %s"
        (pp_econstr env sigma p)

let reify_z_literal _env sigma t : string option =
  (* No reduction: Z0/Zpos/Zneg are constructors and the standard
     scope notations [5%Z] elaborate to [Zpos (xI (xO xH))]
     directly. Calling [whd_all] would unfold [IZR] when called from
     the R literal walker, which we explicitly do not want. *)
  if eq_ref sigma t r_Z0 then Some "0"
  else
    match EConstr.kind sigma t with
    | App (head, [| p |]) when eq_ref sigma head r_Zpos ->
      Some (Z.to_string (positive_to_z _env sigma p))
    | App (head, [| p |]) when eq_ref sigma head r_Zneg ->
      Some ("-" ^ Z.to_string (positive_to_z _env sigma p))
    | _ -> None

(* Walk a Real-typed integer literal: [IZR z] where [z] is a closed
   Z literal. Returns the Z-decimal string (the broker's Num_lit
   value field is type-tag-agnostic; only the [ty] differs from the
   LIA case). Decimal Real literals (e.g. [3.5%R], which use [Q2R] /
   [IPR] chains) are out of scope here — same coverage as Lean's
   ProofBrokerMathlib focuses on integer-flavored Real literals. *)
let reify_r_literal env sigma t : string option =
  match EConstr.kind sigma t with
  | App (head, [| z |]) when eq_ref sigma head r_IZR ->
    reify_z_literal env sigma z
  | _ -> None

(* --- type reification (UF support) --------------------------------- *)

(* Structural arrow check: a [Prod (_, _, body)] is an arrow iff the
   bound variable does NOT occur in [body] (true Pi types are
   dependent and out of scope). *)
let is_arrow_type sigma ty =
  match EConstr.kind sigma ty with
  | Prod (_, _, body) -> EConstr.Vars.noccurn sigma 1 body
  | _ -> false

(* Decode a type [Constr] as an IR [type_ref] string. Mirrors
   [ProofBroker.Reify.reifyType] in lean-bridge: handles [Z]/[R]/Prop
   plus arrow chains [T1 → T2 → ... → R] (encoded as
   [T1->T2->...->R]). The arrow encoding is the SDK's UF convention
   — [Smtlib.parse_arrow_type] + [emit_decls] turn this into
   [(declare-fun f (T1 T2) R)] SMT-LIB output. *)
let rec reify_type env sigma ty : string option =
  if eq_ref sigma ty r_Z then Some "Int"
  else if eq_ref sigma ty r_R then Some "Real"
  else if Termops.is_Prop sigma ty then Some "Prop"
  else
    match EConstr.kind sigma ty with
    | Prod (_, dom, body) when EConstr.Vars.noccurn sigma 1 body ->
      let dom_is_arrow = is_arrow_type sigma dom in
      (match reify_type env sigma dom, reify_type env sigma body with
       | Some d, Some r ->
         (* Parenthesize an arrow-shaped domain so the IR string
            keeps the grouping: [(Z -> Z) -> Prop] must serialize as
            ["(Int->Int)->Prop"], not ["Int->Int->Prop"] (which the
            SDK's [parse_arrow_type] would read as a 2-arg Int->Prop
            predicate, dropping the function-of-Int-to-Int argument
            structure the HOL fragment depends on). *)
         let d_paren = if dom_is_arrow then "(" ^ d ^ ")" else d in
         Some (d_paren ^ "->" ^ r)
       | _ -> None)
    | _ -> None

(* --- term reification ---------------------------------------------- *)

let bin sym a b : Ir.shell_term =
  App { symbol = sym; type_args = []; args = [ a; b ] }

let un sym a : Ir.shell_term =
  App { symbol = sym; type_args = []; args = [ a ] }

let rec reify_term env sigma t : Ir.shell_term =
  (* No top-level reduction: [whd_all] unfolds [Z.ge] / [Z.le] into
     their compare-based definitions (e.g. [x >= 5] becomes
     [(x ?= 5) = Lt -> False]), which destroys the head shape we
     want to match. The literal walker calls its own reductionop. *)
  (* Closed Z literal first — must run before app-shape matching, since
     [Zpos (xO xH)] is structurally an application. R literals
     ([IZR z]) likewise must precede the generic [App] branch so the
     reifier emits a [Num_lit] with the Real type tag rather than
     descending into an [IZR (...)] application. *)
  (match reify_z_literal env sigma t with
   | Some v -> Ir.Num_lit { value = v; ty = "Int" }
   | None ->
     match reify_r_literal env sigma t with
     | Some v -> Ir.Num_lit { value = v; ty = "Real" }
     | None ->
       if EConstr.isVar sigma t then
         Ir.Var { name = Names.Id.to_string (EConstr.destVar sigma t) }
       else if eq_ref sigma t r_True then Ir.Const { name = "True" }
       else if eq_ref sigma t r_False then Ir.Const { name = "False" }
       else
         match EConstr.kind sigma t with
         | App (head, args) -> reify_app env sigma head args t
         | Prod (binder, dom, body) ->
           (* [Prod] at term level encodes either propositional
              implication (non-dependent body) or a [forall]
              (body depends on the bound var — the HOL/FOL
              fragment). Distinguish by whether [body] references
              the bound variable. *)
           if EConstr.Vars.noccurn sigma 1 body then
             (* Non-dependent: [dom -> body]. Treat as implication.
                Lift [body] out of the [Prod]'s binder context so
                its de Bruijn indices line up with the surrounding
                term — [noccurn 1] guarantees the now-removed slot
                isn't referenced. *)
             Ir.Implies {
               antecedent = reify_term env sigma dom;
               consequent =
                 reify_term env sigma (EConstr.Vars.lift (-1) body);
             }
           else
             (* Dependent: a quantification. Reify the domain as an
                IR type-ref (function types preserved with parens),
                emit an [Ir.Forall], and push the binder into the
                env as a named local so the body reifies with the
                quantified name bound as a free [Ir.Var]. *)
             let var_name =
               match binder.Context.binder_name with
               | Names.Name id -> Names.Id.to_string id
               | Anonymous -> "_x"
             in
             let ty_string =
               match reify_type env sigma dom with
               | Some s -> s
               | None ->
                 reify_error "forall over unsupported type: %s"
                   (pp_econstr env sigma dom)
             in
             let fresh_id =
               let avoid = Termops.vars_of_env env in
               Namegen.next_ident_away_in_goal env
                 (Names.Id.of_string var_name) avoid
             in
             let push_decl =
               (* [push_named] takes [Constr.named_declaration], whose
                  annot uses [Sorts.relevance] directly (the kernel
                  side); [EConstr.ERelevance] is the EConstr-side
                  wrapper used by [econstr_named_declaration]. Since
                  we're pushing into [Environ.push_named], use the
                  kernel side. *)
               Context.Named.Declaration.LocalAssum
                 (Context.make_annot fresh_id Sorts.Relevant,
                  EConstr.to_constr sigma dom)
             in
             let env' = Environ.push_named push_decl env in
             let body' =
               EConstr.Vars.subst1 (EConstr.mkVar fresh_id) body
             in
             Ir.Forall {
               var = Names.Id.to_string fresh_id;
               ty = ty_string;
               body = reify_term env' sigma body';
             }
         | _ ->
           reify_error "unsupported term shape: %s"
             (pp_econstr env sigma t))

and reify_app env sigma head args full =
  let nargs = Array.length args in
  let r i = reify_term env sigma args.(i) in
  let head_is c = eq_ref sigma head c in
  if      head_is r_Zadd && nargs = 2 then bin "HAdd.hAdd" (r 0) (r 1)
  else if head_is r_Zsub && nargs = 2 then bin "HSub.hSub" (r 0) (r 1)
  else if head_is r_Zmul && nargs = 2 then bin "HMul.hMul" (r 0) (r 1)
  else if head_is r_Zopp && nargs = 1 then un  "Neg.neg"  (r 0)
  else if head_is r_Zle  && nargs = 2 then bin "LE.le"    (r 0) (r 1)
  else if head_is r_Zlt  && nargs = 2 then bin "LT.lt"    (r 0) (r 1)
  (* Mirror Lean: [Z.ge a b] reifies as [LE.le b a]. *)
  else if head_is r_Zge  && nargs = 2 then bin "LE.le"    (r 1) (r 0)
  else if head_is r_Zgt  && nargs = 2 then bin "LT.lt"    (r 1) (r 0)
  (* R operators: same typeclass-flavored shell vocabulary as the Z
     side. The shell is type-tag-agnostic; the type information is
     carried by [Num_lit.ty] / [free_var.ty] / [Eq.ty]. *)
  else if head_is r_Rplus  && nargs = 2 then bin "HAdd.hAdd" (r 0) (r 1)
  else if head_is r_Rminus && nargs = 2 then bin "HSub.hSub" (r 0) (r 1)
  else if head_is r_Rmult  && nargs = 2 then bin "HMul.hMul" (r 0) (r 1)
  else if head_is r_Ropp   && nargs = 1 then un  "Neg.neg"  (r 0)
  else if head_is r_Rle    && nargs = 2 then bin "LE.le"    (r 0) (r 1)
  else if head_is r_Rlt    && nargs = 2 then bin "LT.lt"    (r 0) (r 1)
  else if head_is r_Rge    && nargs = 2 then bin "LE.le"    (r 1) (r 0)
  else if head_is r_Rgt    && nargs = 2 then bin "LT.lt"    (r 1) (r 0)
  else if head_is r_eq   && nargs = 3 then begin
    (* Defer to [reify_type] for the equality's type argument so
       LIA / LRA / UF arrow-type / HOL function-type equalities all
       go through one path. The Phase-3 HOL test case
       [f = g : Z->Z] needs equality at arrow-typed terms, which
       the earlier LIA/LRA-only restriction explicitly rejected. *)
    match reify_type env sigma args.(0) with
    | Some tref -> Ir.Eq { ty = tref; left = r 1; right = r 2 }
    | None ->
      reify_error
        "equality over unsupported type: %s"
        (* Audit #18: use the passed [env] (the goal's local context),
           not [Global.env ()] — every other error site here does, and
           Global.env may lack section/local context, mis-printing the
           offending term. *)
        (pp_econstr env sigma full)
  end
  else if head_is r_and && nargs = 2 then
    Ir.And { left = r 0; right = r 1 }
  else if head_is r_or && nargs = 2 then
    Ir.Or { left = r 0; right = r 1 }
  else if head_is r_not && nargs = 1 then
    Ir.Not { operand = r 0 }
  else if head_is r_ex && nargs = 2 then begin
    (* [exists x : T, P] is [ex T (fun x => P)]. Mirror the
       dependent-Prod (Forall) path in [reify_term]: reify the
       domain as an IR type-ref, push the binder into the env as
       a named local, and emit an [Ir.Exists] whose body reifies
       with the bound name as a free [Ir.Var]. *)
    let dom = args.(0) in
    match EConstr.kind sigma args.(1) with
    | Lambda (binder, _, body) ->
      let var_name =
        match binder.Context.binder_name with
        | Names.Name id -> Names.Id.to_string id
        | Anonymous -> "_x"
      in
      let ty_string =
        match reify_type env sigma dom with
        | Some s -> s
        | None ->
          reify_error "exists over unsupported type: %s"
            (pp_econstr env sigma dom)
      in
      let fresh_id =
        let avoid = Termops.vars_of_env env in
        Namegen.next_ident_away_in_goal env
          (Names.Id.of_string var_name) avoid
      in
      let push_decl =
        Context.Named.Declaration.LocalAssum
          (Context.make_annot fresh_id Sorts.Relevant,
           EConstr.to_constr sigma dom)
      in
      let env' = Environ.push_named push_decl env in
      let body' =
        EConstr.Vars.subst1 (EConstr.mkVar fresh_id) body
      in
      Ir.Exists {
        var = Names.Id.to_string fresh_id;
        ty = ty_string;
        body = reify_term env' sigma body';
      }
    | _ ->
      reify_error "unsupported exists shape (expected a lambda): %s"
        (pp_econstr env sigma full)
  end
  else if EConstr.isVar sigma head && nargs > 0 then
    (* UF fallback: head is a local Var whose declared type is an
       arrow chain. Emit [App { symbol = "UF.<name>" }]; the SDK's
       [Smtlib.emit_decls] picks up the matching arrow-typed
       free_var declaration and renders [(declare-fun ...)] +
       application sites. The codomain may be any type
       [reify_type] accepts, including [Prop] for predicate-valued
       UF (see lean-bridge mirror). *)
    let head_ty = Retyping.get_type_of env sigma head in
    if is_arrow_type sigma head_ty then
      let name = Names.Id.to_string (EConstr.destVar sigma head) in
      let args_list =
        Array.to_list (Array.map (fun a -> reify_term env sigma a) args)
      in
      Ir.App { symbol = "UF." ^ name; type_args = []; args = args_list }
    else
      reify_error "unsupported application head: %s"
        (pp_econstr env sigma full)
  else
    reify_error "unsupported application head: %s"
      (pp_econstr env sigma full)

(* --- top-level: walk goal + locals --------------------------------- *)

let plugin_version = "0.1"

(* Walk the shell looking for higher-order shapes:
     * a [Forall] whose declared [ty] is an arrow chain (i.e.
       quantifying over a function), and
     * an [Eq] at an arrow-typed [ty] (equality on functions).
   Either is sufficient to bump the fragment from UF to HOL —
   they're the two features cvc5/z3 reject and Vampire-THF wants. *)
let rec shell_has_ho_features (t : Ir.shell_term) : bool =
  let arrow_ty s = Option.has_some (Smtlib.parse_arrow_type s) in
  match t with
  | Var _ | Const _ | Num_lit _ | Opaque _ -> false
  | Not { operand } -> shell_has_ho_features operand
  | And { left; right }
  | Or { left; right }
  | Implies { antecedent = left; consequent = right } ->
    shell_has_ho_features left || shell_has_ho_features right
  | Eq { ty; left; right } ->
    arrow_ty ty
    || shell_has_ho_features left || shell_has_ho_features right
  | Forall { ty; body; _ } | Exists { ty; body; _ } ->
    arrow_ty ty || shell_has_ho_features body
  | Lambda { body; _ } -> shell_has_ho_features body
  | App { args; _ } -> List.exists shell_has_ho_features args

(* Pick the fragment label from the IR contents (free vars +
   shells). Precedence:
     HOL — any [Forall] over an arrow-typed binder OR any [Eq] at
           an arrow type (quantification over / equality at
           function values — the features that route to Vampire
           THF). Carries [order = "higher_order"], matching the
           Lean reifier and example2-function-composition.json.
     UF  — any arrow-typed free var, OR any [App "UF.<name>"] in
           the goal/hypotheses (so closed UF-term goals carry the
           label even when the function symbol comes from a
           larger lemma's free_var rather than a direct local).
     LRA — any Real free var.
     LIA — default.
   Mirrors lean-bridge's [Reify.buildIR] precedence. *)
let logic_for (ir : Ir.t) : Ir.logic_classification =
  let any_hol =
    shell_has_ho_features ir.goal.shell
    || List.exists (fun (h : Ir.hypothesis) -> shell_has_ho_features h.shell)
         ir.context.hypotheses
  in
  let any_uf =
    List.exists
      (fun (fv : Ir.free_var) -> Option.has_some (Smtlib.parse_arrow_type fv.ty))
      ir.context.free_vars
    || Smtlib.shell_mentions_uf ir.goal.shell
    || List.exists (fun (h : Ir.hypothesis) -> Smtlib.shell_mentions_uf h.shell)
         ir.context.hypotheses
  in
  let any_real =
    List.exists (fun (fv : Ir.free_var) -> fv.ty = "Real")
      ir.context.free_vars
  in
  let order, frag =
    if any_hol then "higher_order", "HOL"
    else if any_uf then "first_order", "UF"
    else if any_real then "first_order", "LRA"
    else "first_order", "LIA"
  in
  (* R2 honesty: features_used reports what the reifier actually
     emitted (registry logical_features ids), mirroring the Lean
     reifier's shellQuantEqFlags. *)
  let rec flags (t : Ir.shell_term) ((fa, ex, eq) as acc) =
    match t with
    | Ir.Var _ | Ir.Const _ | Ir.Num_lit _ | Ir.Opaque _ -> acc
    | Ir.Forall { body; _ } -> flags body (true, ex, eq)
    | Ir.Exists { body; _ } -> flags body (fa, true, eq)
    | Ir.Lambda { body; _ } | Ir.Not { operand = body } -> flags body acc
    | Ir.Implies { antecedent = a; consequent = b }
    | Ir.And { left = a; right = b } | Ir.Or { left = a; right = b } ->
      flags b (flags a acc)
    | Ir.Eq { left = a; right = b; _ } -> flags b (flags a (fa, ex, true))
    | Ir.App { args; _ } -> List.fold_left (fun acc a -> flags a acc) acc args
  in
  let shells =
    ir.goal.shell
    :: List.map (fun (h : Ir.hypothesis) -> h.shell) ir.context.hypotheses
  in
  let fa, ex, eq =
    List.fold_left (fun acc s -> flags s acc) (false, false, false) shells
  in
  let features_used =
    (if fa then [ "universal_quantification_over_first_order" ] else [])
    @ (if ex then [ "existential_quantification_over_first_order" ] else [])
    @ (if eq then [ "equality_at_first_order_type" ] else [])
    @ (if any_hol then [ "function_quantification" ] else [])
  in
  {
    order;
    features_used;
    first_order_fragment = frag;
    decidable_theory = None;
  }

let build_ir gl : Ir.t =
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let goal_type = Proofview.Goal.concl gl in
  let goal_shell = reify_term env sigma goal_type in
  (* Walk locals: Z-typed → free_var (Int), R-typed → free_var (Real),
     Prop-typed → hypothesis; anything else is ignored (the goal/Prop
     reifier will trip on it later if it's actually referenced). *)
  let free_vars = ref [] in
  let hypotheses = ref [] in
  let lctx = Environ.named_context_val env in
  let named = Environ.named_context_of_val lctx in
  List.iter (fun decl ->
    let id = Context.Named.Declaration.get_id decl in
    let ty = EConstr.of_constr (Context.Named.Declaration.get_type decl) in
    (* Do NOT reduce [ty]: [whd_all] would unfold [Z.ge x y] into
       [(x ?= y) = Lt -> False] and the reifier then can't see the
       [Z.ge] head. Passing the raw type means [Z.ge] stays folded
       and the head-match in [reify_app] picks it up. *)
    if eq_ref sigma ty r_Z then
      free_vars := { Ir.name = Names.Id.to_string id; ty = "Int" } :: !free_vars
    else if eq_ref sigma ty r_R then
      free_vars := { Ir.name = Names.Id.to_string id; ty = "Real" } :: !free_vars
    else if Termops.is_Prop sigma ty then
      (* A local [p : Prop] is a Boolean ATOM (its type IS Prop),
         not a hypothesis (a local whose type merely LIVES in
         Prop; the branch below). Declare it as a free var — the
         SDK serializer maps the [Prop] type ref to SMT-LIB
         [Bool] — so pure-propositional goals dispatch with
         their atoms declared. *)
      free_vars := { Ir.name = Names.Id.to_string id; ty = "Prop" } :: !free_vars
    else if is_arrow_type sigma ty then
      (* Function-typed local: UF candidate. Encode the type as the
         arrow chain the SDK serializer parses; codomain may be a
         primitive (Int/Real) or Prop (predicate-valued UF). *)
      (match reify_type env sigma ty with
       | Some tref ->
         free_vars := { Ir.name = Names.Id.to_string id; ty = tref } :: !free_vars
       | None ->
         (* arrow-shaped but at least one component outside Z/R/Prop —
            skip silently; if the goal references it the reifier will
            error there with a useful message. *)
         ())
    else if Termops.is_Prop sigma (Retyping.get_type_of env sigma ty) then
      let shell = reify_term env sigma ty in
      hypotheses := { Ir.name = Names.Id.to_string id; shell } :: !hypotheses
    (* else: not a LIA/LRA/UF-relevant local; skip silently. *)
  ) (List.rev named);
  let free_vars = List.rev !free_vars in
  let hypotheses = List.rev !hypotheses in
  let ir : Ir.t = {
    ir_version = "1.0";
    source_system = { name = "rocq"; version = plugin_version };
    (* R2 honesty: "structural" whenever typed hypotheses ride
       along (spec §4.5: "goal" = proposition only). *)
    tier = (if hypotheses = [] then "goal" else "structural");
    (* Filled in below — needs the goal+hypotheses to be in scope
       so [shell_mentions_uf] / [shell_has_ho_features] can detect
       UF / HOL signals introduced by the reified shells. The
       placeholder [LIA / first_order] is replaced by [logic_for]'s
       computed values; the [{ ir with ... }] update at the
       function's exit is the single point of truth. *)
    logic_classification = {
      order = "first_order";
      features_used = [];
      first_order_fragment = "LIA";
      decidable_theory = None;
    };
    goal = { shell = goal_shell; payloads = None };
    context = {
      type_vars = [];
      free_vars;
      hypotheses;
      library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  } in
  { ir with logic_classification = logic_for ir }

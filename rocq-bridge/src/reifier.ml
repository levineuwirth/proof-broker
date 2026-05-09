module Ir = Proof_broker.Ir

(* --- lib_ref-resolved Constr atoms ---------------------------------- *)

let constr_of_ref s =
  EConstr.of_constr
    (UnivGen.constr_of_monomorphic_global (Global.env ()) (Rocqlib.lib_ref s))

(* Z and positive constructors. *)
let r_Z0   = lazy (constr_of_ref "num.Z.Z0")
let r_Zpos = lazy (constr_of_ref "num.Z.Zpos")
let r_Zneg = lazy (constr_of_ref "num.Z.Zneg")
let r_xH   = lazy (constr_of_ref "num.pos.xH")
let r_xO   = lazy (constr_of_ref "num.pos.xO")
let r_xI   = lazy (constr_of_ref "num.pos.xI")
let r_Z    = lazy (constr_of_ref "num.Z.type")

(* Z arithmetic + ordering. *)
let r_Zadd = lazy (constr_of_ref "num.Z.add")
let r_Zsub = lazy (constr_of_ref "num.Z.sub")
let r_Zmul = lazy (constr_of_ref "num.Z.mul")
let r_Zopp = lazy (constr_of_ref "num.Z.opp")
let r_Zle  = lazy (constr_of_ref "num.Z.le")
let r_Zlt  = lazy (constr_of_ref "num.Z.lt")
let r_Zge  = lazy (constr_of_ref "num.Z.ge")
let r_Zgt  = lazy (constr_of_ref "num.Z.gt")

(* Logic. *)
let r_eq    = lazy (constr_of_ref "core.eq.type")
let r_and   = lazy (constr_of_ref "core.and.type")
let r_or    = lazy (constr_of_ref "core.or.type")
let r_not   = lazy (constr_of_ref "core.not.type")
let r_True  = lazy (constr_of_ref "core.True.type")
let r_False = lazy (constr_of_ref "core.False.type")

let eq sigma a b = EConstr.eq_constr_nounivs sigma a b

exception Reify_error of string

let reify_error fmt =
  Printf.ksprintf (fun s -> raise (Reify_error s)) fmt

let pp_econstr env sigma t =
  Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t)

(* --- positive / Z literals ----------------------------------------- *)

let rec positive_to_z env sigma p : Z.t =
  let p = Reductionops.whd_all env sigma p in
  if eq sigma p (Lazy.force r_xH) then Z.one
  else
    match EConstr.kind sigma p with
    | App (head, [| inner |]) when eq sigma head (Lazy.force r_xO) ->
      Z.shift_left (positive_to_z env sigma inner) 1
    | App (head, [| inner |]) when eq sigma head (Lazy.force r_xI) ->
      Z.add Z.one (Z.shift_left (positive_to_z env sigma inner) 1)
    | _ ->
      reify_error "expected positive (xH/xO/xI), got: %s"
        (pp_econstr env sigma p)

let reify_z_literal env sigma t : string option =
  let t = Reductionops.whd_all env sigma t in
  if eq sigma t (Lazy.force r_Z0) then Some "0"
  else
    match EConstr.kind sigma t with
    | App (head, [| p |]) when eq sigma head (Lazy.force r_Zpos) ->
      Some (Z.to_string (positive_to_z env sigma p))
    | App (head, [| p |]) when eq sigma head (Lazy.force r_Zneg) ->
      Some ("-" ^ Z.to_string (positive_to_z env sigma p))
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
     [Zpos (xO xH)] is structurally an application. *)
  (match reify_z_literal env sigma t with
   | Some v -> Ir.Num_lit { value = v; ty = "Int" }
   | None ->
     if EConstr.isVar sigma t then
       Ir.Var { name = Names.Id.to_string (EConstr.destVar sigma t) }
     else if eq sigma t (Lazy.force r_True) then Ir.Const { name = "True" }
     else if eq sigma t (Lazy.force r_False) then Ir.Const { name = "False" }
     else
       match EConstr.kind sigma t with
       | App (head, args) -> reify_app env sigma head args t
       | _ ->
         reify_error "unsupported term shape: %s"
           (pp_econstr env sigma t))

and reify_app env sigma head args full =
  let nargs = Array.length args in
  let r i = reify_term env sigma args.(i) in
  let head_is c = eq sigma head (Lazy.force c) in
  if      head_is r_Zadd && nargs = 2 then bin "HAdd.hAdd" (r 0) (r 1)
  else if head_is r_Zsub && nargs = 2 then bin "HSub.hSub" (r 0) (r 1)
  else if head_is r_Zmul && nargs = 2 then bin "HMul.hMul" (r 0) (r 1)
  else if head_is r_Zopp && nargs = 1 then un  "Neg.neg"  (r 0)
  else if head_is r_Zle  && nargs = 2 then bin "LE.le"    (r 0) (r 1)
  else if head_is r_Zlt  && nargs = 2 then bin "LT.lt"    (r 0) (r 1)
  (* Mirror Lean: [Z.ge a b] reifies as [LE.le b a]. *)
  else if head_is r_Zge  && nargs = 2 then bin "LE.le"    (r 1) (r 0)
  else if head_is r_Zgt  && nargs = 2 then bin "LT.lt"    (r 1) (r 0)
  else if head_is r_eq   && nargs = 3 then begin
    if eq sigma args.(0) (Lazy.force r_Z) then
      Ir.Eq { ty = "Int"; left = r 1; right = r 2 }
    else
      reify_error
        "non-Z equality outside LIA fragment: %s"
        (pp_econstr (Global.env ()) sigma full)
  end
  else if head_is r_and && nargs = 2 then
    Ir.And { left = r 0; right = r 1 }
  else if head_is r_or && nargs = 2 then
    Ir.Or { left = r 0; right = r 1 }
  else if head_is r_not && nargs = 1 then
    Ir.Not { operand = r 0 }
  else
    reify_error "unsupported application head: %s"
      (pp_econstr env sigma full)

(* --- top-level: walk goal + locals --------------------------------- *)

let lia_logic_classification : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LIA";
  decidable_theory = None;
}

let plugin_version = "0.1"

let build_ir gl : Ir.t =
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let goal_type = Proofview.Goal.concl gl in
  let goal_shell = reify_term env sigma goal_type in
  (* Walk locals: Z-typed → free_var, Prop-typed → hypothesis,
     anything else → ignored (the goal/Prop reifier will trip on
     it later if it's actually referenced). *)
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
    if eq sigma ty (Lazy.force r_Z) then
      free_vars := { Ir.name = Names.Id.to_string id; ty = "Int" } :: !free_vars
    else if Termops.is_Prop sigma (Retyping.get_type_of env sigma ty) then
      let shell = reify_term env sigma ty in
      hypotheses := { Ir.name = Names.Id.to_string id; shell } :: !hypotheses
    (* else: not a LIA-relevant local; skip silently. *)
  ) (List.rev named);
  {
    ir_version = "1.0";
    source_system = { name = "rocq"; version = plugin_version };
    tier = "goal";
    logic_classification = lia_logic_classification;
    goal = { shell = goal_shell; payloads = None };
    context = {
      type_vars = [];
      free_vars = List.rev !free_vars;
      hypotheses = List.rev !hypotheses;
      library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

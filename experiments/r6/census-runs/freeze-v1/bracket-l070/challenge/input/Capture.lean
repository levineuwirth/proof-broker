import Lean
import Lean.Elab.Tactic.Omega

/- Trusted extraction instrumentation for any `omega` site, compiled separately
   from the task. The R6-000 helper (`Capture.lean`) fixed one saved-declaration
   name and one task identity in its body; this helper takes both as string
   literals, so the same bytes capture a named `have`, a bare goal-closing
   `omega`, a post-`simp` closer, an inline `(by omega)` term or a `calc` step:
   the capture is of the goal state at the site, whatever syntax surrounds it.
   Keep the entire telescope, including let values and unused binders. -/
open Lean Meta Elab Tactic

private def render (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty

elab "r6_capture_human" savedName:str siteId:str : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let lctx ← getLCtx
  let mut xs := #[]
  let mut entries : Array Json := #[]
  for decl in lctx do
    -- Lean exposes the containing declaration's recursive placeholder as an
    -- auxiliary local. Record it, but never turn it into a theorem assumption.
    unless decl.isAuxDecl do xs := xs.push decl.toExpr
    let value : Json ← match decl.value? (allowNondep := true) with
      | none => pure Json.null
      | some value => do pure <| toJson (← render value)
    entries := entries.push <| Json.mkObj [
      ("index", toJson decl.index),
      ("name", toJson decl.userName.toString),
      ("binder_info", toJson (reprStr decl.binderInfo)),
      ("implementation_detail", toJson decl.isImplementationDetail),
      ("included_in_telescope", toJson (!decl.isAuxDecl)),
      ("nondependent_let", toJson decl.isNondep),
      ("kind", toJson (if decl.isAuxDecl then "declaration_placeholder"
        else if decl.isLet (allowNondep := true) then "let" else "hypothesis")),
      ("type", toJson (← render decl.type)),
      ("value", value)]
  let closedType ← mkForallFVars xs target
    (usedOnly := false) (usedLetOnly := false) (generalizeNondepLet := false)
  let closedType ← instantiateMVars closedType
  if closedType.hasFVar || closedType.hasMVar then
    throwError "R6 extraction left an open type"
  -- Solve a separate metavariable so the original hole receives the named
  -- saved proof, not the tactic's inlined result.
  let trial ← mkFreshExprMVar target
  setGoals [trial.mvarId!]
  evalTactic (← `(tactic| omega))
  unless (← getGoals).isEmpty do throwError "R6 human proof left goals"
  let value ← instantiateMVars trial
  let closedValue ← mkLambdaFVars xs value
    (usedOnly := false) (usedLetOnly := false) (generalizeNondepLet := false)
  let closedValue ← instantiateMVars closedValue
  if closedValue.hasFVar || closedValue.hasMVar then
    throwError "R6 extraction left an open proof"
  let name := savedName.getString.toName
  if name.isAnonymous || (← getEnv).contains name then
    throwError "R6 saved declaration name is unusable: {savedName.getString}"
  addDecl <| .thmDecl {
    name, levelParams := [], type := closedType, value := closedValue }
  -- Let-bound entries are retained in the closed telescope, not generalized
  -- into extra assumptions; only ordinary binders become application args.
  let args := xs.filter fun x => !(lctx.get! x.fvarId!).isLet (allowNondep := true)
  goal.assign (mkAppN (mkConst name) args)
  setGoals []
  let out ← IO.getEnv "R6_CAPTURE_OUTPUT"
  let some out := out | throwError "R6_CAPTURE_OUTPUT is required"
  IO.FS.writeFile out <| (Json.mkObj [
    ("task_id", toJson siteId.getString),
    ("local_declaration", toJson name.toString),
    ("target", toJson (← render target)),
    ("telescope", toJson entries),
    ("closed_type", toJson (← render closedType))]).pretty ++ "\n"

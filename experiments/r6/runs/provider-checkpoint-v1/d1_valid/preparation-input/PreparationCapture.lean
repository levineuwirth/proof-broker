import Lean
import ProofBroker
import Lean.Elab.Tactic.Omega

/- Trusted extraction instrumentation, compiled separately from the task.
   Keep the entire telescope, including let values and unused binders. -/
open Lean Meta Elab Tactic

private def render (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty

elab "r6_prepare" : tactic => withMainContext do
  let goal ← getMainGoal
  let (ir, _, _, skipped) ← ProofBroker.Tactic.Reify.buildIR goal
  let some irOut ← IO.getEnv "R6_PREPARE_OUTPUT" | throwError "R6_PREPARE_OUTPUT is required"
  let ir := { ir with userDirectives := ir.userDirectives.map fun ud =>
    {ud with tierPreference := some ["1", "2"]} }
  IO.FS.writeFile irOut <| (Json.mkObj [
    ("ir", ProofBroker.IR.IR.toJson ir),
    ("skipped_locals", toJson (skipped.map fun (name, reason) =>
      Json.mkObj [("name", toJson name), ("reason", toJson reason)]))]).compress
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
  let name := `Bracket.lift_cell.r6_d1_70
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
    ("task_id", "verinf-d1-70"),
    ("local_declaration", toJson name.toString),
    ("target", toJson (← render target)),
    ("telescope", toJson entries),
    ("closed_type", toJson (← render closedType))]).pretty ++ "\n"

import Lean
import ProofBroker
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

-- R6-013: pinned from ProofBroker/Tactic.lean at e627efe, verbatim.
private def smtSymbolTailChar (c : Char) : Bool :=
  c.isAlphanum || "~!@$%^&*_-+=<>.?/".any (· == c)

private def smtReservedWords : List String :=
  ["let", "forall", "exists", "match", "as", "par", "_",
   "Bool", "Int", "Real"]

private def smtSafeIdent (s : String) : Bool :=
  !s.isEmpty
  && smtSymbolTailChar s.front && !s.front.isDigit
  && s.all smtSymbolTailChar
  && !(smtReservedWords.contains s)

private def smtSanitizeIdent (s : String) : String :=
  let mapped := String.ofList (s.toList.map (fun c => if smtSymbolTailChar c then c else '_'))
  let mapped := if mapped.isEmpty then "_pb_v"
                else if mapped.front.isDigit then "x" ++ mapped
                else mapped
  if smtReservedWords.contains mapped then mapped ++ "_" else mapped

private def renameLocalsForSmt (goal : MVarId) : TacticM MVarId := do
  let renames ← goal.withContext do
    let mut acc : Array (FVarId × String) := #[]
    -- Duplicate user names (`have := e` twice ⇒ two `this`) give the
    -- IR duplicate hypothesis names: the SDK's Farkas search then
    -- finds a positional witness the by-name verifier rejects — a
    -- false "not contradictory" on a provable goal (CONTINUATION
    -- ROUND 1 Med 3, the D3/178 shape). Rename every occurrence but
    -- the LAST (the one unqualified references resolve to), exactly
    -- as unsafe identifiers are renamed below.
    let mut lastOf : Std.HashMap String FVarId := {}
    let mut order : Array (String × FVarId) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let n := decl.userName.toString
      order := order.push (n, decl.fvarId)
      lastOf := lastOf.insert n decl.fvarId
    for (n, fid) in order do
      if lastOf[n]? != some fid then
        acc := acc.push (fid, smtSanitizeIdent n)
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if acc.any (·.1 == decl.fvarId) then continue
      unless smtSafeIdent decl.userName.toString do
        acc := acc.push (decl.fvarId, smtSanitizeIdent decl.userName.toString)
    pure acc
  if renames.isEmpty then return goal
  let mut g := goal
  for (fvarId, base) in renames do
    let fresh ← g.withContext do
      let cand := (← getLCtx).getUnusedName (Name.mkSimple base)
      -- `getUnusedName` disambiguates by appending an index; guard
      -- the result anyway rather than assume the shape of the
      -- suffix, and fall back to a synthetic name that cannot
      -- collide with a source identifier.
      if smtSafeIdent cand.toString then
        pure cand
      else
        pure ((← getLCtx).getUnusedName (Name.mkSimple "_pb_v"))
    g ← g.rename fvarId fresh
  replaceMainGoal [g]
  return g

private def normalizeGoalForBroker (goal : MVarId) : TacticM MVarId := do
  Lean.instantiateMVarDeclMVars goal
  let ty ← goal.getType
  let ty' := ty.consumeMData
  unless ty' == ty do goal.setType ty'
  return goal

private partial def introLeadingNatForalls (goal : MVarId) : TacticM MVarId := do
  let ty ← goal.withContext do Lean.instantiateMVars (← goal.getType)
  match ty with
  | .forallE _ dom _ _ =>
    if dom.isConstOf ``Nat then
      let (_, goal') ← goal.intro1P
      let goal'' ← introLeadingNatForalls goal'
      replaceMainGoal [goal'']
      return goal''
    else return goal
  | _ => return goal

elab "r6_prepare" savedName:str siteId:str : tactic => withMainContext do
  let goal ← getMainGoal
  -- R6-013: the pinned term-mode prefix of `evalProofBrokerTerm`, on a saved and restored state: the search goal is normalized,
  -- its leading ℕ binders introduced and its locals renamed exactly as reconstruction will do; the original goal, the frozen
  -- context captured below and the saved declaration are untouched. The renamed search context is recorded by local index.
  let (ir, skipped, searchContext) ← withoutModifyingState do
    setGoals [goal]
    let original ← goal.withContext getLCtx
    let g ← normalizeGoalForBroker goal
    let g ← introLeadingNatForalls g
    let g ← renameLocalsForSmt g
    let (ir, _, _, skipped) ← ProofBroker.Tactic.Reify.buildIR g
    let searchContext ← g.withContext do
      let mut rows : Array Json := #[]
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let before := (original.find? decl.fvarId).map (·.userName.toString)
        rows := rows.push <| Json.mkObj [("index", toJson decl.index), ("fvar_in_original", toJson before.isSome),
          ("original_name", toJson before), ("search_name", toJson decl.userName.toString)]
      pure rows
    pure (ir, skipped, searchContext)
  let some irOut ← IO.getEnv "R6_PREPARE_OUTPUT" | throwError "R6_PREPARE_OUTPUT is required"
  -- R6-013: `buildExtractionPath`'s merge: the tier preference is added to existing directives or creates them.
  let ir :=
      let ud := ir.userDirectives.getD {
        preferredBackend := none, tierPreference := none,
        rewriterPreferences := none, budget := none }
      { ir with userDirectives := some { ud with tierPreference := some ["1", "2"] } }
  IO.FS.writeFile irOut <| (Json.mkObj [
    ("ir", ProofBroker.IR.IR.toJson ir),
    ("skipped_locals", toJson (skipped.map fun (name, reason) =>
      Json.mkObj [("name", toJson name), ("reason", toJson reason)])),
    ("search_context", toJson searchContext)]).compress
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

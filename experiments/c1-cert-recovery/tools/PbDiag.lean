/-
PbDiag.lean — campaign-local diagnostic tactics. DIAGNOSTIC ONLY.

Nothing here is part of the SDK or the bridge; this module is compiled into
this campaign's own `.build` and imported by the capture files under `ir/`.
It adds no closer and proves nothing — its whole job is to write out, byte
for byte, the IR the production tactic would dispatch at a given goal, so
the OCaml side can be driven on exactly that document.

Faithfulness. `ProofBroker.Tactic.evalProofBroker` runs three front-end
steps before `Reify.buildIR`:

    normalizeGoalForBroker  →  introLeadingNatForalls  →  renameLocalsForSmt

All three are `private` in `ProofBroker/Tactic.lean`, so they are COPIED
here verbatim (bridge at the hash recorded in baseline/artifacts-before.txt;
`tools/check_pbdiag_drift.sh` diffs the copies against the source). Copying
rather than re-deriving is deliberate: a paraphrase would silently make the
dumped IR a different IR from the dispatched one, which is the one thing
this module must not do.
-/
import ProofBroker
import ProofBrokerMathlib

open Lean Lean.Elab.Tactic Lean.Meta ProofBroker.IR

namespace PbDiag

/-- COPY of `ProofBroker.Tactic.normalizeGoalForBroker`. -/
private def normalizeGoalForBroker (goal : MVarId) : TacticM MVarId := do
  Lean.instantiateMVarDeclMVars goal
  let ty ← goal.getType
  let ty' := ty.consumeMData
  unless ty' == ty do goal.setType ty'
  return goal

/-- COPY of `ProofBroker.Tactic.introLeadingNatForalls`. -/
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

/-- COPY of `ProofBroker.Tactic.smtSymbolTailChar`. -/
private def smtSymbolTailChar (c : Char) : Bool :=
  c.isAlphanum || "~!@$%^&*_-+=<>.?/".any (· == c)

/-- COPY of `ProofBroker.Tactic.smtReservedWords`. -/
private def smtReservedWords : List String :=
  ["let", "forall", "exists", "match", "as", "par", "_",
   "Bool", "Int", "Real"]

/-- COPY of `ProofBroker.Tactic.smtSafeIdent`. -/
private def smtSafeIdent (s : String) : Bool :=
  !s.isEmpty
  && smtSymbolTailChar s.front && !s.front.isDigit
  && s.all smtSymbolTailChar
  && !(smtReservedWords.contains s)

/-- COPY of `ProofBroker.Tactic.smtSanitizeIdent`. -/
private def smtSanitizeIdent (s : String) : String :=
  let mapped := String.ofList (s.toList.map (fun c => if smtSymbolTailChar c then c else '_'))
  let mapped := if mapped.isEmpty then "_pb_v"
                else if mapped.front.isDigit then "x" ++ mapped
                else mapped
  if smtReservedWords.contains mapped then mapped ++ "_" else mapped

/-- COPY of `ProofBroker.Tactic.renameLocalsForSmt`. -/
private def renameLocalsForSmt (goal : MVarId) : TacticM MVarId := do
  let renames ← goal.withContext do
    let mut acc : Array (FVarId × String) := #[]
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
      if smtSafeIdent cand.toString then
        pure cand
      else
        pure ((← getLCtx).getUnusedName (Name.mkSimple "_pb_v"))
    g ← g.rename fvarId fresh
  replaceMainGoal [g]
  return g

/-- `pb_dump_ir "<path>"` — write the reified IR of the current goal to
    `<path>` (pretty JSON) and leave the goal untouched. Also logs the
    skipped locals and the ℕ-atom / numeral-def tables, which are the two
    pieces of reifier state a reader cannot recover from the IR alone. -/
syntax (name := pbDumpIr) "pb_dump_ir" str : tactic

@[tactic pbDumpIr]
def evalPbDumpIr : Tactic := fun stx => do
  let path : String ← match stx with
    | `(tactic| pb_dump_ir $s:str) => pure s.getString
    | _ => throwError "pb_dump_ir: malformed invocation"
  let goal ← getMainGoal
  let goal ← normalizeGoalForBroker goal
  let goal ← introLeadingNatForalls goal
  let goal ← renameLocalsForSmt goal
  let (ir, natAtoms, natDefs, skipped) ← ProofBroker.Tactic.Reify.buildIR goal
  let j := ProofBroker.IR.IR.toJson ir
  IO.FS.writeFile path (j.pretty ++ "\n")
  let skippedStr := String.intercalate "; "
    (skipped.toList.map (fun (n, why) => s!"{n} — {why}"))
  let atomStr := String.intercalate ", " (natAtoms.toList.map (·.1))
  let defStr := String.intercalate ", "
    (natDefs.toList.map (fun (n, _, v) => s!"{n}={v}"))
  let msg :=
    s!"pb_dump_ir: wrote {path}" ++
    s!" | hypotheses={ir.context.hypotheses.length}" ++
    s!" fragment={ir.logicClassification.firstOrderFragment}" ++
    s!" | skipped_locals=[{skippedStr}]" ++
    s!" | nat_atoms=[{atomStr}]" ++
    s!" | numeral_defs=[{defStr}]"
  logInfo msg

end PbDiag

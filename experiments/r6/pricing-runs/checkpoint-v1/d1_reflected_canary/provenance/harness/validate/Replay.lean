import Lean
import Lean.Replay
import Comparator
import Export.Parse

/- Saved-export adapter to leanprover/comparator (see vendor/sources.lock.json).
   It does not import a candidate module or execute candidate source. The
   kernel replay and quotient post-check follow Comparator/Main.lean at the
   pinned revision; filesystem isolation is supplied by run.py/Bubblewrap.
   Portions copyright (c) 2025 Lean FRO, LLC (Henrik Böving), Apache-2.0;
   see vendor/comparator/LICENSE. Modified for this frozen-task interface. -/
open Lean

structure Policy where
  theorem_names : Array String
  permitted_axioms : Array String
  primitive_names : Array String
  required_dependency : Option (String × String) := none
  deriving FromJson

private def parseFile (path : String) : IO Export.ExportedEnv := do
  let handle ← IO.FS.Handle.mk path .read
  let stream := IO.FS.Stream.ofHandle handle
  -- The upstream parseStream skips metadata. This artifact accepts one pinned
  -- format and validates every complete JSON line, including the header.
  let header ← IO.ofExcept <| Json.parse (← stream.getLine)
  let expectedHeader ← IO.ofExcept <| Json.parse
    "{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"8c9756b28d64dab099da31a4c09229a9e6a2ef35\",\"version\":\"4.32.0\"}}}"
  unless header == expectedHeader do
    throw <| IO.userError "Export metadata does not match the frozen format/environment"
  let items : Export.Parse.M Unit := do
    repeat
      let line ← stream.getLine
      if line.isEmpty then break
      discard <| IO.ofExcept (Json.parse line)
      Export.Parse.parseItem line
  let (_, state) ← Export.Parse.M.run items stream
  return { constMap := state.constMap, constOrder := state.constOrder }

private def verifyIsolation (challenge solution policy : String) : IO Unit := do
  for path in ["/home", "/env", "/toolchain", "/bin", "/usr/bin"] do
    if ← System.FilePath.pathExists path then
      throw <| IO.userError s!"Unexpected host/search path in validator: {path}"
  for envName in ["LEAN_PATH", "LD_PRELOAD", "PROOF_BROKER_FFI_DIR"] do
    if (← IO.getEnv envName).isSome then
      throw <| IO.userError s!"Unexpected inherited environment: {envName}"
  for path in [challenge, solution, policy] do
    let writable ← try
      let handle ← IO.FS.Handle.mk path .append
      handle.flush
      pure true
    catch _ => pure false
    if writable then throw <| IO.userError s!"Validation input is writable: {path}"

private def dependencyClosure (env : Export.ExportedEnv) (targets legal : Array Name) :
    Except String (Std.HashSet Name) := do
  let (_, state) ← (Comparator.Axioms.loop.run {
    solution := env, legalAxioms := Std.HashSet.ofArray legal
  }).run { worklist := targets, checked := {} }
  return state.checked

private def footprint (env : Export.ExportedEnv) (target : Name) (legal : Array Name) : Except String (Array Name) := do
  let closure ← dependencyClosure env #[target] legal
  return closure.toArray.filter fun n =>
    match env.constMap[n]? with | some (.axiomInfo _) => true | _ => false

private def replay (solution : Export.ExportedEnv) (targets : Array Name) : IO Unit := do
  let env ← Lean.mkEmptyEnvironment
  for (name, info) in solution.constMap do
    if info.isUnsafe || info.isPartial then
      throw <| IO.userError s!"Unsafe/partial exported declaration: {name}"
  let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]
  let constants := quotTargets.foldl (init := solution.constMap) (·.erase ·)
  -- Lean 4.32.2 exposes replay on Environment rather than Kernel.Environment.
  let replayed ← env.replay constants
  let kernelEnv := replayed.toKernelEnv
  for target in `Quot :: quotTargets do
    if let some original := solution.constMap[target]? then
      let some checked := kernelEnv.find? target
        | throw <| IO.userError s!"Missing quotient constant after replay: {target}"
      unless original == checked do
        throw <| IO.userError s!"Quotient constant mismatch: {target}"
  for target in targets do
    let some checked := kernelEnv.find? target
      | throw <| IO.userError s!"Expected theorem missing after replay: {target}"
    unless some checked == solution.constMap[target]? do
      throw <| IO.userError s!"Expected theorem changed during replay: {target}"

def main (args : List String) : IO UInt32 := do
  let [challengePath, solutionPath, policyPath, reportPath] := args
    | IO.eprintln "usage: r6-replay CHALLENGE.ndjson SOLUTION.ndjson POLICY.json REPORT.json"; return 2
  let stage ← IO.mkRef "isolation"
  try
    verifyIsolation challengePath solutionPath policyPath
    stage.set "policy"
    let policy : Policy ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile policyPath))
    if policy.theorem_names.isEmpty then throw <| IO.userError "Empty target set"
    stage.set "export_parse"
    let challenge ← parseFile challengePath
    let solution ← parseFile solutionPath
    let targets := policy.theorem_names.map String.toName
    let axioms := policy.permitted_axioms.map String.toName
    let primitives := policy.primitive_names.map String.toName
    stage.set "challenge_match"
    IO.ofExcept <| Comparator.compareAt challenge solution (targets ++ axioms) #[] primitives
    stage.set "axiom_policy"
    IO.ofExcept <| Comparator.checkAxioms solution targets #[] axioms
    stage.set "local_proof_binding"
    if let some (container, localName) := policy.required_dependency then
      let some info := solution.constMap[container.toName]?
        | throw <| IO.userError s!"Missing container: {container}"
      let some value := info.value? (allowOpaque := true)
        | throw <| IO.userError s!"Container has no proof: {container}"
      unless value.getUsedConstants.contains localName.toName do
        throw <| IO.userError s!"Container does not reference local proof: {localName}"
    stage.set "kernel_replay"
    -- Check only the dependency closure of these named targets and the pinned
    -- primitives. Separate invocations can therefore report local success even
    -- when a different, unrelated containing proof is invalid.
    let closure ← IO.ofExcept <| dependencyClosure solution (targets ++ axioms ++ primitives) axioms
    let relevant := { solution with constMap := solution.constMap.filter fun n _ => closure.contains n }
    replay relevant targets
    let mut results := #[]
    for target in targets do
      let info := solution.constMap[target]!
      let axs ← IO.ofExcept <| footprint solution target axioms
      results := results.push <| Json.mkObj [
        ("name", toJson target.toString),
        ("declaration_exists", true),
        ("statement_and_dependencies_match", true),
        ("kernel_accepted", true),
        ("type_repr", toJson (reprStr info.type)),
        ("axioms", toJson (axs.map Name.toString |>.qsort (· < ·)))]
    let report := Json.mkObj [
      ("accepted", true), ("stage", "complete"),
      ("checked_declarations", toJson relevant.constMap.size),
      ("targets", toJson results),
      ("local_proof_binding_checked", toJson policy.required_dependency.isSome),
      ("kernel_version", toJson Lean.versionString)]
    IO.FS.writeFile reportPath (report.pretty ++ "\n")
    return 0
  catch error =>
    let stage ← stage.get
    let report := Json.mkObj [
      ("accepted", false), ("stage", toJson stage), ("error", toJson error.toString)]
    IO.FS.writeFile reportPath (report.pretty ++ "\n")
    IO.eprintln s!"{stage}: {error}"
    return 1

/-
End-to-end FFI round-trip test, typed-IR edition.

Exercises the typed Lean surface across the FFI:
  * Three IR fixtures parse to typed `IR`, ship through
    `roundtripIR : IR → Except FfiError IR`, and the returned IR
    re-serializes to JSON that's structurally equal to the original
    fixture after normalization (recursive key sort, per
    `sdk/FFI_CONVENTIONS.md`).
  * Lexical garbage at the boundary surfaces as
    `FfiError.jsonParseError` — exercised through the raw-JSON
    drop-down (`pbCall + decodeEnvelope`) since the typed wrapper
    can't be called with non-IR input.
  * Calling an unknown method surfaces as `FfiError.unknownMethod`,
    proving the dispatcher's only synthetic envelope decodes through
    the typed Lean surface end-to-end.
  * Local `IR.fromJsonString` rejects malformed IR JSON before any
    FFI call — proving the Lean codec mirrors `Codec.of_json`.

Exits 0 on success, 1 on any failure path.
-/

import ProofBroker
import Lean.Data.Json

open Lean (Json)
open ProofBroker (FfiError pbCall roundtripIR propositionalSimplify definitionUnfolding
                  quotientElimination runPipeline decodeEnvelope PipelineConfig PassStep)
open ProofBroker.IR (IR ShellTerm normalize)
open ProofBroker.Trace (Entry Outcome Document)

def fail (msg : String) : IO α := do
  IO.eprintln s!"FAIL: {msg}"
  IO.Process.exit 1

def fixtures : List String := [
  "example1-lia-typeclass.json",
  "example2-function-composition.json",
  "example3-quotient-zmod.json"
]

def runRoundTrip (rootDir : System.FilePath) (fixture : String) : IO Unit := do
  let path := rootDir / "examples" / fixture
  let input ← IO.FS.readFile path
  let original ← match Json.parse input with
    | .ok j => pure j
    | .error e => fail s!"{fixture}: could not parse fixture: {e}"

  let ir ← match IR.fromJsonString input with
    | .ok ir => pure ir
    | .error e => fail s!"{fixture}: Lean IR.fromJsonString failed: {e}"

  let ir' ← match roundtripIR ir with
    | .ok ir' => pure ir'
    | .error e => fail s!"{fixture}: roundtripIR returned error: {repr e}"

  let reEncoded := IR.toJson ir'
  if normalize reEncoded == normalize original then
    IO.println s!"OK typed IR round-trip: {fixture} structurally identical after normalization"
  else
    fail s!"{fixture}: round-trip differs structurally\noriginal: {(normalize original).pretty 2}\nreEncoded: {(normalize reEncoded).pretty 2}"

def runJsonParseErrorPath : IO Unit := do
  match decodeEnvelope (pbCall "roundtrip_ir" "{not json") with
  | .ok _ => fail "expected error on lexical garbage, got ok"
  | .error (.jsonParseError _) =>
    IO.println "OK error propagation: malformed JSON surfaces as FfiError.jsonParseError"
  | .error e =>
    fail s!"expected FfiError.jsonParseError, got {repr e}"

def runUnknownMethodPath : IO Unit := do
  let envelopeStr := pbCall "does_not_exist" "{}"
  match decodeEnvelope envelopeStr with
  | .ok _ => fail "expected error on unknown method, got ok"
  | .error (.unknownMethod m) =>
    if m == "does_not_exist" then
      IO.println s!"OK dispatcher: unknown method surfaces as FfiError.unknownMethod \"{m}\""
    else
      fail s!"unknownMethod carried wrong name: {m}"
  | .error e =>
    fail s!"expected FfiError.unknownMethod, got {repr e}"

def runLeanCodecRejectsBadIr : IO Unit := do
  match IR.fromJsonString "{\"foo\":42}" with
  | .ok _ => fail "expected error decoding ill-formed IR, got ok"
  | .error msg =>
    IO.println s!"OK Lean codec: ill-formed IR rejected with: {msg}"

/-- Construct a minimal-scaffolding IR with a given goal shell. The
    schema's required fields are filled with trivial defaults; only
    `goal.shell` varies across cases. Used for end-to-end pass tests
    where the interesting structure is in the goal, not the
    surrounding metadata. -/
def mkTestIR (shell : ShellTerm) : IR :=
  {
    irVersion := "1.0",
    sourceSystem := { name := "test", version := "0.0" },
    tier := "goal",
    logicClassification := {
      order := "first_order",
      featuresUsed := [],
      firstOrderFragment := "FOL",
      decidableTheory := none
    },
    goal := { shell, payloads := none },
    context := {
      typeVars := [], freeVars := [], hypotheses := [], librarySlice := none
    },
    typeMetadata := [],
    definitionalMetadata := [],
    libraryProvenance := [],
    userDirectives := none
  }

def runPropositionalSimplifyApplied : IO Unit := do
  -- (True ∧ p) — should simplify to p with rule And_True_left.
  let ir := mkTestIR (.and_ (.const "True") (.var "p"))
  let (irOut, entry) ← match propositionalSimplify ir with
    | .ok pair => pure pair
    | .error e => fail s!"propositionalSimplify returned error: {repr e}"
  unless entry.pass == "propositional_simplification" do
    fail s!"unexpected pass name: {entry.pass}"
  unless entry.outcome == some .applied do
    fail s!"expected outcome=applied, got {repr entry.outcome}"
  match irOut.goal.shell with
  | .var "p" => pure ()
  | other => fail s!"goal not collapsed to (Var p), got {(ProofBroker.IR.ShellTerm.toJson other).compress}"
  -- Inspect inversion_data: should record exactly one
  -- {"rule":"And_True_left","site":"goal"}.
  let inv ← match entry.inversionData with
    | some j => pure j
    | none => fail "inversion_data missing"
  let simps ← match inv.getObjVal? "simplifications" with
    | .ok j => pure j
    | .error e => fail s!"missing simplifications: {e}"
  let arr ← match simps.getArr? with
    | .ok a => pure a
    | .error e => fail s!"simplifications not an array: {e}"
  unless arr.size == 1 do
    fail s!"expected 1 simplification, got {arr.size}"
  let firstRule := (arr[0]!.getObjValAs? String "rule").toOption.getD ""
  let firstSite := (arr[0]!.getObjValAs? String "site").toOption.getD ""
  unless firstRule == "And_True_left" do
    fail s!"expected rule=And_True_left, got {firstRule}"
  unless firstSite == "goal" do
    fail s!"expected site=goal, got {firstSite}"
  unless entry.beforeHash != entry.afterHash do
    fail "expected before_hash != after_hash on applied pass"
  IO.println s!"OK propositional_simplify: (True ∧ p) ↝ p, rule And_True_left at goal"

def runPropositionalSimplifyNoOp : IO Unit := do
  -- (Var p) has no rewritable structure: outcome=noOp, hashes equal.
  let ir := mkTestIR (.var "p")
  let (_, entry) ← match propositionalSimplify ir with
    | .ok pair => pure pair
    | .error e => fail s!"propositionalSimplify returned error: {repr e}"
  unless entry.outcome == some .noOp do
    fail s!"expected outcome=noOp, got {repr entry.outcome}"
  unless entry.beforeHash == entry.afterHash do
    fail "expected before_hash == after_hash on no-op"
  IO.println "OK propositional_simplify: no-op preserves hash and reports outcome=noOp"

/-- Exercise definition_unfolding on the example2 fixture. The
    fixture has user_directives.enable_definition_unfolding set to
    ["function_composition"] and a Function.comp entry in
    definitional_metadata, so the pass should report
    outcome=applied and emit at least one unfolded_symbols entry. -/
def runDefinitionUnfoldingOnFixture (rootDir : System.FilePath) : IO Unit := do
  let path := rootDir / "examples" / "example2-function-composition.json"
  let raw ← IO.FS.readFile path
  let ir ← match IR.fromJsonString raw with
    | .ok ir => pure ir
    | .error e => fail s!"could not parse example2 fixture: {e}"
  let (_, entry) ← match definitionUnfolding ir with
    | .ok pair => pure pair
    | .error e => fail s!"definitionUnfolding returned error: {repr e}"
  unless entry.pass == "definition_unfolding" do
    fail s!"unexpected pass name: {entry.pass}"
  unless entry.outcome == some .applied do
    fail s!"expected outcome=applied on Function.comp fixture, got {repr entry.outcome}"
  let inv ← match entry.inversionData with
    | some j => pure j
    | none => fail "inversion_data missing"
  let unfolded ← match inv.getObjVal? "unfolded_symbols" with
    | .ok j => pure j
    | .error e => fail s!"missing unfolded_symbols: {e}"
  let arr ← match unfolded.getArr? with
    | .ok a => pure a
    | .error e => fail s!"unfolded_symbols not an array: {e}"
  unless arr.size >= 1 do
    fail s!"expected at least 1 unfolded symbol, got {arr.size}"
  let firstSym := (arr[0]!.getObjValAs? String "symbol").toOption.getD ""
  let firstVia := (arr[0]!.getObjValAs? String "via").toOption.getD ""
  unless firstVia == "definitional_equation" do
    fail s!"expected via=definitional_equation, got {firstVia}"
  IO.println s!"OK definition_unfolding: example2 unfolded {arr.size} symbol(s) including {firstSym} via definitional_equation"

/-- Pass-skipping path: an IR without enable_definition_unfolding
    should land on outcome=skippedPreconditions, leaving the IR
    untouched. -/
def runDefinitionUnfoldingSkipped : IO Unit := do
  let ir := mkTestIR (.var "p")  -- mkTestIR sets userDirectives := none
  let (_, entry) ← match definitionUnfolding ir with
    | .ok pair => pure pair
    | .error e => fail s!"definitionUnfolding returned error: {repr e}"
  unless entry.outcome == some .skippedPreconditions do
    fail s!"expected outcome=skippedPreconditions, got {repr entry.outcome}"
  unless entry.beforeHash == entry.afterHash do
    fail "expected before_hash == after_hash on skipped pass"
  IO.println "OK definition_unfolding: empty config yields outcome=skippedPreconditions"

/-- End-to-end test of the pipeline driver: a two-pass run on
    `(True ∧ p)` should produce a Trace.Document with two entries
    (propositional_simplification, definition_unfolding) whose hashes
    chain (entries[0].after == entries[1].before) and bracket
    initial/final. -/
def runPipelineTwoPassChain : IO Unit := do
  let ir := mkTestIR (.and_ (.const "True") (.var "p"))
  let config : PipelineConfig := {
    pipeline := [
      { pass := "propositional_simplification" },
      { pass := "definition_unfolding" }
    ],
    stopOnFailure := false,
    timeoutPerPassMs := none
  }
  let (_, doc) ← match runPipeline ir config with
    | .ok pair => pure pair
    | .error e => fail s!"runPipeline returned error: {repr e}"
  unless doc.traceVersion == "1.0" do
    fail s!"unexpected trace_version: {doc.traceVersion}"
  unless doc.entries.length == 2 do
    fail s!"expected 2 entries, got {doc.entries.length}"
  let e0 := doc.entries[0]!
  let e1 := doc.entries[1]!
  unless e0.pass == "propositional_simplification" do
    fail s!"expected first pass propositional_simplification, got {e0.pass}"
  unless e1.pass == "definition_unfolding" do
    fail s!"expected second pass definition_unfolding, got {e1.pass}"
  unless e0.afterHash == e1.beforeHash do
    fail "hash chain broken: entries[0].after_hash != entries[1].before_hash"
  unless doc.initialIrHash == e0.beforeHash do
    fail "initial_ir_hash != entries[0].before_hash"
  unless doc.finalIrHash == e1.afterHash do
    fail "final_ir_hash != entries[1].after_hash"
  IO.println s!"OK pipeline: 2-pass chain produced linked Trace.Document with {doc.entries.length} entries"

/-- Default-pipeline path: calling `runPipeline` without a config
    should use `PipelineConfig.default` (propositional then unfolding,
    matching spec §5.4). The trace's configuration field round-trips
    the OCaml-side default. -/
def runPipelineDefault : IO Unit := do
  let ir := mkTestIR (.var "p")
  let (_, doc) ← match runPipeline ir with
    | .ok pair => pure pair
    | .error e => fail s!"runPipeline (default) error: {repr e}"
  unless doc.entries.length == 2 do
    fail s!"default pipeline should produce 2 entries, got {doc.entries.length}"
  unless doc.initialIrHash == doc.finalIrHash do
    fail "no-op IR through default pipeline should leave hashes equal"
  IO.println "OK pipeline: default config wires propositional + definition_unfolding"

/-- Stop-on-failure path: an unknown pass at position 0 with
    `stopOnFailure := true` halts the chain after a single
    `Outcome.failed` entry. -/
def runPipelineStopOnFailure : IO Unit := do
  let ir := mkTestIR (.var "p")
  let config : PipelineConfig := {
    pipeline := [
      { pass := "no_such_pass" },
      { pass := "propositional_simplification" }
    ],
    stopOnFailure := true,
    timeoutPerPassMs := none
  }
  let (_, doc) ← match runPipeline ir config with
    | .ok pair => pure pair
    | .error e => fail s!"runPipeline returned error: {repr e}"
  unless doc.entries.length == 1 do
    fail s!"stop_on_failure should halt after 1 entry, got {doc.entries.length}"
  let e := doc.entries[0]!
  unless e.outcome == some .failed do
    fail s!"expected outcome=failed for unknown pass, got {repr e.outcome}"
  IO.println "OK pipeline: stop_on_failure halts after Failed entry"

/-- Read example3 with `enable_quotient_elimination := true` patched
    into `userDirectives`, then call `quotientElimination`. Validates
    that the pass lands on `Outcome.applied` and that all three
    inversion-data sections (eliminations, equality_reductions,
    lifted_unfoldings) carry at least one entry. -/
def runQuotientEliminationOnFixture (rootDir : System.FilePath) : IO Unit := do
  let path := rootDir / "examples" / "example3-quotient-zmod.json"
  let raw ← IO.FS.readFile path
  let irBase ← match IR.fromJsonString raw with
    | .ok ir => pure ir
    | .error e => fail s!"could not parse example3 fixture: {e}"
  let ud : ProofBroker.IR.UserDirectives := {
    preferredBackend := none,
    tierPreference := none,
    rewriterPreferences := some {
      enableQuotientElimination := some true,
      enableDefinitionUnfolding := none,
      disablePasses := none
    },
    budget := none
  }
  let ir : IR := { irBase with userDirectives := some ud }
  let (_, entry) ← match quotientElimination ir with
    | .ok pair => pure pair
    | .error e => fail s!"quotientElimination returned error: {repr e}"
  unless entry.pass == "quotient_elimination" do
    fail s!"unexpected pass name: {entry.pass}"
  unless entry.outcome == some .applied do
    fail s!"expected outcome=applied on example3, got {repr entry.outcome}"
  let inv ← match entry.inversionData with
    | some j => pure j
    | none => fail "inversion_data missing"
  let countSection (key : String) : IO Nat := do
    match inv.getObjVal? key with
    | .ok j => match j.getArr? with
      | .ok arr => pure arr.size
      | .error e => fail s!"{key} not an array: {e}"
    | .error e => fail s!"missing {key}: {e}"
  let elims ← countSection "eliminations"
  let lifted ← countSection "lifted_unfoldings"
  let eqs ← countSection "equality_reductions"
  unless elims >= 1 ∧ lifted >= 1 ∧ eqs >= 1 do
    fail s!"expected each inversion section to be non-empty, got eliminations={elims}, lifted_unfoldings={lifted}, equality_reductions={eqs}"
  unless entry.beforeHash != entry.afterHash do
    fail "expected before_hash != after_hash on applied pass"
  IO.println s!"OK quotient_elimination: example3 yields outcome=applied with {elims} elim(s), {lifted} lifted unfolding(s), {eqs} eq reduction(s)"

/-- Without the flag set, the pass must report
    `Outcome.skippedPreconditions` and leave the IR untouched. -/
def runQuotientEliminationSkipped : IO Unit := do
  let ir := mkTestIR (.var "p")  -- mkTestIR sets userDirectives := none
  let (_, entry) ← match quotientElimination ir with
    | .ok pair => pure pair
    | .error e => fail s!"quotientElimination returned error: {repr e}"
  unless entry.outcome == some .skippedPreconditions do
    fail s!"expected outcome=skippedPreconditions, got {repr entry.outcome}"
  unless entry.beforeHash == entry.afterHash do
    fail "expected before_hash == after_hash on skipped pass"
  IO.println "OK quotient_elimination: missing flag yields outcome=skippedPreconditions"

def main : IO Unit := do
  let cwd ← IO.currentDir
  let rootDir := cwd / ".."
  for fixture in fixtures do
    runRoundTrip rootDir fixture
  runJsonParseErrorPath
  runUnknownMethodPath
  runLeanCodecRejectsBadIr
  runPropositionalSimplifyApplied
  runPropositionalSimplifyNoOp
  runDefinitionUnfoldingOnFixture rootDir
  runDefinitionUnfoldingSkipped
  runQuotientEliminationOnFixture rootDir
  runQuotientEliminationSkipped
  runPipelineTwoPassChain
  runPipelineDefault
  runPipelineStopOnFailure

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
                  quotientElimination runPipeline runMatchAdapters
                  runVerifyCertificate runDispatchToAdapter runDispatchBroker
                  decodeEnvelope PipelineConfig PassStep MatchReason MatchResults
                  CertReason CertVerification
                  DispatchResult DispatchFailure
                  BrokerResult Attempt AttemptOutcome)
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

/-- Capability matching against the cvc5 manifest fixture. example1
    (LIA goal, primitive constructions) should match; example3
    (quotient construction) should reject as
    `typeConstructionNotSupported`. Validates the FFI surface of
    `match_adapters` and the typed Lean rejection-reason ADT. -/
def runMatchAdaptersOnFixtures (rootDir : System.FilePath) : IO Unit := do
  let manifestRaw ← IO.FS.readFile (rootDir / "examples" / "manifest-cvc5.json")
  let manifestJ ← match Json.parse manifestRaw with
    | .ok j => pure j
    | .error e => fail s!"could not parse cvc5 manifest: {e}"
  let loadIr (name : String) : IO IR := do
    let raw ← IO.FS.readFile (rootDir / "examples" / name)
    match IR.fromJsonString raw with
    | .ok ir => pure ir
    | .error e => fail s!"{name}: parse error: {e}"
  let ir1 ← loadIr "example1-lia-typeclass.json"
  let res1 ← match runMatchAdapters ir1 [manifestJ] with
    | .ok r => pure r
    | .error e => fail s!"runMatchAdapters on example1: {repr e}"
  unless res1.matchedAdapters == ["cvc5"] do
    fail s!"expected example1 to match cvc5; got matches={res1.matchedAdapters}"
  unless res1.rejections.length == 0 do
    fail s!"expected no rejections on example1; got {res1.rejections.length}"
  IO.println "OK match_adapters: example1 matches cvc5"
  let ir3 ← loadIr "example3-quotient-zmod.json"
  let res3 ← match runMatchAdapters ir3 [manifestJ] with
    | .ok r => pure r
    | .error e => fail s!"runMatchAdapters on example3: {repr e}"
  unless res3.matchedAdapters.length == 0 do
    fail s!"expected no matches on example3; got {res3.matchedAdapters}"
  unless res3.rejections.length == 1 do
    fail s!"expected 1 rejection on example3; got {res3.rejections.length}"
  match res3.rejections with
  | [(adapter, .typeConstructionNotSupported _)] =>
    unless adapter == "cvc5" do fail s!"unexpected rejected adapter: {adapter}"
    IO.println "OK match_adapters: example3 rejected as typeConstructionNotSupported"
  | other =>
    fail s!"expected single typeConstructionNotSupported rejection; got {other.length} entries"

/-- Build a synthetic certificate JSON addressing `ir`. The hash
    is supplied by the caller (typically harvested from an empty
    `runPipeline` invocation, which exposes the canonical IR hash
    via `Trace.Document.initialIrHash`). The cert is Tier 1 / Farkas
    with a single dummy coefficient — enough structure to exercise
    the envelope verifier; the actual Farkas arithmetic check is
    deferred per OCaml-side `Verifier` notes. -/
def buildSyntheticTier1Cert (irHash : String) (goal : Json)
    (overrideHash : Option String := none) : Json :=
  let cert_ctx_hash := overrideHash.getD irHash
  Json.mkObj [
    ("cert_version", .str "1.0"),
    ("tier", .num 1),
    ("format", .str "farkas"),
    ("goal", goal),
    ("dispatch_context_hash", .str cert_ctx_hash),
    ("rewrite_trace_hash", .str s!"sha256:{String.ofList (List.replicate 64 '0')}"),
    ("backend", Json.mkObj [
      ("name", .str "synthetic"),
      ("version", .str "0.0"),
      ("config_hash", .str s!"sha256:{String.ofList (List.replicate 64 '0')}")
    ]),
    ("resources", Json.mkObj [
      ("wall_time_ms", .num 1),
      ("memory_peak_kb", .num 1)
    ]),
    ("refinement_record", Json.mkObj [
      ("adapter", .str "synthetic"),
      ("adapter_version", .str "0.0"),
      ("specializations", Json.arr #[]),
      ("fragment", .str "FOL")
    ]),
    ("payload", Json.mkObj [
      ("witness_kind", .str "farkas"),
      ("witness_data", Json.mkObj [
        ("coefficients", Json.arr #[
          Json.mkObj [
            ("hypothesis", .str "h0"),
            ("coefficient", .str "1")
          ]
        ])
      ]),
      ("checking_recipe", .str "lean.farkas_check")
    ])
  ]

/-- End-to-end certificate verification across the FFI: build a
    synthetic IR, harvest its canonical hash via an empty pipeline
    run, build a cert against that hash, verify it. The synthetic
    cert references a hypothesis `h0` not present in the IR, so the
    Farkas verifier rejects with `farkasUnknownHypothesis` after
    envelope checks pass — exercising both that the FFI surface
    propagates Farkas-tier failures and that the typed Lean ADT
    has the matching constructor. Hash mutation then surfaces
    `hashMismatch` from the envelope layer, before Farkas runs. -/
def runVerifyCertificateFlow : IO Unit := do
  let ir := mkTestIR (.var "p")
  let emptyConfig : PipelineConfig := {
    pipeline := [], stopOnFailure := false, timeoutPerPassMs := none
  }
  let (_, doc) ← match runPipeline ir emptyConfig with
    | .ok pair => pure pair
    | .error e => fail s!"pipeline run for hash failed: {repr e}"
  let irHash := doc.initialIrHash
  let goalJson := ProofBroker.IR.Goal.toJson ir.goal
  let goodCert := buildSyntheticTier1Cert irHash goalJson
  let res ← match runVerifyCertificate goodCert ir with
    | .ok r => pure r
    | .error e => fail s!"runVerifyCertificate (good): {repr e}"
  if res.ok then
    fail s!"expected ok=false on h0-absent IR; reason={repr res.reason}"
  match res.reason with
  | .farkasUnknownHypothesis _ =>
    IO.println "OK verify_certificate: envelope passes, Farkas rejects unknown hypothesis"
  | other =>
    fail s!"expected farkasUnknownHypothesis, got {repr other}"
  let badHash := s!"sha256:{String.ofList (List.replicate 64 '1')}"
  let badCert := buildSyntheticTier1Cert irHash goalJson (overrideHash := some badHash)
  let res2 ← match runVerifyCertificate badCert ir with
    | .ok r => pure r
    | .error e => fail s!"runVerifyCertificate (bad): {repr e}"
  if res2.ok then
    fail "expected ok=false on hash mismatch"
  match res2.reason with
  | .hashMismatch _ =>
    IO.println "OK verify_certificate: hash_mismatch surfaces typed reason"
  | other =>
    fail s!"expected hashMismatch, got {repr other}"

/-- End-to-end Tier 1 Farkas verification across the FFI on a real
    LIA goal. Build an IR with hypotheses [h1: n + m = 10,
    h3: 0 <= m] and goal [n <= 10], then a Farkas certificate with
    coefficients [h1=1, h3=1, neg_goal=1] — the same structure as
    the spec's worked example (cert-example1-tier1-farkas.json).
    The weighted sum simplifies to constant 1 over the LIA +1 trick
    on `neg_goal`, so the verifier returns `verifiedFarkas`. Then
    flip the certificate to coefficients [h1=1] alone and confirm
    the verifier rejects with `farkasNotContradictory`. -/
def runFarkasVerificationFlow : IO Unit := do
  -- IR: n + m = 10, 0 <= m, ⊢ n <= 10
  let n : ShellTerm := .var "n"
  let m : ShellTerm := .var "m"
  let ten : ShellTerm := .numLit "10" "Int"
  let zero : ShellTerm := .numLit "0" "Int"
  let n_plus_m : ShellTerm := .app "Int.add" [] [n, m]
  let h1 : ShellTerm := .eq "Int" n_plus_m ten
  let h3 : ShellTerm := .app "LE.le" [] [zero, m]
  let goal : ShellTerm := .app "LE.le" [] [n, ten]
  let irBase := mkTestIR goal
  let ir : IR := { irBase with
    context := {
      typeVars := [], freeVars := [
        { name := "n", ty := "Int" },
        { name := "m", ty := "Int" }
      ],
      hypotheses := [
        { name := "h1", shell := h1 },
        { name := "h3", shell := h3 }
      ],
      librarySlice := none
    }
  }
  let emptyConfig : PipelineConfig := {
    pipeline := [], stopOnFailure := false, timeoutPerPassMs := none
  }
  let (_, doc) ← match runPipeline ir emptyConfig with
    | .ok pair => pure pair
    | .error e => fail s!"pipeline run for hash failed: {repr e}"
  let irHash := doc.initialIrHash
  let goalJson := ProofBroker.IR.Goal.toJson ir.goal
  let mkCert (coefs : Array Json) : Json :=
    Json.mkObj [
      ("cert_version", .str "1.0"),
      ("tier", .num 1),
      ("format", .str "farkas"),
      ("goal", goalJson),
      ("dispatch_context_hash", .str irHash),
      ("rewrite_trace_hash", .str s!"sha256:{String.ofList (List.replicate 64 '0')}"),
      ("backend", Json.mkObj [
        ("name", .str "synthetic"),
        ("version", .str "0.0"),
        ("config_hash", .str s!"sha256:{String.ofList (List.replicate 64 '0')}")
      ]),
      ("resources", Json.mkObj [
        ("wall_time_ms", .num 1),
        ("memory_peak_kb", .num 1)
      ]),
      ("refinement_record", Json.mkObj [
        ("adapter", .str "synthetic"),
        ("adapter_version", .str "0.0"),
        ("specializations", Json.arr #[]),
        ("fragment", .str "LIA")
      ]),
      ("payload", Json.mkObj [
        ("witness_kind", .str "farkas"),
        ("witness_data", Json.mkObj [("coefficients", Json.arr coefs)]),
        ("checking_recipe", .str "lean.farkas_check")
      ])
    ]
  let coef (h : String) (c : String) : Json :=
    Json.mkObj [("hypothesis", .str h), ("coefficient", .str c)]
  -- Good cert: h1=1, h3=1, neg_goal=1 ⇒ residual = 1 ⇒ verifiedFarkas
  let goodCert := mkCert #[coef "h1" "1", coef "h3" "1", coef "neg_goal" "1"]
  let res ← match runVerifyCertificate goodCert ir with
    | .ok r => pure r
    | .error e => fail s!"runVerifyCertificate (Farkas good): {repr e}"
  unless res.ok do
    fail s!"expected ok=true on valid Farkas cert; reason={repr res.reason}"
  match res.reason with
  | .verifiedFarkas =>
    IO.println "OK verify_certificate: Tier 1 Farkas arithmetic verified end-to-end"
  | other =>
    fail s!"expected verifiedFarkas, got {repr other}"
  -- Bad cert: only h1=1 ⇒ residual = n + m - 10 (not constant) ⇒ farkasNotContradictory
  let badCert := mkCert #[coef "h1" "1"]
  let res2 ← match runVerifyCertificate badCert ir with
    | .ok r => pure r
    | .error e => fail s!"runVerifyCertificate (Farkas bad): {repr e}"
  if res2.ok then
    fail s!"expected ok=false on insufficient Farkas cert; reason={repr res2.reason}"
  match res2.reason with
  | .farkasNotContradictory _ =>
    IO.println "OK verify_certificate: Farkas non-contradictory residual surfaced"
  | other =>
    fail s!"expected farkasNotContradictory, got {repr other}"

/-- Probe whether cvc4 is available; the dispatch flow needs the
    binary on PATH and we want CI without cvc4 to stay green. -/
def cvc4Available : IO Bool := do
  let exit ← IO.Process.run {
    cmd := "sh", args := #["-c", "which cvc4 > /dev/null 2>&1"], stdin := .null
  } |>.toBaseIO
  return exit.toOption.isSome

/-- End-to-end Phase 2.1 cvc4 dispatch across the FFI: build the
    example1 LIA IR, hand it to `runDispatchToAdapter "cvc4" ...`,
    expect a Tier 0 oracle cert addressing the same IR. Then feed
    the cert back to `runVerifyCertificate` and confirm the
    envelope verifies (with `tierCheckDeferred` on Tier 0). Then
    a satisfiable goal returns `.failed .satReturned`. Skipped
    cleanly if cvc4 isn't on PATH. -/
def runDispatchToCvc4Flow : IO Unit := do
  unless ← cvc4Available do
    IO.println "[skip] cvc4 not on PATH; skipping dispatch flow"
    return
  let n : ShellTerm := .var "n"
  let m : ShellTerm := .var "m"
  let ten : ShellTerm := .numLit "10" "Int"
  let zero : ShellTerm := .numLit "0" "Int"
  let n_plus_m : ShellTerm := .app "Int.add" [] [n, m]
  let h1 : ShellTerm := .eq "Int" n_plus_m ten
  let h3 : ShellTerm := .app "LE.le" [] [zero, m]
  let goal : ShellTerm := .app "LE.le" [] [n, ten]
  let irBase := mkTestIR goal
  let ir : IR := { irBase with
    context := {
      typeVars := [], freeVars := [
        { name := "n", ty := "Int" },
        { name := "m", ty := "Int" }
      ],
      hypotheses := [
        { name := "h1", shell := h1 },
        { name := "h3", shell := h3 }
      ],
      librarySlice := none
    }
  }
  let res ← match runDispatchToAdapter "cvc4" ir with
    | .ok r => pure r
    | .error e => fail s!"runDispatchToAdapter (provable goal): {repr e}"
  let certJ ← match res with
    | .cert j => pure j
    | .failed f => fail s!"expected .cert on provable goal, got .failed {repr f}"
  let tier := (certJ.getObjValAs? Int "tier").toOption.getD (-1)
  unless tier == 0 do
    fail s!"expected tier=0, got {tier}"
  let backend := (certJ.getObjVal? "backend" |>.bind (·.getObjValAs? String "name")).toOption.getD ""
  unless backend == "cvc4" do
    fail s!"expected backend=cvc4, got {backend}"
  IO.println "OK dispatch_to_adapter: cvc4 minted Tier 0 oracle cert on provable LIA goal"
  -- Round-trip the cert through verify_certificate to confirm the
  -- envelope addresses our IR.
  let verif ← match runVerifyCertificate certJ ir with
    | .ok v => pure v
    | .error e => fail s!"runVerifyCertificate on minted cert: {repr e}"
  unless verif.ok do
    fail s!"expected ok=true on minted cert verification; reason={repr verif.reason}"
  match verif.reason with
  | .tierCheckDeferred _ =>
    IO.println "OK verify_certificate: Tier 0 cvc4 cert envelope-verifies (tier soundness deferred)"
  | other =>
    fail s!"expected tierCheckDeferred, got {repr other}"
  -- Satisfiable goal: no hypotheses, ⊢ n <= 10. n=11 satisfies ¬G.
  let irOpen : IR := { mkTestIR goal with
    context := {
      typeVars := [], freeVars := [{ name := "n", ty := "Int" }],
      hypotheses := [], librarySlice := none
    }
  }
  let res2 ← match runDispatchToAdapter "cvc4" irOpen with
    | .ok r => pure r
    | .error e => fail s!"runDispatchToAdapter (sat goal): {repr e}"
  match res2 with
  | .failed .satReturned =>
    IO.println "OK dispatch_to_adapter: cvc4 reports satReturned on non-provable goal"
  | other => fail s!"expected .failed .satReturned, got {repr other}"

/-- End-to-end refinement-then-dispatch on the typeclass-shaped
    example1 fixture: the IR has `alpha` as a type variable, full
    `type_metadata` (with the LIA embedding tag) and
    `definitional_metadata` (with HAdd.hAdd / LE.le specialization
    targets). The broker should refine to LIA, dispatch to cvc4,
    and return a Tier 0 oracle cert whose `refinement_record`
    enumerates the type and method specializations applied. -/
def runRefinementDispatchFlow (rootDir : System.FilePath) : IO Unit := do
  unless ← cvc4Available do
    IO.println "[skip] cvc4 not on PATH; skipping refinement+dispatch flow"
    return
  let path := rootDir / "examples" / "example1-lia-typeclass.json"
  let raw ← IO.FS.readFile path
  let ir ← match IR.fromJsonString raw with
    | .ok ir => pure ir
    | .error e => fail s!"could not parse example1: {e}"
  let res ← match runDispatchToAdapter "cvc4" ir with
    | .ok r => pure r
    | .error e => fail s!"runDispatchToAdapter (typeclass IR): {repr e}"
  let certJ ← match res with
    | .cert j => pure j
    | .failed f => fail s!"expected .cert on typeclass IR, got .failed {repr f}"
  let rrJ ← match certJ.getObjVal? "refinement_record" with
    | .ok j => pure j
    | .error e => fail s!"missing refinement_record: {e}"
  let specsJ ← match rrJ.getObjVal? "specializations" with
    | .ok j => pure j
    | .error e => fail s!"missing specializations: {e}"
  let arr ← match specsJ.getArr? with
    | .ok a => pure a
    | .error e => fail s!"specializations not array: {e}"
  let kinds := arr.toList.filterMap fun s =>
    (s.getObjValAs? String "kind").toOption
  let sources := arr.toList.filterMap fun s =>
    (s.getObjValAs? String "source").toOption
  unless kinds.contains "type_specialization" do
    fail s!"expected type_specialization in cert; kinds={kinds}"
  unless kinds.contains "method_specialization" do
    fail s!"expected method_specialization in cert; kinds={kinds}"
  unless sources.contains "alpha" do
    fail s!"expected alpha in specializations; sources={sources}"
  unless sources.contains "HAdd.hAdd" || sources.contains "LE.le" do
    fail s!"expected HAdd.hAdd or LE.le; sources={sources}"
  IO.println s!"OK refinement+dispatch: example1 typeclass IR refined to LIA, cvc4 minted cert with {arr.size} refinement specs"

/-- End-to-end multi-adapter dispatch (spec §7). Hands the broker
    the typeclass-shaped example1 IR plus two manifests in priority
    order: a fake BV-only manifest first (capability mismatch on
    LIA), then the real cvc4 manifest. Expectation: bv-fake is
    skipped via logicOutOfFragment, cvc4 mints the cert, attempts
    list reflects both outcomes in order. -/
def runDispatchBrokerFlow (rootDir : System.FilePath) : IO Unit := do
  unless ← cvc4Available do
    IO.println "[skip] cvc4 not on PATH; skipping broker dispatch flow"
    return
  let cvc4ManifestRaw ← IO.FS.readFile (rootDir / "examples" / "manifest-cvc4.json")
  let cvc4Manifest ← match Json.parse cvc4ManifestRaw with
    | .ok j => pure j
    | .error e => fail s!"could not parse cvc4 manifest: {e}"
  let bvFakeManifest := Json.mkObj [
    ("manifest_version", .str "1.0"),
    ("adapter", .str "bv-fake"),
    ("adapter_version", .str "0.0"),
    ("logic_fragments", Json.arr #[.str "BV"]),
    ("type_constructions", Json.arr #[.str "primitive"]),
    ("max_order", .str "first_order"),
    ("tiers_produced", Json.arr #[.num 0])
  ]
  let path := rootDir / "examples" / "example1-lia-typeclass.json"
  let raw ← IO.FS.readFile path
  let ir ← match IR.fromJsonString raw with
    | .ok ir => pure ir
    | .error e => fail s!"could not parse example1: {e}"
  let r ← match runDispatchBroker ir [bvFakeManifest, cvc4Manifest] with
    | .ok r => pure r
    | .error e => fail s!"runDispatchBroker error: {repr e}"
  unless r.cert.isSome do
    fail s!"expected cert minted; attempts={r.attempts.length}"
  unless r.attempts.length == 2 do
    fail s!"expected 2 attempts, got {r.attempts.length}"
  let a0 := r.attempts[0]!
  let a1 := r.attempts[1]!
  unless a0.adapter == "bv-fake" do
    fail s!"expected first attempt bv-fake, got {a0.adapter}"
  -- The example1 fixture has first_order_fragment="none", so the
  -- fragment check is skipped (see Capability_match notes). The
  -- type-construction check does the work: alpha lives in
  -- context.type_vars, requiring [type_variable_via_specialization]
  -- support — which bv-fake doesn't have.
  match a0.outcome with
  | .skipped (.typeConstructionNotSupported _) => pure ()
  | other => fail s!"expected skipped typeConstructionNotSupported for bv-fake, got {repr other}"
  unless a1.adapter == "cvc4" do
    fail s!"expected second attempt cvc4, got {a1.adapter}"
  match a1.outcome with
  | .succeeded => pure ()
  | other => fail s!"expected succeeded for cvc4, got {repr other}"
  IO.println "OK dispatch_broker: bv-fake skipped on type construction, cvc4 minted cert, attempts logged in order"

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
  runMatchAdaptersOnFixtures rootDir
  runVerifyCertificateFlow
  runFarkasVerificationFlow
  runDispatchToCvc4Flow
  runRefinementDispatchFlow rootDir
  runDispatchBrokerFlow rootDir

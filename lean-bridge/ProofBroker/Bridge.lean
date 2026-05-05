/-
Lean-side surface for the proof_broker FFI boundary.

One low-level extern (`pbCall`) routes every dispatch through the
generic `pb_ffi_call` C entry point per `sdk/FFI_CONVENTIONS.md`.
Typed wrappers (`roundtripIR`, etc.) sit on top, decoding the
envelope into a typed `Except FfiError α` so callers never
hand-parse status/kind themselves.

Adding a new op: register it in `sdk/ffi/proof_broker_ffi.ml` under
a fresh method name and add a `def myOp ... := decodeEnvelope (pbCall
"my_op" input)` here. Neither the C ABI nor the C glue grows.
-/

import Lean.Data.Json
import ProofBroker.IR
import ProofBroker.Trace

namespace ProofBroker

open Lean (Json)
open ProofBroker.IR (IR)
open ProofBroker.Trace (Entry Document)

/-- One step in a pipeline configuration (spec v1.0 §5.3). The
    `config` field is JSON pass-through; the schema is permissive. -/
structure PassStep where
  pass : String
  config : Option Json := none
deriving Inhabited

def PassStep.toJson (s : PassStep) : Json :=
  let fields : List (String × Json) := [("pass", .str s.pass)]
  let fields := match s.config with
    | none => fields
    | some c => fields ++ [("config", c)]
  Json.mkObj fields

/-- Pipeline configuration mirroring `sdk/lib/pipeline.ml`'s `config`. -/
structure PipelineConfig where
  pipeline : List PassStep
  stopOnFailure : Bool := false
  timeoutPerPassMs : Option Int := none
deriving Inhabited

def PipelineConfig.toJson (c : PipelineConfig) : Json :=
  let fields : List (String × Json) := [
    ("pipeline", Json.arr (c.pipeline.map PassStep.toJson).toArray),
    ("stop_on_failure", .bool c.stopOnFailure)
  ]
  let fields := match c.timeoutPerPassMs with
    | none => fields
    | some t => fields ++ [("timeout_per_pass_ms", .num t)]
  Json.mkObj fields

/-- Default pipeline (spec v1.0 §5.4): propositional simplification
    then definition unfolding. Matches OCaml `Pipeline.default_config`. -/
def PipelineConfig.default : PipelineConfig := {
  pipeline := [
    { pass := "propositional_simplification" },
    { pass := "definition_unfolding" }
  ],
  stopOnFailure := false,
  timeoutPerPassMs := none
}

/-- Typed FFI error matching the `kind` taxonomy in
    `sdk/FFI_CONVENTIONS.md`. The `.other` constructor is the
    forward-compatibility escape hatch: envelope kinds added on the
    OCaml side that this Lean version doesn't know about decode into
    `.other` rather than rejecting the envelope, so a newer Lean ↔
    older shim (or vice versa) still surfaces actionable diagnostics. -/
inductive FfiError where
  | jsonParseError (message : String)
  | decodeError (message : String) (site : Option String)
  | unknownMethod (method : String)
  | shimFailure (rc : Int) (message : String)
  | other (kind : String) (message : String)
deriving Repr

/-- Low-level extern: pass a method name and a JSON input string,
    receive an FFI envelope JSON string. Always returns a parseable
    envelope; per-method success/failure is encoded in the envelope's
    `status` and `error.kind` fields. The C glue layer synthesizes a
    `kind="shim_failure"` envelope on its own (sub-OCaml) failures so
    the contract that this function returns a valid envelope holds
    even when the runtime can't be reached. -/
@[extern "pb_lean_call"]
opaque pbCall (method : @& String) (input : @& String) : String

/-- Decode an FFI envelope string into a typed result. On `status=ok`,
    returns the payload as `Json`; on `status=error`, returns the
    typed `FfiError` matching the envelope's `kind`.

    Envelopes that fail to parse, or that have a malformed shape, fall
    through to `FfiError.other "envelope_parse_error"` — this is the
    failure mode where the contract above (always-parseable envelope)
    has been violated, and is treated as a genuine shim bug rather
    than a normal error path. -/
def decodeEnvelope (envelopeStr : String) : Except FfiError Json := do
  let envelope ← match Json.parse envelopeStr with
    | .ok j => pure j
    | .error e => throw (.other "envelope_parse_error" e)
  match envelope.getObjValAs? String "status" with
  | .ok "ok" =>
    match envelope.getObjVal? "payload" with
    | .ok p => pure p
    | .error e => throw (.other "envelope_parse_error" s!"missing payload: {e}")
  | .ok "error" =>
    let errObj ← match envelope.getObjVal? "error" with
      | .ok j => pure j
      | .error e => throw (.other "envelope_parse_error" s!"missing error: {e}")
    let kind ← match errObj.getObjValAs? String "kind" with
      | .ok k => pure k
      | .error e => throw (.other "envelope_parse_error" s!"missing error.kind: {e}")
    let message := (errObj.getObjValAs? String "message").toOption.getD ""
    throw <| match kind with
      | "json_parse_error" => .jsonParseError message
      | "decode_error" =>
        let site := (errObj.getObjValAs? String "site").toOption
        .decodeError message site
      | "unknown_method" => .unknownMethod message
      | "shim_failure" =>
        let rc := (errObj.getObjValAs? Int "rc").toOption.getD 0
        .shimFailure rc message
      | k => .other k message
  | .ok status => throw (.other "envelope_parse_error" s!"unexpected status: {status}")
  | .error e => throw (.other "envelope_parse_error" s!"missing status: {e}")

/-- Round-trip a typed IR document through OCaml's `Codec.of_json`
    and `Codec.to_json`. Serializes the IR, ships it through `pbCall`,
    decodes the envelope, and re-decodes the payload back into a
    typed IR. Codec failures on either end surface as
    `FfiError.decodeError` so callers see a single uniform error
    surface for both transport and shape failures.

    For raw-JSON callers (debugging, ops that don't have a typed
    Lean ADT yet), drop down one level: `decodeEnvelope (pbCall
    "roundtrip_ir" str)` returns the payload as `Json`. -/
def roundtripIR (ir : IR) : Except FfiError IR := do
  let inputStr := (ProofBroker.IR.IR.toJson ir).compress
  let payload ← decodeEnvelope (pbCall "roundtrip_ir" inputStr)
  match ProofBroker.IR.IR.fromJson? payload with
  | .ok ir' => .ok ir'
  | .error msg =>
    .error (.decodeError s!"failed to decode round-trip payload: {msg}" none)

/-- Decode a multi-return payload of shape
    `{"ir": <IR>, "trace_entry": <TraceEntry>}` per FFI_CONVENTIONS.md
    §Multi-return envelope. Both fields are accessed by name; new
    optional fields land non-breakingly. -/
private def decodeIrAndTrace (payload : Json) : Except FfiError (IR × Entry) := do
  let irJ ← match payload.getObjVal? "ir" with
    | .ok v => pure v
    | .error _ => .error (.decodeError "missing 'ir' in payload" none)
  let traceJ ← match payload.getObjVal? "trace_entry" with
    | .ok v => pure v
    | .error _ => .error (.decodeError "missing 'trace_entry' in payload" none)
  let ir ← match ProofBroker.IR.IR.fromJson? irJ with
    | .ok ir => pure ir
    | .error e => .error (.decodeError s!"decoding 'ir': {e}" none)
  let entry ← match Entry.fromJson? traceJ with
    | .ok e => pure e
    | .error e => .error (.decodeError s!"decoding 'trace_entry': {e}" none)
  return (ir, entry)

/-- Run the propositional-simplification pass on `ir`. Returns the
    rewritten IR paired with a trace entry that records each rule
    applied (in `inversion_data.simplifications`). The trace's
    `outcome` is `.applied` when at least one rule fired and `.noOp`
    otherwise. -/
def propositionalSimplify (ir : IR) : Except FfiError (IR × Entry) := do
  let inputStr := (ProofBroker.IR.IR.toJson ir).compress
  let payload ← decodeEnvelope (pbCall "propositional_simplify" inputStr)
  decodeIrAndTrace payload

/-- Run the definition-unfolding pass on `ir`. Configuration is read
    from `ir.userDirectives.rewriterPreferences.enableDefinitionUnfolding`
    (a list of concept_tags); symbols whose definitional_metadata
    declares a matching `concept_tag` are unfolded against their
    `definitional_equation`. Trace's `outcome` is `.skippedPreconditions`
    when the config list is empty, `.applied` when at least one symbol
    was unfolded, `.noOp` otherwise. -/
def definitionUnfolding (ir : IR) : Except FfiError (IR × Entry) := do
  let inputStr := (ProofBroker.IR.IR.toJson ir).compress
  let payload ← decodeEnvelope (pbCall "definition_unfolding" inputStr)
  decodeIrAndTrace payload

/-- Run the quotient-elimination pass on `ir`. Configuration is read
    from `ir.userDirectives.rewriterPreferences.enableQuotientElimination`
    (a `Bool`). When the flag is missing or `false`, the trace's
    `outcome` is `.skippedPreconditions`. When set, the pass rewrites:
    * free vars and binders of quotient type → underlying type,
    * `Eq` at a quotient type → applied equivalence relation,
    * `App` of a `lifted_to_quotient` symbol → underlying function.
    Inversion data populates three sections — `eliminations`,
    `equality_reductions`, `lifted_unfoldings` — that the lifting
    layer consults to rewrap the result in `Quot.ind`/`Quot.sound`. -/
def quotientElimination (ir : IR) : Except FfiError (IR × Entry) := do
  let inputStr := (ProofBroker.IR.IR.toJson ir).compress
  let payload ← decodeEnvelope (pbCall "quotient_elimination" inputStr)
  decodeIrAndTrace payload

/-- Decode the pipeline-payload shape `{"ir": <IR>, "trace": <Document>}`
    as defined in `sdk/lib/pipeline.ml`. -/
private def decodeIrAndTraceDocument (payload : Json) : Except FfiError (IR × Document) := do
  let irJ ← match payload.getObjVal? "ir" with
    | .ok v => pure v
    | .error _ => .error (.decodeError "missing 'ir' in payload" none)
  let traceJ ← match payload.getObjVal? "trace" with
    | .ok v => pure v
    | .error _ => .error (.decodeError "missing 'trace' in payload" none)
  let ir ← match ProofBroker.IR.IR.fromJson? irJ with
    | .ok ir => pure ir
    | .error e => .error (.decodeError s!"decoding 'ir': {e}" none)
  let doc ← match Document.fromJson? traceJ with
    | .ok d => pure d
    | .error e => .error (.decodeError s!"decoding 'trace': {e}" none)
  return (ir, doc)

/-- Run a configured pipeline of rewriter passes. Returns the final
    rewritten IR paired with a `Trace.Document` whose `entries` records
    one entry per attempted pass, with `initial_ir_hash` and
    `final_ir_hash` bracketing the chain. Failures inside a pass
    surface as `Outcome.failed` entries; `stopOnFailure := true`
    halts the chain after a failure, otherwise the next pass runs on
    the pre-failure IR. -/
def runPipeline (ir : IR) (config : PipelineConfig := PipelineConfig.default)
    : Except FfiError (IR × Document) := do
  let input := Json.mkObj [
    ("ir", ProofBroker.IR.IR.toJson ir),
    ("config", PipelineConfig.toJson config)
  ]
  let payload ← decodeEnvelope (pbCall "run_pipeline" input.compress)
  decodeIrAndTraceDocument payload

/-- Capability-matching reason. Mirrors OCaml's `Capability_match.reason`
    via the kind discriminator. `kind="match"` for adapters that pass;
    the other three are the rejection reasons spec §7.4 enumerates. -/
inductive MatchReason where
  | match_
  | orderTooHigh (detail : String)
  | logicOutOfFragment (detail : String)
  | typeConstructionNotSupported (detail : String)
  | otherReason (kind : String) (detail : String)
deriving Repr

/-- Outcome of `runMatchAdapters`: parallel `matches` and `rejections`
    arrays, each carrying the adapter name and (for rejections) the
    structured reason. -/
structure MatchResults where
  matchedAdapters : List String
  rejections : List (String × MatchReason)
deriving Inhabited

private def parseReason (j : Json) : MatchReason :=
  let kind := (j.getObjValAs? String "kind").toOption.getD ""
  let detail := (j.getObjValAs? String "detail").toOption.getD ""
  match kind with
  | "match" => .match_
  | "order_too_high" => .orderTooHigh detail
  | "logic_out_of_fragment" => .logicOutOfFragment detail
  | "type_construction_not_supported" => .typeConstructionNotSupported detail
  | k => .otherReason k detail

/-- Result of `runVerifyCertificate`. Mirrors OCaml's
    `Verifier.reason`, covering four layers: envelope checks
    (`verifiedEnvelope`, `hashMismatch`, `tierPayloadMismatch`,
    `certVersionMismatch`); Tier 1 / Farkas arithmetic checks
    (`verifiedFarkas` plus `farkas*` failure variants); Tier 2 /
    case-split-Farkas checks (`verifiedCaseSplit` plus `caseSplit*`
    failure variants — per-branch Farkas plus partition coverage of
    a disjunctive hypothesis); and Tier 3 / Alethe passthrough
    re-checking (`verifiedTier3` plus `tier3*` failure variants —
    per-step rule dispatch with `tier3UnsupportedRule` as the
    bailout, `tier3StepFailed` for rejected step-level checks, and
    `tier3UnsupportedFormat` for non-`alethe-2024` trace formats).
    For tiers without a soundness verifier, OCaml emits
    `tierCheckDeferred` / `unsupportedWitnessKind`; the cert's
    envelope was verified but nothing further. New reason kinds the
    OCaml side adds in the future decode into `otherCertReason`. -/
inductive CertReason where
  | verifiedEnvelope
  | verifiedFarkas
  | verifiedCaseSplit
  | verifiedTier3
  | hashMismatch (detail : String)
  | tierPayloadMismatch (detail : String)
  | certVersionMismatch (detail : String)
  | farkasUnknownHypothesis (detail : String)
  | farkasNonlinear (detail : String)
  | farkasBadCoefficient (detail : String)
  | farkasNegativeCoefficient (detail : String)
  | farkasNotContradictory (detail : String)
  | farkasMalformedWitness (detail : String)
  | caseSplitMalformed (detail : String)
  | caseSplitBranchFailed (detail : String)
  | caseSplitPartitionMismatch (detail : String)
  | tier3UnsupportedRule (detail : String)
  | tier3StepFailed (detail : String)
  | tier3UnsupportedFormat (detail : String)
  | unsupportedWitnessKind (detail : String)
  | tierCheckDeferred (detail : String)
  | otherCertReason (kind : String) (detail : String)
deriving Repr, Inhabited

structure CertVerification where
  ok : Bool
  reason : CertReason
deriving Inhabited

private def parseCertReason (j : Json) : CertReason :=
  let kind := (j.getObjValAs? String "kind").toOption.getD ""
  let detail := (j.getObjValAs? String "detail").toOption.getD ""
  match kind with
  | "verified_envelope" => .verifiedEnvelope
  | "verified_farkas" => .verifiedFarkas
  | "verified_case_split" => .verifiedCaseSplit
  | "verified_tier3" => .verifiedTier3
  | "hash_mismatch" => .hashMismatch detail
  | "tier_payload_mismatch" => .tierPayloadMismatch detail
  | "cert_version_mismatch" => .certVersionMismatch detail
  | "farkas_unknown_hypothesis" => .farkasUnknownHypothesis detail
  | "farkas_nonlinear" => .farkasNonlinear detail
  | "farkas_bad_coefficient" => .farkasBadCoefficient detail
  | "farkas_negative_coefficient" => .farkasNegativeCoefficient detail
  | "farkas_not_contradictory" => .farkasNotContradictory detail
  | "farkas_malformed_witness" => .farkasMalformedWitness detail
  | "case_split_malformed" => .caseSplitMalformed detail
  | "case_split_branch_failed" => .caseSplitBranchFailed detail
  | "case_split_partition_mismatch" => .caseSplitPartitionMismatch detail
  | "tier3_unsupported_rule" => .tier3UnsupportedRule detail
  | "tier3_step_failed" => .tier3StepFailed detail
  | "tier3_unsupported_format" => .tier3UnsupportedFormat detail
  | "unsupported_witness_kind" => .unsupportedWitnessKind detail
  | "tier_check_deferred" => .tierCheckDeferred detail
  | k => .otherCertReason k detail

/-- Certificate verification (spec §8.2). Submit a certificate,
    the IR it claims to address, and (optionally) the rewrite trace
    that produced that IR; the dispatcher runs envelope checks
    (well-formedness, tier/payload match, hash agreement) and then
    dispatches to a tier-specific soundness verifier where one
    exists. Today: Tier 1 / Farkas certs go through real arithmetic
    verification (returning `verifiedFarkas` / `farkas*`
    diagnostics); Tier 2 / case-split-Farkas certs (strategy_hint
    = "case_split_farkas") run a per-branch Farkas check plus a
    partition-coverage check against the disjunctive hypothesis
    named in `structural_hint.disjunctive_hypothesis` (returning
    `verifiedCaseSplit` / `caseSplit*` diagnostics); Tier 3 with
    `trace_format = "alethe-2024"` runs the per-step Alethe
    re-checker, returning `verifiedTier3` only when every step's
    rule has a registered checker that accepts (today: just
    `la_generic`; everything else trips
    `tier3UnsupportedRule`). Other tiers fall through to
    `tierCheckDeferred`, other Tier 1 witness kinds to
    `unsupportedWitnessKind`, and other Tier 3 trace formats to
    `tier3UnsupportedFormat`. Strict consumers should treat only
    `verifiedEnvelope`, `verifiedFarkas`, `verifiedCaseSplit`, and
    `verifiedTier3` as proof of soundness.

    Certificates are caller-supplied JSON because there's no
    Lean-side `Certificate` ADT yet — consistent with the
    pass-through stance for adapter manifests. -/
def runVerifyCertificate (cert : Json) (ir : IR) (trace : Option Document := none)
    : Except FfiError CertVerification := do
  let baseFields : List (String × Json) := [
    ("cert", cert),
    ("ir", ProofBroker.IR.IR.toJson ir)
  ]
  let fields := match trace with
    | none => baseFields
    | some d => baseFields ++ [("trace", Document.toJson d)]
  let input := Json.mkObj fields
  let payload ← decodeEnvelope (pbCall "verify_certificate" input.compress)
  let ok := (payload.getObjValAs? Bool "ok").toOption.getD false
  let reasonJ ← match payload.getObjVal? "reason" with
    | .ok v => pure v
    | .error _ => .error (.decodeError "missing 'reason'" none)
  return { ok, reason := parseCertReason reasonJ }

/-- Adapter dispatch failure (spec §7). Mirrors OCaml's
    `Adapter.failure`. `satReturned` means the solver said the
    negated goal is satisfiable — the home-system goal is *not*
    provable. `unknownReturned` is timeout or incompleteness on
    the fragment; the broker may try another adapter. The other
    variants are operational issues. New OCaml-side failure kinds
    decode into `otherDispatchFailure`. -/
inductive DispatchFailure where
  | satReturned
  | unknownReturned
  | timeout
  | solverError (detail : String)
  | parseError (detail : String)
  | unsupportedIr (detail : String)
  | adapterNotFound (detail : String)
  | otherDispatchFailure (kind : String) (detail : String)
deriving Repr, Inhabited

/-- Outcome of `runDispatchToAdapter`. Either the adapter minted a
    certificate (returned as raw JSON since there is no Lean-side
    Certificate ADT yet) or it failed with a typed reason. -/
inductive DispatchResult where
  | cert (certJson : Json)
  | failed (failure : DispatchFailure)
deriving Inhabited

instance : Repr DispatchResult where
  reprPrec r _ := match r with
    | .cert _ => "DispatchResult.cert <cert>"
    | .failed f => s!"DispatchResult.failed ({repr f})"

private def parseDispatchFailure (j : Json) : DispatchFailure :=
  let kind := (j.getObjValAs? String "kind").toOption.getD ""
  let detail := (j.getObjValAs? String "detail").toOption.getD ""
  match kind with
  | "sat_returned" => .satReturned
  | "unknown_returned" => .unknownReturned
  | "timeout" => .timeout
  | "solver_error" => .solverError detail
  | "parse_error" => .parseError detail
  | "unsupported_ir" => .unsupportedIr detail
  | "adapter_not_found" => .adapterNotFound detail
  | k => .otherDispatchFailure k detail

/-- Adapter invocation across the FFI (spec §7, Phase 2.1).
    Hand the broker an IR and the name of an adapter it knows
    about; the broker serializes to SMT-LIB, spawns the solver,
    and either mints a `Certificate` (returned as raw JSON) or
    surfaces a typed failure. The cert can be re-submitted to
    `runVerifyCertificate` to confirm the envelope addresses the
    same IR.

    Phase 2.1 supports `cvc4` only and only mints Tier 0 oracle
    certs; proof-tier minting (Tier 1 / Tier 3) is deferred. -/
def runDispatchToAdapter (adapter : String) (ir : IR)
    : Except FfiError DispatchResult := do
  let input := Json.mkObj [
    ("adapter", .str adapter),
    ("ir", ProofBroker.IR.IR.toJson ir)
  ]
  let payload ← decodeEnvelope (pbCall "dispatch_to_adapter" input.compress)
  let ok := (payload.getObjValAs? Bool "ok").toOption.getD false
  if ok then
    match payload.getObjVal? "cert" with
    | .ok j => pure (.cert j)
    | .error e => .error (.decodeError s!"missing 'cert': {e}" none)
  else
    let failJ ← match payload.getObjVal? "failure" with
      | .ok v => pure v
      | .error _ => .error (.decodeError "missing 'failure'" none)
    pure (.failed (parseDispatchFailure failJ))

/-- One per-manifest outcome from `runDispatchBroker`. Mirrors
    OCaml's [Dispatch.attempt_outcome]. Note: when [.succeeded],
    the cert isn't duplicated here — it lives at the top level of
    [BrokerResult]. -/
inductive AttemptOutcome where
  | skipped (reason : MatchReason)
  | noImplementation
  | failed (failure : DispatchFailure)
  | succeeded
deriving Repr, Inhabited

structure Attempt where
  adapter : String
  outcome : AttemptOutcome
deriving Repr, Inhabited

/-- Result of `runDispatchBroker`. [cert] is the first successful
    cert (as JSON, since there's no Lean-side Certificate ADT yet)
    or [none] if no adapter succeeded. [attempts] is the per-manifest
    outcome log in input order; in stop-on-success mode (the FFI
    default), the list ends at the first [.succeeded] attempt. -/
structure BrokerResult where
  cert : Option Json
  attempts : List Attempt
deriving Inhabited

private def parseAttempt (j : Json) : Attempt :=
  let adapter := (j.getObjValAs? String "adapter").toOption.getD ""
  let outcomeKind := (j.getObjValAs? String "outcome").toOption.getD ""
  let outcome : AttemptOutcome := match outcomeKind with
    | "skipped" =>
      let r := (j.getObjVal? "reason").toOption.getD .null
      .skipped (parseReason r)
    | "no_implementation" => .noImplementation
    | "failed" =>
      let f := (j.getObjVal? "failure").toOption.getD .null
      .failed (parseDispatchFailure f)
    | "succeeded" => .succeeded
    | _ => .noImplementation
  { adapter, outcome }

/-- Multi-adapter broker dispatch (spec §7). Hand the broker an IR
    plus an ordered list of manifest JSON values; the broker
    consults each manifest's capabilities, dispatches to the first
    eligible adapter that succeeds, and returns the cert (if any)
    plus the per-manifest attempt log.

    [preferHigherTier := true] (the default) sorts manifests by
    max declared tier capability descending before dispatch, so a
    Tier 1/2-capable adapter wins over a Tier 0 fallback regardless
    of input order. The sort is stable, so caller-supplied order
    within a tier is preserved. Pass [false] to opt out and respect
    input order verbatim. -/
def runDispatchBroker (ir : IR) (manifests : List Json)
    (preferHigherTier : Bool := true)
    : Except FfiError BrokerResult := do
  let input := Json.mkObj [
    ("ir", ProofBroker.IR.IR.toJson ir),
    ("manifests", Json.arr manifests.toArray),
    ("prefer_higher_tier", .bool preferHigherTier)
  ]
  let payload ← decodeEnvelope (pbCall "dispatch_broker" input.compress)
  let cert := (payload.getObjVal? "cert").toOption
  let attemptsJ ← match payload.getObjVal? "attempts" with
    | .ok v => pure v
    | .error _ => .error (.decodeError "missing 'attempts'" none)
  let arr ← match attemptsJ.getArr? with
    | .ok a => pure a
    | .error e => .error (.decodeError s!"attempts not array: {e}" none)
  let attempts := arr.toList.map parseAttempt
  return { cert, attempts }

/-- Submit an IR + a list of manifest JSON values to the dispatcher's
    capability-matching layer (spec §7.4). Returns the partition of
    adapters into matches / rejections. The manifests are caller-
    supplied JSON because there's no Lean-side `Manifest` ADT yet —
    consistent with the pass-through stance for adapter manifests
    documented in `sdk/FFI_CONVENTIONS.md`. -/
def runMatchAdapters (ir : IR) (manifests : List Json)
    : Except FfiError MatchResults := do
  let input := Json.mkObj [
    ("ir", ProofBroker.IR.IR.toJson ir),
    ("manifests", Json.arr manifests.toArray)
  ]
  let payload ← decodeEnvelope (pbCall "match_adapters" input.compress)
  let matchesJ ← match payload.getObjVal? "matches" with
    | .ok v => pure v
    | .error _ => .error (.decodeError "missing 'matches'" none)
  let rejectionsJ ← match payload.getObjVal? "rejections" with
    | .ok v => pure v
    | .error _ => .error (.decodeError "missing 'rejections'" none)
  let matchesArr ← match matchesJ.getArr? with
    | .ok a => pure a
    | .error e => .error (.decodeError s!"matches not array: {e}" none)
  let rejArr ← match rejectionsJ.getArr? with
    | .ok a => pure a
    | .error e => .error (.decodeError s!"rejections not array: {e}" none)
  let matched := matchesArr.toList.filterMap fun e =>
    (e.getObjValAs? String "adapter").toOption
  let rejections := rejArr.toList.filterMap fun e =>
    let adapter? := (e.getObjValAs? String "adapter").toOption
    let reason? := (e.getObjVal? "reason").toOption.map parseReason
    match adapter?, reason? with
    | some a, some r => some (a, r)
    | _, _ => none
  return { matchedAdapters := matched, rejections }

end ProofBroker

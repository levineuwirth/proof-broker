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

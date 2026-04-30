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
open ProofBroker.Trace (Entry)

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

end ProofBroker

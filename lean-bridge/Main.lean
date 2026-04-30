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
open ProofBroker (FfiError pbCall roundtripIR decodeEnvelope)
open ProofBroker.IR (IR normalize)

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

def main : IO Unit := do
  let cwd ← IO.currentDir
  let rootDir := cwd / ".."
  for fixture in fixtures do
    runRoundTrip rootDir fixture
  runJsonParseErrorPath
  runUnknownMethodPath
  runLeanCodecRejectsBadIr

/-
End-to-end FFI round-trip test.

Exercises the typed Lean surface from `ProofBroker.Bridge`:
  * Three IR fixtures round-trip through `roundtripIR`, with the
    decoded `Json` payload structurally equal to the original after
    normalization (recursive key sort, per `sdk/FFI_CONVENTIONS.md`).
  * Lexical garbage surfaces as `FfiError.jsonParseError`.
  * Calling an unknown method surfaces as `FfiError.unknownMethod`,
    proving the dispatcher's only synthetic envelope decodes through
    the typed Lean surface end-to-end.

Exits 0 on success, 1 on any failure path.
-/

import ProofBroker
import Lean.Data.Json

open Lean (Json)
open ProofBroker (FfiError pbCall roundtripIR decodeEnvelope)

/-- Recursive key sort: makes object equality order-insensitive,
    matching the OCaml-side `Codec.normalize`. -/
partial def normalize : Json → Json
  | .obj kvs =>
    let sorted := kvs.toArray.qsort (fun a b => a.1 < b.1) |>.toList
    .obj (sorted.foldl (fun m (k, v) => m.insert k (normalize v)) .empty)
  | .arr xs => .arr (xs.map normalize)
  | j => j

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

  let payload ← match roundtripIR input with
    | .ok p => pure p
    | .error e => fail s!"{fixture}: roundtripIR returned error: {repr e}"

  if normalize payload == normalize original then
    IO.println s!"OK Lean ↔ C ↔ OCaml round-trip: {fixture} structurally identical after normalization"
  else
    fail s!"{fixture}: round-trip differs structurally\noriginal: {(normalize original).pretty 2}\npayload:  {(normalize payload).pretty 2}"

def runJsonParseErrorPath : IO Unit := do
  match roundtripIR "{not json" with
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

def main : IO Unit := do
  let cwd ← IO.currentDir
  let rootDir := cwd / ".."
  for fixture in fixtures do
    runRoundTrip rootDir fixture
  runJsonParseErrorPath
  runUnknownMethodPath

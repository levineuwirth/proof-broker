/-
End-to-end FFI round-trip test.

Reads `examples/example1-lia-typeclass.json` from the repo root,
ships it through `pbRoundtripIr` (Lean → C glue → OCaml shim → C
glue → Lean), parses both sides as `Lean.Json`, normalizes
(recursive key sort) per `sdk/FFI_CONVENTIONS.md`, and asserts
structural equality of the round-tripped payload against the
original.

Exits 0 on success, 1 on any failure path.
-/

import ProofBroker
import Lean.Data.Json

open Lean (Json)

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

  let envelopeStr := ProofBroker.pbRoundtripIr input
  let envelope ← match Json.parse envelopeStr with
    | .ok j => pure j
    | .error e => fail s!"{fixture}: could not parse envelope: {e}\nraw: {envelopeStr}"

  match envelope.getObjValAs? String "status" with
  | .ok "ok" => pure ()
  | .ok other => fail s!"{fixture}: envelope status = {other}, expected ok\nenvelope: {envelopeStr}"
  | .error e => fail s!"{fixture}: missing status: {e}\nenvelope: {envelopeStr}"

  let payload ← match envelope.getObjVal? "payload" with
    | .ok j => pure j
    | .error e => fail s!"{fixture}: missing payload: {e}"

  if normalize payload == normalize original then
    IO.println s!"OK Lean ↔ C ↔ OCaml round-trip: {fixture} structurally identical after normalization"
  else
    fail s!"{fixture}: round-trip differs structurally\noriginal: {(normalize original).pretty 2}\npayload:  {(normalize payload).pretty 2}"

def runErrorPath : IO Unit := do
  let envelopeStr := ProofBroker.pbRoundtripIr "{not json"
  let envelope ← match Json.parse envelopeStr with
    | .ok j => pure j
    | .error e => fail s!"error envelope unparseable: {e}\nraw: {envelopeStr}"
  match envelope.getObjValAs? String "status" with
  | .ok "error" => pure ()
  | other => fail s!"expected error status, got {repr other}\nenvelope: {envelopeStr}"
  let kind ← match envelope.getObjVal? "error" >>= (·.getObjValAs? String "kind") with
    | .ok k => pure k
    | .error e => fail s!"missing error.kind: {e}"
  if kind == "json_parse_error" then
    IO.println s!"OK error propagation: malformed JSON surfaces as kind={kind}"
  else
    fail s!"unexpected error kind: {kind}"

def main : IO Unit := do
  let cwd ← IO.currentDir
  let rootDir := cwd / ".."
  for fixture in fixtures do
    runRoundTrip rootDir fixture
  runErrorPath

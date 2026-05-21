/-
Alethe proof ADT + walker (Lean side of the M1 Alethe walker
work, in the Lean-side Alethe walker arc).

The SDK ([sdk/lib/alethe.ml]) parses cvc5's alethe-2024 trace
into a step list and exposes it across the FFI via the
[parse_alethe_proof] method (see [ProofBroker.Bridge]). This
module mirrors the parsed structure on the Lean side and walks
it step-by-step, producing a kernel proof term — the "cert IS
the proof" architectural play, parallel to the Tier-1 Farkas
term-mode closer for Tier-1 certs but for Tier-3 alethe-2024.

Trust model. The OCaml-side [Tier3_alethe.verify] runs a
provenance-level check (every step references valid premises,
the proof walks to the empty clause). The walker here does the
*soundness* work: per-step elaboration into a Lean expression
that the kernel will independently typecheck when the goal
mvar is assigned. Audit H1: no axiom is introduced; a walker
failure on an unsupported rule is a tactic failure, with the
existing omega fallback re-running (closer chain in
[ProofBroker.Tactic.closeOrFail]).

M1 scope (LIA + UF): assume / refl / resolution / or /
la_generic / la_mult_neg / false-closing / symm / trans / cong
/ not_and / contraction / reordering. Subproof is M3 scope.
Unsupported rules surface as throwError; the omega fallback
catches them.
-/

import Lean
import ProofBroker.Bridge

namespace ProofBroker.Alethe

open Lean

/-- The parsed shape of an Alethe S-expression: a leaf atom
    (variable, keyword, literal) or a nested list. Mirrors the
    OCaml [Alethe.Sexp.t]; the FFI encoding (see
    [parse_alethe_proof] in [sdk/ffi/proof_broker_ffi.ml]) renders
    atoms as JSON strings and lists as JSON arrays. -/
inductive Sexp where
  | atom : String → Sexp
  | list : List Sexp → Sexp
  deriving Repr, BEq, Inhabited

/-- Decode an FFI-shaped JSON value into an `Sexp`. Strings →
    atoms; arrays → lists; anything else is a decoding error. -/
partial def Sexp.fromJson? : Json → Except String Sexp
  | .str s => .ok (.atom s)
  | .arr xs => do
    let parts ← xs.toList.mapM Sexp.fromJson?
    return .list parts
  | other =>
    .error s!"expected JSON string/array for Alethe Sexp, got: {other.compress}"

/-- An individual Alethe step from the parsed proof. The
    [conclusion] field corresponds to the [(cl …)] form's
    literals (after named-ref expansion); [args] and [premises]
    are rule-specific; [discharge] is the set of subproof
    assumptions discharged at this step (only populated for
    subproof-closing steps). -/
structure Step where
  id : String
  rule : String
  clause : List Sexp
  args : Option (List Sexp)
  premises : Option (List String)
  discharge : Option (List String)
  deriving Repr, Inhabited

private def sexpListFromJson? (j : Json) : Except String (List Sexp) :=
  match j with
  | .arr xs => xs.toList.mapM Sexp.fromJson?
  | _ => .error s!"expected JSON array, got: {j.compress}"

private def stringListFromJson? (j : Json) : Except String (List String) :=
  match j with
  | .arr xs => xs.toList.mapM (fun
      | .str s => .ok s
      | other => .error s!"expected string element, got: {other.compress}")
  | _ => .error s!"expected JSON array of strings, got: {j.compress}"

def Step.fromJson? (j : Json) : Except String Step := do
  let id ← match j.getObjValAs? String "id" with
    | .ok s => pure s
    | .error e => .error e
  let rule ← match j.getObjValAs? String "rule" with
    | .ok s => pure s
    | .error e => .error e
  let clauseJ ← match j.getObjVal? "clause" with
    | .ok v => pure v
    | .error _ => .error "missing 'clause'"
  let clause ← sexpListFromJson? clauseJ
  let args ← match j.getObjVal? "args" with
    | .error _ => pure none
    | .ok v => do
      let xs ← sexpListFromJson? v
      pure (some xs)
  let premises ← match j.getObjVal? "premises" with
    | .error _ => pure none
    | .ok v => do
      let xs ← stringListFromJson? v
      pure (some xs)
  let discharge ← match j.getObjVal? "discharge" with
    | .error _ => pure none
    | .ok v => do
      let xs ← stringListFromJson? v
      pure (some xs)
  return { id, rule, clause, args, premises, discharge }

/-- A top-level Alethe `assume` (the input hypotheses; each
    `assume`-rule step in the proof references one of these by
    id). On the home-system side these correspond to the
    negated-goal literals plus any hypothesis the original goal
    carried into the SMT call. -/
structure Assume where
  id : String
  literal : Sexp
  deriving Repr, Inhabited

def Assume.fromJson? (j : Json) : Except String Assume := do
  let id ← match j.getObjValAs? String "id" with
    | .ok s => pure s
    | .error e => .error e
  let litJ ← match j.getObjVal? "literal" with
    | .ok v => pure v
    | .error _ => .error "missing 'literal'"
  let literal ← Sexp.fromJson? litJ
  return { id, literal }

/-- The full parsed proof: top-level assumes, the step list (in
    declaration order), and the subproof anchor ids (M3 scope —
    not consumed by M1). -/
structure Proof where
  assumes : List Assume
  steps : List Step
  anchors : List String
  deriving Repr, Inhabited

def Proof.fromJson? (j : Json) : Except String Proof := do
  let assumesJ ← match j.getObjVal? "assumes" with
    | .ok v => pure v
    | .error _ => .error "missing 'assumes'"
  let assumes ← match assumesJ with
    | .arr xs => xs.toList.mapM Assume.fromJson?
    | _ => .error "'assumes' is not an array"
  let stepsJ ← match j.getObjVal? "steps" with
    | .ok v => pure v
    | .error _ => .error "missing 'steps'"
  let steps ← match stepsJ with
    | .arr xs => xs.toList.mapM Step.fromJson?
    | _ => .error "'steps' is not an array"
  let anchorsJ ← match j.getObjVal? "anchors" with
    | .ok v => pure v
    | .error _ => .error "missing 'anchors'"
  let anchors ← stringListFromJson? anchorsJ
  return { assumes, steps, anchors }

open ProofBroker (FfiError pbCall decodeEnvelope)

/-- Parse a cvc5 alethe-2024 trace into an `Alethe.Proof` via the
    SDK's [parse_alethe_proof] FFI method. Failure modes: parser
    errors (raised from OCaml as `alethe_parse_error`), envelope
    decode errors (malformed FFI response), and Alethe-shape
    decode errors (FFI returned an unexpected shape). -/
def runParseAletheProof (proofText : String) : Except FfiError Proof := do
  let input := Json.mkObj [("proof", Json.str proofText)]
  let payload ← decodeEnvelope (pbCall "parse_alethe_proof" input.compress)
  match Proof.fromJson? payload with
  | .ok p => pure p
  | .error e =>
    .error (.decodeError s!"decoding alethe proof: {e}" none)

end ProofBroker.Alethe

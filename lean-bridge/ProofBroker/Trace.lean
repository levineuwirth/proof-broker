/-
Lean-side rewrite-trace types matching
`schemas/v1.0/rewrite-trace.schema.json` (single-entry shape).

Mirrors `sdk/lib/trace.ml` one-to-one. The schema's `configuration`
and `inversion_data` fields are JSON pass-through (the schema is
deliberately permissive there); per-pass interpretation lives in the
pass's typed wrapper, not here.
-/

import Lean.Data.Json

namespace ProofBroker.Trace

open Lean (Json ToJson FromJson)

/-- Outcome enum, matching the schema's `outcome` field. -/
inductive Outcome where
  | applied
  | skippedPreconditions
  | noOp
  | failed
deriving Repr, BEq, Inhabited

def Outcome.toString : Outcome → String
  | .applied => "applied"
  | .skippedPreconditions => "skipped_preconditions"
  | .noOp => "no_op"
  | .failed => "failed"

def Outcome.fromString? : String → Except String Outcome
  | "applied" => .ok .applied
  | "skipped_preconditions" => .ok .skippedPreconditions
  | "no_op" => .ok .noOp
  | "failed" => .ok .failed
  | other => .error s!"unknown outcome: {other}"

/-- Single trace entry. Fields with [Option] types are absent in the
    JSON encoding when set to `none`, never serialized as `null`,
    matching the OCaml side and the schema's "field absent =
    field absent" convention. -/
structure Entry where
  pass : String
  version : String
  beforeHash : String
  afterHash : String
  configuration : Option Json
  outcome : Option Outcome
  inversionData : Option Json
  diagnostics : Option String
deriving Inhabited

private def getReqStr (j : Json) (key : String) : Except String String :=
  match j.getObjValAs? String key with
  | .ok s => .ok s
  | .error _ => .error s!"missing or non-string field: {key}"

private def getOpt (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

def Entry.toJson (e : Entry) : Json :=
  let fields : List (String × Json) := [
    ("pass", .str e.pass),
    ("version", .str e.version),
    ("before_hash", .str e.beforeHash),
    ("after_hash", .str e.afterHash)
  ]
  let fields := match e.configuration with
    | none => fields
    | some c => fields ++ [("configuration", c)]
  let fields := match e.outcome with
    | none => fields
    | some o => fields ++ [("outcome", .str o.toString)]
  let fields := match e.inversionData with
    | none => fields
    | some d => fields ++ [("inversion_data", d)]
  let fields := match e.diagnostics with
    | none => fields
    | some s => fields ++ [("diagnostics", .str s)]
  Json.mkObj fields

def Entry.fromJson? (j : Json) : Except String Entry := do
  let outcome ← match getOpt j "outcome" with
    | none => pure none
    | some (.str s) => do let o ← Outcome.fromString? s; pure (some o)
    | some other => .error s!"expected string at outcome, got {other.compress}"
  let diagnostics := match getOpt j "diagnostics" with
    | none => none
    | some v => v.getStr?.toOption
  return {
    pass := ← getReqStr j "pass",
    version := ← getReqStr j "version",
    beforeHash := ← getReqStr j "before_hash",
    afterHash := ← getReqStr j "after_hash",
    configuration := getOpt j "configuration",
    outcome,
    inversionData := getOpt j "inversion_data",
    diagnostics
  }

instance : ToJson Entry := ⟨Entry.toJson⟩
instance : FromJson Entry := ⟨Entry.fromJson?⟩

/-- Pipeline-level trace document (spec v1.0 §5.6). Mirrors
    `sdk/lib/trace.ml`'s `t` type and the schema's top-level shape.
    `configuration` is JSON pass-through: the schema constrains its
    inner shape, but a typed Lean ADT for it is overkill until a Lean
    caller needs to build pipelines from typed config rather than
    receive them as opaque payloads. -/
structure Document where
  traceVersion : String
  initialIrHash : String
  finalIrHash : String
  entries : List Entry
  configuration : Option Json
deriving Inhabited

def Document.toJson (d : Document) : Json :=
  let fields : List (String × Json) := [
    ("trace_version", .str d.traceVersion),
    ("initial_ir_hash", .str d.initialIrHash),
    ("final_ir_hash", .str d.finalIrHash),
    ("entries", Json.arr (d.entries.map Entry.toJson).toArray)
  ]
  let fields := match d.configuration with
    | none => fields
    | some c => fields ++ [("configuration", c)]
  Json.mkObj fields

def Document.fromJson? (j : Json) : Except String Document := do
  let entriesJ ← j.getObjVal? "entries"
  let entriesArr ← entriesJ.getArr?
  let entries ← entriesArr.toList.mapM Entry.fromJson?
  return {
    traceVersion := ← getReqStr j "trace_version",
    initialIrHash := ← getReqStr j "initial_ir_hash",
    finalIrHash := ← getReqStr j "final_ir_hash",
    entries,
    configuration := getOpt j "configuration"
  }

instance : ToJson Document := ⟨Document.toJson⟩
instance : FromJson Document := ⟨Document.fromJson?⟩

end ProofBroker.Trace

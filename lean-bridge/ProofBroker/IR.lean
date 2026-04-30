/-
Lean-side IR ADTs and JSON codec for spec v1.0.

Mirrors `sdk/lib/ir.ml` and `sdk/lib/codec.ml` one-to-one against
`schemas/v1.0/ir.schema.json` (the canonical source). Field names
and shell-node tags match the schema verbatim; Lean reserved words
(`forall`, `exists`, `opaque`, etc.) become trailing-underscore
constructors (`forall_`, `exists_`, `opaque_`).

`type_metadata` and `definitional_metadata` are JSON pass-through
per `sdk/FFI_CONVENTIONS.md` until structured ADTs land. The codec
round-trips them faithfully because it does not look at the values.
The Python `tools/check.py` validator remains the single source of
truth for these maps.
-/

import Lean.Data.Json
import Lean.Data.RBMap

namespace ProofBroker.IR

open Lean (Json ToJson FromJson)
open Lean.ToJson (toJson)
open Lean.FromJson (fromJson?)

/-- A type reference: either a shell primitive or a key into
    `type_metadata` / `context.type_vars`. Currently a string in
    the schema; promoted to its own abbrev for readability. -/
abbrev TypeRef := String

structure Binder where
  var : String
  ty : TypeRef
deriving Inhabited, BEq, Repr

/-- Shell-calculus terms (spec §4.4). The JSON encoding tags each
    constructor with a `node` discriminator matching the OCaml
    side: "Forall", "Exists", "Lambda", ... -/
inductive ShellTerm where
  | forall_  (var : String) (ty : TypeRef) (body : ShellTerm)
  | exists_  (var : String) (ty : TypeRef) (body : ShellTerm)
  | lambda   (binders : List Binder) (body : ShellTerm)
  | implies  (antecedent : ShellTerm) (consequent : ShellTerm)
  | and_     (left : ShellTerm) (right : ShellTerm)
  | or_      (left : ShellTerm) (right : ShellTerm)
  | not_     (operand : ShellTerm)
  | eq       (ty : TypeRef) (left : ShellTerm) (right : ShellTerm)
  | app      (symbol : String) (typeArgs : List TypeRef) (args : List ShellTerm)
  | var      (name : String)
  | const    (name : String)
  | numLit   (value : String) (ty : TypeRef)
  | opaque_  (payloadId : String)
deriving Inhabited

structure Goal where
  shell : ShellTerm
  /-- Optional payloads object, JSON pass-through. -/
  payloads : Option Json
deriving Inhabited

structure FreeVar where
  name : String
  ty : TypeRef
deriving Inhabited, BEq, Repr

structure Hypothesis where
  name : String
  shell : ShellTerm
deriving Inhabited

structure LibrarySliceEntry where
  entityName : String
  shell : ShellTerm
  selectionReason : Option String
deriving Inhabited

structure Context where
  typeVars : List String
  freeVars : List FreeVar
  hypotheses : List Hypothesis
  librarySlice : Option (List LibrarySliceEntry)
deriving Inhabited

structure LogicClassification where
  order : String
  featuresUsed : List String
  firstOrderFragment : String
  /-- Schema-level nullable: `null` is distinct from absent. The
      schema requires the field to be present, so this stays
      non-`Option` at the structure level — `none` here means the
      JSON had explicit `null`. -/
  decidableTheory : Option String
deriving Inhabited, Repr

structure Provenance where
  library : String
  version : String
  modulePath : Option String
  contentHash : String
deriving Inhabited, Repr

structure Budget where
  wallTimeMs : Option Int
  memoryMb : Option Int
deriving Inhabited, Repr

structure RewriterPreferences where
  enableQuotientElimination : Option Bool
  enableDefinitionUnfolding : Option (List String)
  disablePasses : Option (List String)
deriving Inhabited, Repr

/-- Three-state encoding of `user_directives.preferred_backend`,
    matching OCaml's `[ \`Null | \`String of string ] option`:
    `Option.none` = field absent, `some .explicitNull` = JSON null,
    `some (.named s)` = backend named. The distinction matters
    because explicit-null carries a different intent than
    field-absent (the user opted out of expressing a preference,
    versus the serializer not setting it at all). -/
inductive PreferredBackend where
  | explicitNull
  | named (name : String)
deriving Inhabited, Repr, BEq

structure UserDirectives where
  preferredBackend : Option PreferredBackend
  tierPreference : Option (List String)
  rewriterPreferences : Option RewriterPreferences
  budget : Option Budget
deriving Inhabited

structure SourceSystem where
  name : String
  version : String
deriving Inhabited, Repr, BEq

/-- Top-level IR document. Field names are camelCase here; the
    codec maps them to the schema's snake_case. -/
structure IR where
  irVersion : String
  sourceSystem : SourceSystem
  tier : String
  logicClassification : LogicClassification
  goal : Goal
  context : Context
  /-- Pass-through; structured ADTs deferred. -/
  typeMetadata : List (String × Json)
  /-- Pass-through; structured ADTs deferred. -/
  definitionalMetadata : List (String × Json)
  libraryProvenance : List (String × Provenance)
  userDirectives : Option UserDirectives
deriving Inhabited

/- ===========================================================
   JSON codec
   =========================================================== -/

/-- Convenience: extract an obj's pairs as a list. -/
private def objPairs? (j : Json) : Except String (List (String × Json)) :=
  match j with
  | .obj kvs => .ok (kvs.foldl (init := []) (fun acc k v => (k, v) :: acc) |>.reverse)
  | _ => .error s!"expected object, got {j.compress}"

/-- Get an optional field. Returns `none` if absent, `some v` if present. -/
private def getOpt (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

/-- Get a required field by key. -/
private def getReq (j : Json) (key : String) : Except String Json :=
  match j.getObjVal? key with
  | .ok v => .ok v
  | .error _ => .error s!"missing field: {key}"

/-- Get a required string field. -/
private def getReqStr (j : Json) (key : String) : Except String String := do
  let v ← getReq j key
  match v with
  | .str s => .ok s
  | _ => .error s!"expected string at {key}, got {v.compress}"

/-- Build an obj from a list of (key, value) pairs preserving the
    convention used by Lean's Json.mkObj. -/
private def mkObj (pairs : List (String × Json)) : Json := Json.mkObj pairs

/- ---- Binder ---- -/

def Binder.toJson (b : Binder) : Json :=
  mkObj [("var", .str b.var), ("type", .str b.ty)]

def Binder.fromJson? (j : Json) : Except String Binder := do
  return { var := ← getReqStr j "var", ty := ← getReqStr j "type" }

instance : ToJson Binder := ⟨Binder.toJson⟩
instance : FromJson Binder := ⟨Binder.fromJson?⟩

/- ---- ShellTerm ---- -/

partial def ShellTerm.toJson : ShellTerm → Json
  | .forall_ v t b =>
    mkObj [("node", .str "Forall"), ("var", .str v), ("type", .str t),
           ("body", ShellTerm.toJson b)]
  | .exists_ v t b =>
    mkObj [("node", .str "Exists"), ("var", .str v), ("type", .str t),
           ("body", ShellTerm.toJson b)]
  | .lambda binders b =>
    mkObj [("node", .str "Lambda"),
           ("binders", .arr (binders.map Binder.toJson |>.toArray)),
           ("body", ShellTerm.toJson b)]
  | .implies a c =>
    mkObj [("node", .str "Implies"),
           ("antecedent", ShellTerm.toJson a),
           ("consequent", ShellTerm.toJson c)]
  | .and_ l r =>
    mkObj [("node", .str "And"),
           ("left", ShellTerm.toJson l), ("right", ShellTerm.toJson r)]
  | .or_ l r =>
    mkObj [("node", .str "Or"),
           ("left", ShellTerm.toJson l), ("right", ShellTerm.toJson r)]
  | .not_ op =>
    mkObj [("node", .str "Not"), ("operand", ShellTerm.toJson op)]
  | .eq t l r =>
    mkObj [("node", .str "Eq"), ("type", .str t),
           ("left", ShellTerm.toJson l), ("right", ShellTerm.toJson r)]
  | .app symbol typeArgs args =>
    mkObj [("node", .str "App"), ("symbol", .str symbol),
           ("type_args", .arr (typeArgs.map (Json.str ·) |>.toArray)),
           ("args", .arr (args.map ShellTerm.toJson |>.toArray))]
  | .var name =>
    mkObj [("node", .str "Var"), ("name", .str name)]
  | .const name =>
    mkObj [("node", .str "Const"), ("name", .str name)]
  | .numLit value t =>
    mkObj [("node", .str "NumLit"), ("value", .str value), ("type", .str t)]
  | .opaque_ payloadId =>
    mkObj [("node", .str "Opaque"), ("payload_id", .str payloadId)]

private def strList? (j : Json) : Except String (List String) := do
  let arr ← j.getArr?
  arr.toList.mapM Json.getStr?

partial def ShellTerm.fromJson? (j : Json) : Except String ShellTerm := do
  let node ← getReqStr j "node"
  match node with
  | "Forall" =>
    return .forall_ (← getReqStr j "var") (← getReqStr j "type")
                    (← ShellTerm.fromJson? (← getReq j "body"))
  | "Exists" =>
    return .exists_ (← getReqStr j "var") (← getReqStr j "type")
                    (← ShellTerm.fromJson? (← getReq j "body"))
  | "Lambda" => do
    let bindersJ ← (← getReq j "binders").getArr?
    let binders ← bindersJ.toList.mapM Binder.fromJson?
    return .lambda binders (← ShellTerm.fromJson? (← getReq j "body"))
  | "Implies" =>
    return .implies (← ShellTerm.fromJson? (← getReq j "antecedent"))
                    (← ShellTerm.fromJson? (← getReq j "consequent"))
  | "And" =>
    return .and_ (← ShellTerm.fromJson? (← getReq j "left"))
                 (← ShellTerm.fromJson? (← getReq j "right"))
  | "Or" =>
    return .or_ (← ShellTerm.fromJson? (← getReq j "left"))
                (← ShellTerm.fromJson? (← getReq j "right"))
  | "Not" =>
    return .not_ (← ShellTerm.fromJson? (← getReq j "operand"))
  | "Eq" =>
    return .eq (← getReqStr j "type")
               (← ShellTerm.fromJson? (← getReq j "left"))
               (← ShellTerm.fromJson? (← getReq j "right"))
  | "App" => do
    let typeArgs ← match getOpt j "type_args" with
      | .none => pure []
      | .some v => strList? v
    let args ← match getOpt j "args" with
      | .none => pure []
      | .some v => do
        let arr ← v.getArr?
        arr.toList.mapM ShellTerm.fromJson?
    return .app (← getReqStr j "symbol") typeArgs args
  | "Var"   => return .var (← getReqStr j "name")
  | "Const" => return .const (← getReqStr j "name")
  | "NumLit" =>
    return .numLit (← getReqStr j "value") (← getReqStr j "type")
  | "Opaque" =>
    return .opaque_ (← getReqStr j "payload_id")
  | other => .error s!"unknown shell node: {other}"

instance : ToJson ShellTerm := ⟨ShellTerm.toJson⟩
instance : FromJson ShellTerm := ⟨ShellTerm.fromJson?⟩

/- ---- Goal ---- -/

def Goal.toJson (g : Goal) : Json :=
  let base := [("shell", ShellTerm.toJson g.shell)]
  match g.payloads with
  | none => mkObj base
  | some p => mkObj (base ++ [("payloads", p)])

def Goal.fromJson? (j : Json) : Except String Goal := do
  return {
    shell := ← ShellTerm.fromJson? (← getReq j "shell"),
    payloads := getOpt j "payloads"
  }

instance : ToJson Goal := ⟨Goal.toJson⟩
instance : FromJson Goal := ⟨Goal.fromJson?⟩

/- ---- FreeVar ---- -/

def FreeVar.toJson (fv : FreeVar) : Json :=
  mkObj [("name", .str fv.name), ("type", .str fv.ty)]

def FreeVar.fromJson? (j : Json) : Except String FreeVar := do
  return { name := ← getReqStr j "name", ty := ← getReqStr j "type" }

instance : ToJson FreeVar := ⟨FreeVar.toJson⟩
instance : FromJson FreeVar := ⟨FreeVar.fromJson?⟩

/- ---- Hypothesis ---- -/

def Hypothesis.toJson (h : Hypothesis) : Json :=
  mkObj [("name", .str h.name), ("shell", ShellTerm.toJson h.shell)]

def Hypothesis.fromJson? (j : Json) : Except String Hypothesis := do
  return {
    name := ← getReqStr j "name",
    shell := ← ShellTerm.fromJson? (← getReq j "shell")
  }

instance : ToJson Hypothesis := ⟨Hypothesis.toJson⟩
instance : FromJson Hypothesis := ⟨Hypothesis.fromJson?⟩

/- ---- LibrarySliceEntry ---- -/

def LibrarySliceEntry.toJson (e : LibrarySliceEntry) : Json :=
  let base := [("entity_name", .str e.entityName),
               ("shell", ShellTerm.toJson e.shell)]
  match e.selectionReason with
  | none => mkObj base
  | some r => mkObj (base ++ [("selection_reason", .str r)])

def LibrarySliceEntry.fromJson? (j : Json) : Except String LibrarySliceEntry := do
  return {
    entityName := ← getReqStr j "entity_name",
    shell := ← ShellTerm.fromJson? (← getReq j "shell"),
    selectionReason := match getOpt j "selection_reason" with
      | none => none
      | some v => v.getStr?.toOption
  }

instance : ToJson LibrarySliceEntry := ⟨LibrarySliceEntry.toJson⟩
instance : FromJson LibrarySliceEntry := ⟨LibrarySliceEntry.fromJson?⟩

/- ---- Context ---- -/

def Context.toJson (c : Context) : Json :=
  let base : List (String × Json) := [
    ("type_vars", .arr (c.typeVars.map (Json.str ·) |>.toArray)),
    ("free_vars", .arr (c.freeVars.map FreeVar.toJson |>.toArray)),
    ("hypotheses", .arr (c.hypotheses.map Hypothesis.toJson |>.toArray)),
  ]
  match c.librarySlice with
  | none => mkObj base
  | some xs =>
    mkObj (base ++ [("library_slice",
                     .arr (xs.map LibrarySliceEntry.toJson |>.toArray))])

def Context.fromJson? (j : Json) : Except String Context := do
  let typeVars ← match getOpt j "type_vars" with
    | none => pure []
    | some v => strList? v
  let freeVars ← match getOpt j "free_vars" with
    | none => pure []
    | some v => do (← v.getArr?).toList.mapM FreeVar.fromJson?
  let hypotheses ← match getOpt j "hypotheses" with
    | none => pure []
    | some v => do (← v.getArr?).toList.mapM Hypothesis.fromJson?
  let librarySlice ← match getOpt j "library_slice" with
    | none => pure none
    | some v => do
      let xs ← (← v.getArr?).toList.mapM LibrarySliceEntry.fromJson?
      pure (some xs)
  return { typeVars, freeVars, hypotheses, librarySlice }

instance : ToJson Context := ⟨Context.toJson⟩
instance : FromJson Context := ⟨Context.fromJson?⟩

/- ---- LogicClassification ---- -/

def LogicClassification.toJson (lc : LogicClassification) : Json :=
  mkObj [
    ("order", .str lc.order),
    ("features_used", .arr (lc.featuresUsed.map (Json.str ·) |>.toArray)),
    ("first_order_fragment", .str lc.firstOrderFragment),
    ("decidable_theory",
      match lc.decidableTheory with
      | none => Json.null
      | some s => Json.str s)
  ]

def LogicClassification.fromJson? (j : Json) : Except String LogicClassification := do
  let dt ← match ← getReq j "decidable_theory" with
    | .null => pure none
    | .str s => pure (some s)
    | other => .error s!"expected string or null at decidable_theory, got {other.compress}"
  return {
    order := ← getReqStr j "order",
    featuresUsed := ← strList? (← getReq j "features_used"),
    firstOrderFragment := ← getReqStr j "first_order_fragment",
    decidableTheory := dt
  }

instance : ToJson LogicClassification := ⟨LogicClassification.toJson⟩
instance : FromJson LogicClassification := ⟨LogicClassification.fromJson?⟩

/- ---- Provenance ---- -/

def Provenance.toJson (p : Provenance) : Json :=
  let fields : List (String × Json) := [
    ("library", .str p.library),
    ("version", .str p.version)
  ]
  let fields := match p.modulePath with
    | none => fields
    | some s => fields ++ [("module_path", .str s)]
  mkObj (fields ++ [("content_hash", .str p.contentHash)])

def Provenance.fromJson? (j : Json) : Except String Provenance := do
  return {
    library := ← getReqStr j "library",
    version := ← getReqStr j "version",
    modulePath := match getOpt j "module_path" with
      | none => none
      | some v => v.getStr?.toOption,
    contentHash := ← getReqStr j "content_hash"
  }

instance : ToJson Provenance := ⟨Provenance.toJson⟩
instance : FromJson Provenance := ⟨Provenance.fromJson?⟩

/- ---- Budget ---- -/

def Budget.toJson (b : Budget) : Json :=
  let fields : List (String × Json) := []
  let fields := match b.wallTimeMs with
    | none => fields
    | some n => fields ++ [("wall_time_ms", Json.num n)]
  let fields := match b.memoryMb with
    | none => fields
    | some n => fields ++ [("memory_mb", Json.num n)]
  mkObj fields

def Budget.fromJson? (j : Json) : Except String Budget := do
  let getIntOpt (key : String) : Except String (Option Int) :=
    match getOpt j key with
    | none => .ok none
    | some v => v.getInt?.map some
  return { wallTimeMs := ← getIntOpt "wall_time_ms",
           memoryMb := ← getIntOpt "memory_mb" }

instance : ToJson Budget := ⟨Budget.toJson⟩
instance : FromJson Budget := ⟨Budget.fromJson?⟩

/- ---- RewriterPreferences ---- -/

def RewriterPreferences.toJson (rp : RewriterPreferences) : Json :=
  let fields : List (String × Json) := []
  let fields := match rp.enableQuotientElimination with
    | none => fields
    | some b => fields ++ [("enable_quotient_elimination", Json.bool b)]
  let fields := match rp.enableDefinitionUnfolding with
    | none => fields
    | some xs => fields ++ [("enable_definition_unfolding",
                              .arr (xs.map (Json.str ·) |>.toArray))]
  let fields := match rp.disablePasses with
    | none => fields
    | some xs => fields ++ [("disable_passes",
                              .arr (xs.map (Json.str ·) |>.toArray))]
  mkObj fields

def RewriterPreferences.fromJson? (j : Json) : Except String RewriterPreferences := do
  let optBool (key : String) : Except String (Option Bool) :=
    match getOpt j key with
    | none => .ok none
    | some v => v.getBool?.map some
  let optStrList (key : String) : Except String (Option (List String)) :=
    match getOpt j key with
    | none => .ok none
    | some v => do let xs ← strList? v; pure (some xs)
  return {
    enableQuotientElimination := ← optBool "enable_quotient_elimination",
    enableDefinitionUnfolding := ← optStrList "enable_definition_unfolding",
    disablePasses := ← optStrList "disable_passes"
  }

instance : ToJson RewriterPreferences := ⟨RewriterPreferences.toJson⟩
instance : FromJson RewriterPreferences := ⟨RewriterPreferences.fromJson?⟩

/- ---- UserDirectives ---- -/

def UserDirectives.toJson (ud : UserDirectives) : Json :=
  let fields : List (String × Json) := []
  let fields := match ud.preferredBackend with
    | none => fields
    | some .explicitNull => fields ++ [("preferred_backend", Json.null)]
    | some (.named s) => fields ++ [("preferred_backend", .str s)]
  let fields := match ud.tierPreference with
    | none => fields
    | some xs => fields ++ [("tier_preference",
                              .arr (xs.map (Json.str ·) |>.toArray))]
  let fields := match ud.rewriterPreferences with
    | none => fields
    | some rp => fields ++ [("rewriter_preferences",
                              RewriterPreferences.toJson rp)]
  let fields := match ud.budget with
    | none => fields
    | some b => fields ++ [("budget", Budget.toJson b)]
  mkObj fields

def UserDirectives.fromJson? (j : Json) : Except String UserDirectives := do
  let preferredBackend ← match getOpt j "preferred_backend" with
    | none => pure none
    | some .null => pure (some .explicitNull)
    | some (.str s) => pure (some (.named s))
    | some other => .error s!"expected string or null at preferred_backend, got {other.compress}"
  let tierPreference ← match getOpt j "tier_preference" with
    | none => pure none
    | some v => do let xs ← strList? v; pure (some xs)
  let rewriterPreferences ← match getOpt j "rewriter_preferences" with
    | none => pure none
    | some v => do let rp ← RewriterPreferences.fromJson? v; pure (some rp)
  let budget ← match getOpt j "budget" with
    | none => pure none
    | some v => do let b ← Budget.fromJson? v; pure (some b)
  return { preferredBackend, tierPreference, rewriterPreferences, budget }

instance : ToJson UserDirectives := ⟨UserDirectives.toJson⟩
instance : FromJson UserDirectives := ⟨UserDirectives.fromJson?⟩

/- ---- SourceSystem ---- -/

def SourceSystem.toJson (s : SourceSystem) : Json :=
  mkObj [("name", .str s.name), ("version", .str s.version)]

def SourceSystem.fromJson? (j : Json) : Except String SourceSystem := do
  return { name := ← getReqStr j "name", version := ← getReqStr j "version" }

instance : ToJson SourceSystem := ⟨SourceSystem.toJson⟩
instance : FromJson SourceSystem := ⟨SourceSystem.fromJson?⟩

/- ---- IR (top level) ---- -/

def IR.toJson (ir : IR) : Json :=
  let provenancePairs : List (String × Json) :=
    ir.libraryProvenance.map (fun (k, v) => (k, Provenance.toJson v))
  let fields : List (String × Json) := [
    ("ir_version", .str ir.irVersion),
    ("source_system", SourceSystem.toJson ir.sourceSystem),
    ("tier", .str ir.tier),
    ("logic_classification", LogicClassification.toJson ir.logicClassification),
    ("goal", Goal.toJson ir.goal),
    ("context", Context.toJson ir.context),
    ("type_metadata", mkObj ir.typeMetadata),
    ("definitional_metadata", mkObj ir.definitionalMetadata),
    ("library_provenance", mkObj provenancePairs)
  ]
  match ir.userDirectives with
  | none => mkObj fields
  | some ud => mkObj (fields ++ [("user_directives", UserDirectives.toJson ud)])

def IR.fromJson? (j : Json) : Except String IR := do
  let typeMetadata ← match getOpt j "type_metadata" with
    | none => pure []
    | some v => objPairs? v
  let definitionalMetadata ← match getOpt j "definitional_metadata" with
    | none => pure []
    | some v => objPairs? v
  let libraryProvenance ← match getOpt j "library_provenance" with
    | none => pure []
    | some v => do
      let pairs ← objPairs? v
      pairs.mapM (fun (k, pj) => do let p ← Provenance.fromJson? pj; pure (k, p))
  let userDirectives ← match getOpt j "user_directives" with
    | none => pure none
    | some v => do let ud ← UserDirectives.fromJson? v; pure (some ud)
  return {
    irVersion := ← getReqStr j "ir_version",
    sourceSystem := ← SourceSystem.fromJson? (← getReq j "source_system"),
    tier := ← getReqStr j "tier",
    logicClassification := ← LogicClassification.fromJson? (← getReq j "logic_classification"),
    goal := ← Goal.fromJson? (← getReq j "goal"),
    context := ← Context.fromJson? (← getReq j "context"),
    typeMetadata,
    definitionalMetadata,
    libraryProvenance,
    userDirectives
  }

instance : ToJson IR := ⟨IR.toJson⟩
instance : FromJson IR := ⟨IR.fromJson?⟩

/-- Parse a JSON string into a typed IR, composing `Json.parse` and
    `IR.fromJson?`. Convenience for fixture-loading and tests. -/
def IR.fromJsonString (s : String) : Except String IR := do
  let j ← Json.parse s
  IR.fromJson? j

/-- Re-serialize a typed IR to a compact JSON string. Convenience for
    FFI callers and round-trip diagnostics. -/
def IR.toJsonString (ir : IR) : String :=
  (IR.toJson ir).compress

/- ===========================================================
   JSON normalization for round-trip equality
   =========================================================== -/

/-- Recursive key sort, matching `sdk/lib/codec.ml`'s `normalize`
    and the OCaml `Codec.normalize`. Two JSON documents that
    `normalize`-equal are considered equal across the boundary. -/
partial def normalize : Json → Json
  | .obj kvs =>
    let pairs := kvs.foldl (init := []) (fun acc k v => (k, normalize v) :: acc)
    let sorted := pairs.toArray.qsort (fun a b => a.1 < b.1) |>.toList
    Json.mkObj sorted
  | .arr xs => .arr (xs.map normalize)
  | j => j

/-- Round-trip equality: parse, encode, normalize, compare. -/
def equalAfterNormalize (a b : Json) : Bool :=
  normalize a == normalize b

end ProofBroker.IR

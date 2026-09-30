import Lean
import Export.Parse
open Lean Meta Elab

/-!
# R6 qualification 1 audit

The tool specified by `experiments/r6/R6-QUALIFICATION-1-AUDIT-PROPOSAL.md` (revision 2). For one `lean4export` export it
reports, for the broker's final positivity step `hpos : 0 < s` in `ProofBroker.TermMode.farkasContradictN s sumProof hpos`:

* **Check 1 (dependency):** which hypotheses `hpos` refers to, directly or through local definitions (`let` values and the
  arguments of applied lambdas), each with its path; for the whole target, mapped through the arguments at its single reference
  to the local theorem.
* **Check 2 (sufficiency):** whether `omega`, in an empty context, proves the original quantified statement `∀ values, 0 < s`;
  a success counts only when the kernel accepts the proof. An abstraction path (non-arithmetic subterms generalized) counts
  only together with a kernel-checked specialization back to the original statement.

## Environment

Built with the Lean 4.32.0 toolchain, whose git hash equals the exports' header (`8c9756b2…`). `Init` is imported with its
extensions; every export constant `Init` also has must equal it up to what the kernel ignores (metadata, binder names and info,
the `let` `nonDep` hint), or the audit refuses. The export's remaining constants are replayed through `addDecl`, so each is
kernel-checked and visible to `MetaM`. The replay is adapted from Lean's `Lean.Replay` (Copyright (c) 2023 Kim Morrison,
Apache-2.0). R6's final validation used the 4.32.2 kernel, whose fix concerns nested inductive *declarations*; every constant
replayed here was already accepted by that validation, and the only new declarations are Check 2's theorems.
-/

-- As in the vendored Comparator (Comparator/Compare.lean:25-28).
deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

def expectedHeader : String :=
  "{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"8c9756b28d64dab099da31a4c09229a9e6a2ef35\",\"version\":\"4.32.0\"}}}"

def parseFile (path : String) : IO Export.ExportedEnv := do
  let handle ← IO.FS.Handle.mk path .read
  let stream := IO.FS.Stream.ofHandle handle
  let header ← IO.ofExcept <| Json.parse (← stream.getLine)
  unless header == (← IO.ofExcept <| Json.parse expectedHeader) do
    throw <| IO.userError "export metadata does not match the pinned format and environment"
  let items : Export.Parse.M Unit := do
    repeat
      let line ← stream.getLine
      if line.isEmpty then break
      discard <| IO.ofExcept (Json.parse line)
      Export.Parse.parseItem line
  let (_, state) ← Export.Parse.M.run items stream
  return { constMap := state.constMap, constOrder := state.constOrder }

/-! ## Equality up to what the kernel ignores -/

partial def erase : Expr → Expr
  | .mdata _ e => erase e
  | .app f x => .app (erase f) (erase x)
  | .lam _ t b _ => .lam .anonymous (erase t) (erase b) .default
  | .forallE _ t b _ => .forallE .anonymous (erase t) (erase b) .default
  | .letE _ t v b _ => .letE .anonymous (erase t) (erase v) (erase b) false
  | .proj s i e => .proj s i (erase e)
  | e => e

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "defn" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def sameUpToAnnotations (a b : ConstantInfo) : Bool :=
  kindOf a == kindOf b && a.levelParams == b.levelParams && erase a.type == erase b.type &&
  ((a.value? (allowOpaque := true)).map erase == (b.value? (allowOpaque := true)).map erase)

/-! ## Replay through `addDecl` -/

structure RState where
  remaining : NameSet := {}
  pending : NameSet := {}
  ctors : NameSet := {}
  recs : NameSet := {}

partial def replayConst (m : Std.HashMap Name ConstantInfo) (st : IO.Ref RState) (name : Name) : CoreM Unit := do
  let s ← st.get
  unless s.remaining.contains name do return
  st.set { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
  let some ci := m[name]? | unreachable!
  for n in ci.getUsedConstantsAsSet do replayConst m st n
  unless (← st.get).pending.contains name do return
  match ci with
  | .defnInfo i => addDecl (.defnDecl i)
  | .thmInfo i => addDecl (.thmDecl i)
  | .axiomInfo i => addDecl (.axiomDecl i)
  | .opaqueInfo i => addDecl (.opaqueDecl i)
  | .inductInfo i =>
    let all := i.all.map (m[·]!)
    for o in all do st.modify fun s => { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
    let ctorInfo := all.map fun ci => (ci, ci.inductiveVal!.ctors.map (m[·]!))
    for (_, cs) in ctorInfo do for c in cs do for n in c.getUsedConstantsAsSet do replayConst m st n
    let types : List InductiveType := ctorInfo.map fun (ci, cs) =>
      { name := ci.name, type := ci.type, ctors := cs.map fun c => { name := c.name, type := c.type } }
    addDecl (.inductDecl i.levelParams i.numParams types false)
  | .ctorInfo i => st.modify fun s => { s with ctors := s.ctors.insert i.name }
  | .recInfo i => st.modify fun s => { s with recs := s.recs.insert i.name }
  | .quotInfo _ => throwError "unexpected quotient constant outside Init: {name}"
  st.modify fun s => { s with pending := s.pending.erase name }

def replayAll (m : Std.HashMap Name ConstantInfo) : CoreM Unit := do
  let st ← IO.mkRef ({ remaining := m.fold (fun acc n _ => acc.insert n) {} } : RState)
  for (n, _) in m do replayConst m st n
  let s ← st.get
  for n in s.ctors ++ s.recs do
    match (← getEnv).find? n, m[n]? with
    | some a, some b => unless sameUpToAnnotations a b do throwError "generated constructor/recursor differs: {n}"
    | _, _ => throwError "missing generated constructor/recursor: {n}"

/-! ## Traversal with binders and local definitions

A binder's *definition* is its `let` value, or the argument of an applied lambda (how `have`/`assert` facts appear). -/

structure Site where
  lctx : LocalContext
  defs : Std.HashMap FVarId Expr
  head : Expr
  args : Array Expr
  deriving Inhabited

partial def visit (e : Expr) (defs : Std.HashMap FVarId Expr) (pick : Expr → Bool) (acc : IO.Ref (Array Site)) : MetaM Unit := do
  match e with
  | .lam n t b bi =>
    visit t defs pick acc
    withLocalDecl n bi t fun x => visit (b.instantiate1 x) defs pick acc
  | .forallE n t b bi =>
    visit t defs pick acc
    withLocalDecl n bi t fun x => visit (b.instantiate1 x) defs pick acc
  | .letE n t v b _ =>
    visit t defs pick acc; visit v defs pick acc
    withLetDecl n t v fun x => visit (b.instantiate1 x) defs pick acc
  | .mdata _ b => visit b defs pick acc
  | .proj _ _ b => visit b defs pick acc
  | .app .. =>
    let f := e.getAppFn.consumeMData
    let args := e.getAppArgs
    if pick e then acc.modify (·.push { lctx := (← getLCtx), defs, head := f, args })
    for a in args do visit a defs pick acc
    match f with
    | .lam n t b bi =>
      -- an applied lambda: its binder is defined by the first argument
      visit t defs pick acc
      withLocalDecl n bi t fun x =>
        visit (mkAppN (b.instantiate1 x) args[1:]) (defs.insert x.fvarId! args[0]!) pick acc
    | _ => visit f defs pick acc
  | _ => pure ()

/-- The hypotheses reachable from `e`: free variables whose type is a proposition, following local definitions transitively.
    Each is reported with its path (the chain of definitions through which it was reached). -/
partial def reach (e : Expr) (defs : Std.HashMap FVarId Expr) : MetaM (Array (FVarId × List Name) × Array FVarId) := do
  let seen ← IO.mkRef ({} : Std.HashSet FVarId)
  let hyps ← IO.mkRef (#[] : Array (FVarId × List Name))
  let vals ← IO.mkRef (#[] : Array FVarId)
  let rec go (e : Expr) (path : List Name) : MetaM Unit := do
    for id in (collectFVars {} e).fvarIds do
      if (← seen.get).contains id then continue
      seen.modify (·.insert id)
      let d ← id.getDecl
      if ← isProp d.type then hyps.modify (·.push (id, path.reverse))
      else vals.modify (·.push id)
      -- definitions: a let value, or a recorded applied-lambda argument
      if let some v := d.value? then go v (d.userName :: path)
      if let some v := defs[id]? then go v (d.userName :: path)
  go e []
  return (← hyps.get, ← vals.get)

/-! ## Check 2 -/

def arithHeads : List Name :=
  [``HAdd.hAdd, ``HSub.hSub, ``Neg.neg, ``HMul.hMul, ``OfNat.ofNat, ``Nat.cast, ``NatCast.natCast, ``Int.ofNat, ``HPow.hPow,
   ``LT.lt, ``LE.le]

/-- Generalize maximal non-arithmetic subterms that are not free variables. A product of two non-numeral factors is itself an
    atom (linear arithmetic only). Returns the atoms in order of first occurrence. -/
partial def atomsOf (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let e := e.consumeMData
  if e.isFVar || e.isRawNatLit || (e.isAppOf ``OfNat.ofNat) then return acc
  let f := e.getAppFn
  if let .const n _ := f then
    if arithHeads.contains n then
      let args := e.getAppArgs
      if n == ``HMul.hMul && args.size == 6 then
        let (a, b) := (args[4]!, args[5]!)
        let numeral (x : Expr) := x.consumeMData.isAppOf ``OfNat.ofNat || x.consumeMData.isRawNatLit
        unless numeral a || numeral b do
          return if acc.contains e then acc else acc.push e
      -- recurse into the value arguments; type and instance arguments carry no atoms of interest
      let mut acc := acc
      for a in args do
        unless (← isType a) || (← isInstanceArg a) do acc ← atomsOf a acc
      return acc
  return if acc.contains e then acc else acc.push e
where
  isInstanceArg (a : Expr) : MetaM Bool := do
    return (← isClass? (← inferType a)).isSome

structure Proved where
  ok : Bool
  detail : String
  deriving ToJson

def proveClosed (name : Name) (closed : Expr) : MetaM Proved := withLCtx {} {} do
  if closed.hasFVar || closed.hasMVar then return { ok := false, detail := "statement not closed" }
  let mv ← mkFreshExprMVar closed
  try
    let rest ← Term.TermElabM.run' (Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic| intros; omega))))
    unless rest.isEmpty do return { ok := false, detail := "goals remain" }
  catch err => return { ok := false, detail := s!"omega: {(← err.toMessageData.toString).take 300}" }
  let pf ← instantiateMVars mv
  if pf.hasFVar || pf.hasMVar then return { ok := false, detail := "proof not closed" }
  try
    addDecl (.thmDecl { name, levelParams := [], type := closed, value := pf })
    return { ok := true, detail := "kernel accepted" }
  catch err => return { ok := false, detail := s!"kernel rejected: {(← err.toMessageData.toString).take 300}" }

/-- All free variables `e` depends on, including through their types, in local-context order. -/
partial def closure (e : Expr) : MetaM (Array FVarId) := do
  let mut todo := (collectFVars {} e).fvarIds
  let mut seen : Std.HashSet FVarId := {}
  while !todo.isEmpty do
    let id := todo.back!; todo := todo.pop
    if seen.contains id then continue
    seen := seen.insert id
    todo := todo ++ (collectFVars {} (← id.getDecl).type).fvarIds
  let lctx ← getLCtx
  return seen.toArray.qsort fun a b => (lctx.get! a).index < (lctx.get! b).index

structure Check2 where
  statement : String
  original : Proved
  abstraction : Option Proved
  specialization : Option Proved
  atoms : Array String
  deriving ToJson

/-- Replace every `let`-bound variable of `ty` by a fresh variable of the same type, dropping its definition: the statement is
    then quantified over it as a plain value, which is stronger, and no definition can bring a hypothesis into scope. -/
partial def dropDefinitions (ty : Expr) (k : Expr → MetaM α) : MetaM α := do
  let lets ← (collectFVars {} ty).fvarIds.filterM fun id => return (← id.getDecl).isLet
  let rec go (i : Nat) (ty : Expr) : MetaM α :=
    if h : i < lets.size then do
      let d ← lets[i].getDecl
      withLocalDeclD d.userName d.type fun v => go (i + 1) (ty.replaceFVar (mkFVar lets[i]) v)
    else k ty
  go 0 ty

def check2 (tag : String) (ty0 : Expr) (forceAbstraction : Bool) : MetaM Check2 := do
  dropDefinitions (← instantiateMVars ty0) fun ty => do
    let fvs ← closure ty
    if ← fvs.anyM (fun id => do isProp (← id.getDecl).type) then
      let none : Proved := { ok := false, detail := "the statement mentions a proof term; not attempted" }
      return { statement := toString (← ppExpr ty), original := none, abstraction := none, specialization := none, atoms := #[] }
    let closed ← mkForallFVars (fvs.map mkFVar) ty
    let statement := toString (← ppExpr closed)
    let original ← proveClosed (.mkSimple s!"_r6audit_{tag}_original") closed
    if original.ok && !forceAbstraction then
      return { statement, original, abstraction := none, specialization := none, atoms := #[] }
    -- abstraction path
    let atoms ← atomsOf ty #[]
    let atomStrs ← atoms.mapM fun a => return toString (← ppExpr a)
    let rec withAtoms (i : Nat) (vars : Array Expr) (k : Array Expr → MetaM (Option Proved × Option Proved)) :
        MetaM (Option Proved × Option Proved) :=
      if h : i < atoms.size then do
        withLocalDeclD (.mkSimple s!"_atom{i}") (← inferType atoms[i]) fun v => withAtoms (i + 1) (vars.push v) k
      else k vars
    let (abs, spec) ← withAtoms 0 #[] fun vars => do
      let gen := (atoms.zip vars).foldl (fun e (a, v) => e.replace fun x => if x == a then some v else none) ty
      let genFvs ← closure gen
      let genFvs := genFvs.filter fun id => !vars.any (·.fvarId! == id)
      let genClosed ← mkForallFVars (genFvs.map mkFVar ++ vars) gen
      let genName := Name.mkSimple s!"_r6audit_{tag}_generalized"
      let abs ← proveClosed genName genClosed
      unless abs.ok do return (some abs, none)
      -- specialization back to the original statement, kernel-checked
      let body := mkAppN (.const genName []) (genFvs.map mkFVar ++ atoms)
      let specVal ← mkLambdaFVars (fvs.map mkFVar) body
      if specVal.hasFVar then return (some abs, some { ok := false, detail := "specialization not closed" })
      let spec ← try
          addDecl (.thmDecl { name := .mkSimple s!"_r6audit_{tag}_specialized", levelParams := [], type := closed, value := specVal })
          pure { ok := true, detail := "kernel accepted" : Proved }
        catch err => pure { ok := false, detail := s!"kernel rejected: {(← err.toMessageData.toString).take 300}" }
      return (some abs, some spec)
    return { statement, original, abstraction := abs, specialization := spec, atoms := atomStrs }

/-! ## One export -/

structure Hyp where
  name : String
  path : List String
  deriving ToJson

def hypsJson (hs : Array (FVarId × List Name)) : MetaM (Array Hyp) :=
  hs.mapM fun (id, path) => return { name := (← id.getDecl).userName.toString, path := path.map toString }

def classify (hyps : Array Hyp) (c2 : Check2) : String :=
  let sufficient := c2.original.ok || (c2.abstraction.any (·.ok) && c2.specialization.any (·.ok))
  if !sufficient then "sufficiency_not_established"
  else if hyps.isEmpty then "certificate_alone"
  else "sufficient_but_context_referenced"

def auditExport (localName wholeName : Name) (residual : String) (forceAbstraction : Bool) : MetaM Json := do
  let some li := (← getEnv).find? localName | throwError "missing local target {localName}"
  let some wi := (← getEnv).find? wholeName | throwError "missing whole target {wholeName}"
  -- local target: exactly one fold
  let folds ← IO.mkRef #[]
  visit (li.value? (allowOpaque := true)).get! {} (·.isAppOfArity `ProofBroker.TermMode.farkasContradictN 3) folds
  let folds ← folds.get
  unless folds.size == 1 do
    return Json.mkObj [("local", Json.mkObj [("locatable", false), ("reason", toJson s!"{folds.size} fold applications")])]
  let fold := folds[0]!
  withLCtx fold.lctx #[] do
    let hpos := fold.args[2]!
    let hposTy ← inferType hpos
    let pp := toString (← ppExpr hposTy)
    let (localHyps, localVals) ← reach hpos fold.defs
    let localHypsJ ← hypsJson localHyps
    let c2 ← check2 "c" hposTy forceAbstraction
    -- which of the local theorem's parameters does hpos reach? (the outermost binders, in order)
    let nParams ← forallTelescope li.type fun xs _ => pure xs.size
    let paramIds := (fold.lctx.foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d.fvarId)[:nParams].toArray
    let reached := (localHyps.map (·.1)) ++ localVals
    let reachedParams := (List.range nParams).filter fun i => reached.contains paramIds[i]!
    let internal := localHyps.filter fun (id, _) => !paramIds.contains id
    let internalJ := (← hypsJson internal).map fun h => { h with path := "internal to the local proof" :: h.path }
    -- whole target: exactly one reference to the local theorem, fully applied
    let refs ← IO.mkRef #[]
    withLCtx {} {} do
      visit (wi.value? (allowOpaque := true)).get! {} (fun e => e.getAppFn.consumeMData.isConstOf localName) refs
    let refs ← refs.get
    let wholeJ ← if refs.size != 1 || refs[0]!.args.size != nParams then
        pure <| Json.mkObj [("locatable", false), ("reason", toJson s!"{refs.size} references; arity {refs.map (·.args.size)} for {nParams} parameters")]
      else
        let r := refs[0]!
        withLCtx r.lctx #[] do
          let mut hs : Array Hyp := #[]
          for i in reachedParams do
            let (h, _) ← reach r.args[i]! r.defs
            for (id, path) in h do
              hs := hs.push { name := (← id.getDecl).userName.toString,
                              path := s!"parameter {i} of {localName}" :: path.map toString }
          let all := internalJ ++ hs
          pure <| Json.mkObj [("locatable", true), ("hypotheses", toJson all),
            ("internal_to_local_proof", toJson internalJ), ("classification", toJson (classify all c2))]
    return Json.mkObj [
      ("local", Json.mkObj [("locatable", true), ("residual_goal", toJson pp), ("binding_matches_residual", toJson (pp == residual)),
                            ("hypotheses", toJson localHypsJ), ("classification", toJson (classify localHypsJ c2))]),
      ("whole", wholeJ),
      ("check2", toJson c2)]

def main (args : List String) : IO UInt32 := do
  let (flags, args) := args.partition (·.startsWith "--")
  let [path, localName, wholeName, residualPath, reportPath] := args
    | IO.eprintln "usage: r6-qualification-audit [--force-abstraction] EXPORT LOCAL WHOLE RESIDUAL.txt REPORT.json"; return 2
  let forceAbstraction := flags.contains "--force-abstraction"
  let exp ← parseFile path
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let base ← importModules #[{ module := `Init }] {} (loadExts := true)
  let mut identical := 0
  let mut annotated := 0
  let mut differing := #[]
  let mut added : Std.HashMap Name ConstantInfo := {}
  for (n, ci) in exp.constMap do
    match base.find? n with
    | some ci' =>
      if ci' == ci then identical := identical + 1
      else if sameUpToAnnotations ci ci' then annotated := annotated + 1
      else differing := differing.push n
    | none => added := added.insert n ci
  unless differing.isEmpty do
    IO.FS.writeFile reportPath ((Json.mkObj [("refused", toJson s!"constants differ from Init beyond annotations: {differing[:10]}")]).pretty ++ "\n")
    return 1
  let residual ← IO.FS.readFile residualPath
  let ctx : Core.Context := { fileName := "<audit>", fileMap := default, maxHeartbeats := 0,
                              options := Options.empty.setBool `Elab.async false }
  let (report, _) ← (do
      replayAll added
      let r ← auditExport localName.toName wholeName.toName residual.trimAsciiEnd.toString forceAbstraction
      return r
    : MetaM Json).run' {} |>.toIO ctx { env := base }
  let env := Json.mkObj [("init_shared_identical", toJson identical), ("init_shared_equal_up_to_annotations", toJson annotated),
                         ("replayed_through_addDecl", toJson added.size), ("lean", toJson Lean.versionString)]
  IO.FS.writeFile reportPath ((Json.mkObj [("environment", env), ("audit", report)]).pretty ++ "\n")
  return 0

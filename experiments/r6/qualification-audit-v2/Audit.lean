import Lean
import Export.Parse
open Lean Meta Elab

/-!
# R6 qualification 1 audit, amended (build revision 3, amendment 1)

Build revision 2 of the tool specified by `experiments/r6/R6-QUALIFICATION-1-AUDIT-PROPOSAL.md` (revision 2), locked as
`qualification-audit-v1`, amended by `experiments/r6/R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md` (revision 3):
* **Rule B:** the local declaration's parameters are established by a lockstep walk of its type and value (`walk`), never guessed
  from the fold's context; a failed walk is `parameters_unverified` and the whole target is not locatable.
* **Rule A:** binding up to the run's recorded renaming (`--rename=`), every row verified (`verifyRenaming`), applied by binder
  identity: `matches_residual`, `matches_residual_after_renaming`, `rename_unverified` or `residual_mismatch`.
Everything else is build revision 2's. For one `lean4export` export it reports,
for the broker's final positivity step `hpos : 0 < s` in `ProofBroker.TermMode.farkasContradictN s sumProof hpos`:

* **Check 1 (dependency):** which hypotheses `hpos` refers to, directly or through local definitions (`let` values and the
  arguments of applied lambdas), each with its path; for the whole target, mapped through the arguments at its single reference
  to the local theorem.
* **Check 2 (sufficiency):** whether a kernel-accepted theorem exists whose type is exactly the *original* quantified statement:
  `hpos`'s type closed over its free variables, local definitions retained. `omega` runs only in an empty context. Dropping
  definitions (quantifying a `let`-bound value as a plain variable) and generalizing non-arithmetic subterms are both
  generalizations; each counts only through a kernel-checked specialization back.
* **Binding:** in real mode, `hpos`'s pretty-printed type must equal the run's retained residual goal, or no sufficiency
  classification is made for either target. Synthetic controls run in an explicit mode without a retained residual.

## Environment

Built with Lean 4.32.2, the kernel of R6's final validation. `Init` is imported with its extensions. Every export constant `Init`
also has must equal it in **every field** once expressions are erased of what the kernel ignores (metadata, binder names and
info, the `let` `nonDep` hint), recursor-rule right-hand sides included; otherwise the audit refuses. The export's remaining
constants are replayed through `addDecl`, so each is kernel-checked and visible to `MetaM`. The replay is adapted from Lean's
`Lean.Replay` (Copyright (c) 2023 Kim Morrison, Apache-2.0).
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

/-! ## Equality up to what the kernel ignores, over the complete `ConstantInfo` -/

partial def erase : Expr → Expr
  | .mdata _ e => erase e
  | .app f x => .app (erase f) (erase x)
  | .lam _ t b _ => .lam .anonymous (erase t) (erase b) .default
  | .forallE _ t b _ => .forallE .anonymous (erase t) (erase b) .default
  | .letE _ t v b _ => .letE .anonymous (erase t) (erase v) (erase b) false
  | .proj s i e => .proj s i (erase e)
  | e => e

/-- Every expression in the declaration erased; every other field kept, and compared by `==`. -/
def eraseCI : ConstantInfo → ConstantInfo
  | .axiomInfo v => .axiomInfo { v with type := erase v.type }
  | .defnInfo v => .defnInfo { v with type := erase v.type, value := erase v.value }
  | .thmInfo v => .thmInfo { v with type := erase v.type, value := erase v.value }
  | .opaqueInfo v => .opaqueInfo { v with type := erase v.type, value := erase v.value }
  | .quotInfo v => .quotInfo { v with type := erase v.type }
  | .inductInfo v => .inductInfo { v with type := erase v.type }
  | .ctorInfo v => .ctorInfo { v with type := erase v.type }
  | .recInfo v => .recInfo { v with type := erase v.type, rules := v.rules.map fun r => { r with rhs := erase r.rhs } }

def sameUpToAnnotations (a b : ConstantInfo) : Bool := eraseCI a == eraseCI b

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
      if let some v := d.value? then go v (d.userName :: path)
      if let some v := defs[id]? then go v (d.userName :: path)
  go e []
  return (← hyps.get, ← vals.get)

/-! ## Check 2 -/

def arithHeads : List Name :=
  [``HAdd.hAdd, ``HSub.hSub, ``Neg.neg, ``HMul.hMul, ``OfNat.ofNat, ``Nat.cast, ``NatCast.natCast, ``Int.ofNat, ``HPow.hPow,
   ``LT.lt, ``LE.le]

/-- Maximal non-arithmetic subterms that are not free variables. A product of two non-numeral factors is itself an atom. -/
partial def atomsOf (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let e := e.consumeMData
  if e.isFVar || e.isRawNatLit || (e.isAppOf ``OfNat.ofNat) then return acc
  let f := e.getAppFn
  if let .const n _ := f then
    if arithHeads.contains n then
      let args := e.getAppArgs
      if n == ``HMul.hMul && args.size == 6 then
        let numeral (x : Expr) := x.consumeMData.isAppOf ``OfNat.ofNat || x.consumeMData.isRawNatLit
        unless numeral args[4]! || numeral args[5]! do
          return if acc.contains e then acc else acc.push e
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

def addTheorem (name : Name) (type value : Expr) : MetaM Proved := do
  if type.hasFVar || type.hasMVar || value.hasFVar || value.hasMVar then return { ok := false, detail := "not closed" }
  try
    addDecl (.thmDecl { name, levelParams := [], type, value })
    return { ok := true, detail := "kernel accepted" }
  catch err => return { ok := false, detail := s!"kernel rejected: {(← err.toMessageData.toString).take 300}" }

/-- `omega` on a closed statement, in an empty local context; the proof is then added through the kernel. -/
def proveClosed (name : Name) (closed : Expr) : MetaM Proved := withLCtx {} {} do
  if closed.hasFVar || closed.hasMVar then return { ok := false, detail := "statement not closed" }
  let mv ← mkFreshExprMVar closed
  try
    let rest ← Term.TermElabM.run' (Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic| intros; omega))))
    unless rest.isEmpty do return { ok := false, detail := "goals remain" }
  catch err => return { ok := false, detail := s!"omega: {(← err.toMessageData.toString).take 300}" }
  addTheorem name closed (← instantiateMVars mv)

/-- All free variables `e` depends on, through types and (when `values`) through `let` values, in local-context order. -/
partial def closure (e : Expr) (values : Bool) : MetaM (Array FVarId) := do
  let mut todo := (collectFVars {} e).fvarIds
  let mut seen : Std.HashSet FVarId := {}
  while !todo.isEmpty do
    let id := todo.back!; todo := todo.pop
    if seen.contains id then continue
    seen := seen.insert id
    let d ← id.getDecl
    todo := todo ++ (collectFVars {} d.type).fvarIds
    if values then if let some v := d.value? then todo := todo ++ (collectFVars {} v).fvarIds
  let lctx ← getLCtx
  return seen.toArray.qsort fun a b => (lctx.get! a).index < (lctx.get! b).index

/-- Replace each `let`-bound variable by a fresh plain variable of the same type (its definition dropped). -/
partial def withPlainVars (lets : Array FVarId) (ty : Expr) (k : Expr → Array (FVarId × FVarId) → MetaM α) : MetaM α := do
  let rec go (i : Nat) (ty : Expr) (repl : Array (FVarId × FVarId)) : MetaM α :=
    if h : i < lets.size then do
      let d ← lets[i].getDecl
      withLocalDeclD d.userName d.type fun v => go (i + 1) (ty.replaceFVar (mkFVar lets[i]) v) (repl.push (lets[i], v.fvarId!))
    else k ty repl
  go 0 ty #[]

structure Check2 where
  statement : String                       -- the original quantified statement, definitions retained
  definitions_dropped : Array String
  attempted : String                       -- the statement `omega` was asked for (the original, or its generalization)
  direct : Proved
  abstraction : Option Proved
  atoms : Array String
  specialization_atoms : Option Proved     -- the atom generalization back to the attempted statement
  specialization_definitions : Option Proved  -- the attempted statement back to the original (when definitions were dropped)
  established : Bool                       -- a kernel-accepted theorem whose type is the original statement exists
  deriving ToJson

def check2 (tag : String) (hposTy : Expr) (forceAbstraction : Bool) : MetaM Check2 := do
  let ty ← instantiateMVars hposTy
  let fvsO ← closure ty (values := true)
  let original ← mkForallFVars (fvsO.map mkFVar) ty
  let statement := toString (← ppExpr original)
  let origName := Name.mkSimple s!"_r6audit_{tag}_original"
  let lets ← fvsO.filterM fun id => return (← id.getDecl).isLet
  withPlainVars lets ty fun tyA repl => do
    let fvsA ← closure tyA (values := false)
    let dropped ← lets.mapM fun id => return toString (← id.getDecl).userName
    let fail (why : String) : MetaM Check2 := return {
      statement, definitions_dropped := dropped, attempted := "", direct := { ok := false, detail := why },
      abstraction := none, atoms := #[], specialization_atoms := none, specialization_definitions := none, established := false }
    if ← fvsA.anyM (fun id => do isProp (← id.getDecl).type) then return ← fail "the statement mentions a proof term; not attempted"
    let attemptedE ← mkForallFVars (fvsA.map mkFVar) tyA
    let attempted := toString (← ppExpr attemptedE)
    -- when nothing was dropped, the attempted statement is the original, and is proved under the original's name
    let attName := if lets.isEmpty then origName else Name.mkSimple s!"_r6audit_{tag}_attempted"
    let direct ← proveClosed attName attemptedE
    let mut proof? : Option Name := if direct.ok then some attName else none
    let mut abs? : Option Proved := none
    let mut specA? : Option Proved := none
    let mut atomStrs := #[]
    if !direct.ok || forceAbstraction then
      let atoms ← atomsOf tyA #[]
      atomStrs ← atoms.mapM fun a => return toString (← ppExpr a)
      let genName := Name.mkSimple s!"_r6audit_{tag}_atoms"
      let viaName := if direct.ok then Name.mkSimple s!"_r6audit_{tag}_via_atoms" else attName
      let rec withAtoms (i : Nat) (vars : Array Expr) (k : Array Expr → MetaM (Proved × Option Proved)) : MetaM (Proved × Option Proved) :=
        if h : i < atoms.size then do
          withLocalDeclD (.mkSimple s!"_atom{i}") (← inferType atoms[i]) fun v => withAtoms (i + 1) (vars.push v) k
        else k vars
      let (abs, specA) ← withAtoms 0 #[] fun vars => do
        let gen := (atoms.zip vars).foldl (fun e (a, v) => e.replace fun x => if x == a then some v else none) tyA
        let genFvs := (← closure gen (values := false)).filter fun id => !vars.any (·.fvarId! == id)
        let abs ← proveClosed genName (← mkForallFVars (genFvs.map mkFVar ++ vars) gen)
        unless abs.ok do return (abs, none)
        -- the atoms back: instantiate the generalized theorem, kernel-checked against the attempted statement
        let value ← mkLambdaFVars (fvsA.map mkFVar) (mkAppN (.const genName []) (genFvs.map mkFVar ++ atoms))
        return (abs, some (← addTheorem viaName attemptedE value))
      abs? := some abs; specA? := specA
      if proof?.isNone && abs.ok && (specA.any (·.ok)) then proof? := some viaName
    -- the dropped definitions back: instantiate the attempted theorem at the let-bound variables, checked against the original
    let mut specD? : Option Proved := none
    let mut established := false
    match proof? with
    | none => pure ()
    | some thm =>
      if lets.isEmpty then established := true
      else
        let args := fvsA.map fun id => mkFVar ((repl.find? (·.2 == id)).map (·.1) |>.getD id)
        let value ← mkLambdaFVars (fvsO.map mkFVar) (mkAppN (.const thm []) args)
        let specD ← addTheorem origName original value
        specD? := some specD; established := specD.ok
    return { statement, definitions_dropped := dropped, attempted, direct, abstraction := abs?, atoms := atomStrs,
             specialization_atoms := specA?, specialization_definitions := specD?, established }

/-! ## One export -/

structure Hyp where
  name : String
  path : List String
  deriving ToJson

def hypsJson (hs : Array (FVarId × List Name)) : MetaM (Array Hyp) :=
  hs.mapM fun (id, path) => return { name := (← id.getDecl).userName.toString, path := path.map toString }

def classify (bound : Bool) (hyps : Array Hyp) (c2 : Check2) : String :=
  if !bound then "unbound_residual_mismatch"
  else if !c2.established then "sufficiency_not_established"
  else if hyps.isEmpty then "certificate_alone"
  else "sufficient_but_context_referenced"

/-! ## Amendment 1, rule B: the declaration's parameters, by a lockstep walk of the local's type and value -/

structure Walked where
  params : Array FVarId := #[]           -- the declaration's parameters, in order
  telescope : Array FVarId := #[]        -- every telescope entry, parameters and declaration `let`s, in order
  defs : Std.HashMap FVarId Expr := {}   -- internal applied-lambda definitions
  body : Expr := default

/-- The frozen walk. Metadata is transparent, nothing is reduced, and the first matching form is taken: (1) the end; (2) an applied
    lambda, internal, the type staying; (3) a parameter, `∀` against `λ` with definitionally equal binder types; (4) a declaration
    `let`, matched by type and value; (5) a value-only `let`, internal, the type staying; anything else fails. `k` runs in the
    walk's context, so the parameters keep their identities through to the fold. -/
partial def walk (T V : Expr) (w : Walked) (k : Walked → MetaM α) (fail : String → MetaM α) : MetaM α := do
  let T := T.consumeMData
  let V := V.consumeMData
  if !(T.isForall || T.isLet) then return ← k { w with body := V }
  if V.isApp then
    if let .lam n t b bi := V.getAppFn.consumeMData then
      let args := V.getAppArgs
      return ← withLocalDecl n bi t fun q =>
        walk T (mkAppN (b.instantiate1 q) args[1:]) { w with defs := w.defs.insert q.fvarId! args[0]! } k fail
  match T, V with
  | .forallE _ a t' _, .lam n a' v' bi =>
    unless ← isDefEq a a' do return ← fail s!"parameter {w.params.size}: the binder types are not definitionally equal"
    withLocalDecl n bi a' fun x =>
      walk (t'.instantiate1 x) (v'.instantiate1 x)
        { w with params := w.params.push x.fvarId!, telescope := w.telescope.push x.fvarId! } k fail
  | .letE _ a v t' _, .letE n a' v' b' _ =>
    unless (← isDefEq a a') && (← isDefEq v v') do return ← fail "a declaration let does not match the value's"
    withLetDecl n a' v' fun x =>
      walk (t'.instantiate1 x) (b'.instantiate1 x) { w with telescope := w.telescope.push x.fvarId! } k fail
  | .forallE .., .letE n b a v' _ =>
    withLetDecl n b a fun q => walk T (v'.instantiate1 q) w k fail
  | _, _ => fail "the value does not have the form its type requires"

/-! ## Amendment 1, rule A: binding up to the run's recorded renaming -/

structure RenameRow where
  index : Nat
  original_name : String
  search_name : String
  fvar_in_original : Bool
  deriving FromJson, ToJson

structure ContextEntry where
  index : Nat
  name : String
  included_in_telescope : Bool
  deriving FromJson, ToJson, Inhabited

/-- The sealed rename rows of a run (those whose names differ) and the site's frozen context. -/
structure RenameInput where
  rows : Array RenameRow
  context : Array ContextEntry
  deriving FromJson, ToJson

/-- Every row verified (correspondence, unique sources, distinct destinations, global injectivity), or the first failure. -/
def verifyRenaming (input : RenameInput) (w : Walked) (hposTy : Expr) : MetaM (Except String (Array (FVarId × Name))) := do
  let included := (input.context.filter (·.included_in_telescope)).qsort (·.index < ·.index)
  let indices := input.rows.map (·.index)
  if indices.toList.eraseDups.length != indices.size then return .error "two rows name the same index"
  let dests := input.rows.map (·.search_name)
  if dests.toList.eraseDups.length != dests.size then return .error "two rows share a search name"
  let mut renames : Array (FVarId × Name) := #[]
  for row in input.rows do
    unless row.fvar_in_original do return .error s!"row {row.index}: not a variable of the original context"
    let some pos := included.findIdx? (·.index == row.index) | return .error s!"row {row.index}: no telescope entry at that index"
    unless included[pos]!.name == row.original_name do return .error s!"row {row.index}: the frozen context names {included[pos]!.name}"
    unless pos < w.telescope.size do return .error s!"row {row.index}: telescope position {pos} beyond the walked telescope"
    let fv := w.telescope[pos]!
    unless (← fv.getDecl).userName.toString == row.original_name do
      return .error s!"row {row.index}: the export's binder at position {pos} is {(← fv.getDecl).userName}"
    if renames.any (·.1 == fv) then return .error s!"row {row.index}: two rows reach the same binder"
    renames := renames.push (fv, Name.mkSimple row.search_name)
  let lctx ← getLCtx
  for (fv, n) in renames do
    for d in lctx do
      if d.fvarId != fv && !renames.any (·.1 == d.fvarId) && d.userName == n then
        return .error s!"search name {n} already names another binder"
  let shown ← (collectFVars {} hposTy).fvarIds.mapM fun id => do
    return ((renames.find? (·.1 == id)).map (·.2)).getD (← id.getDecl).userName
  if shown.toList.eraseDups.length != shown.size then return .error "after renaming, two binders in the goal share a name"
  return .ok renames

/-! ## One export -/

def auditExport (localName wholeName : Name) (residual : Option String) (rename? : Option RenameInput) (forceAbstraction : Bool)
    : MetaM Json := do
  let some li := (← getEnv).find? localName | throwError "missing local target {localName}"
  unless (← getEnv).contains wholeName do throwError "missing whole target {wholeName}"
  let value := (li.value? (allowOpaque := true)).get!
  walk li.type value {} (fun w => body (some w) none) (fun why => withLCtx {} {} (body none (some why)))
where
  body (walked : Option Walked) (walkFailure : Option String) : MetaM Json := do
    let some li := (← getEnv).find? localName | throwError "missing local target {localName}"
    let some wi := (← getEnv).find? wholeName | throwError "missing whole target {wholeName}"
    let folds ← IO.mkRef #[]
    let pick := (·.isAppOfArity `ProofBroker.TermMode.farkasContradictN 3)
    match walked with
    | some w => visit w.body w.defs pick folds
    | none => visit (li.value? (allowOpaque := true)).get! {} pick folds
    let folds ← folds.get
    let paramsJ := match walked, walkFailure with
      | some w, _ => Json.mkObj [("established", toJson true), ("count", toJson w.params.size)]
      | none, why => Json.mkObj [("established", toJson false), ("reason", toJson s!"parameters_unverified: {why.getD ""}")]
    unless folds.size == 1 do
      return Json.mkObj [("parameters", paramsJ),
        ("local", Json.mkObj [("locatable", false), ("reason", toJson s!"{folds.size} fold applications")])]
    let fold := folds[0]!
    withLCtx fold.lctx #[] do
      let hpos := fold.args[2]!
      let hposTy ← inferType hpos
      let pp := toString (← ppExpr hposTy)
      -- binding (amendment 1, rule A): in real mode the audited term must be the run's; anything but the first two values withholds
      -- every sufficiency classification
      let (bound, binding, renameJ) ← match residual with
        | none => pure (true, "not_applicable_synthetic", Json.null)
        | some r =>
          if pp == r then pure (true, "matches_residual", Json.null)
          else match rename? with
            | none => pure (false, "residual_mismatch", Json.null)
            | some input =>
              match walked with
              | none => pure (false, "rename_unverified", toJson "the declaration's parameters are unverified")
              | some w =>
                match ← verifyRenaming input w hposTy with
                | .error why => pure (false, "rename_unverified", toJson why)
                | .ok renames =>
                  let lctx' := renames.foldl (fun l (fv, n) => l.setUserName fv n) (← getLCtx)
                  let pp' := toString (← withLCtx lctx' #[] (ppExpr hposTy))
                  let detail := Json.mkObj [("renamed_print", toJson pp'), ("rows", toJson input.rows)]
                  pure (if pp' == r then (true, "matches_residual_after_renaming", detail) else (false, "residual_mismatch", detail))
      let (localHyps, localVals) ← reach hpos fold.defs
      let localHypsJ ← hypsJson localHyps
      let c2 ← check2 "c" hposTy forceAbstraction
      let wholeJ ← match walked with
        | none => pure <| Json.mkObj [("locatable", false), ("reason", toJson s!"parameters_unverified: {walkFailure.getD ""}"),
                                      ("classification", toJson "not_locatable")]
        | some w => do
          let params := w.params
          let reached := (localHyps.map (·.1)) ++ localVals
          let reachedParams := (List.range params.size).filter fun i => reached.contains params[i]!
          let internal := localHyps.filter fun (id, _) => !params.contains id
          let internalJ := (← hypsJson internal).map fun h => { h with path := "internal to the local proof" :: h.path }
          let refs ← IO.mkRef #[]
          withLCtx {} {} do
            visit (wi.value? (allowOpaque := true)).get! {} (fun e => e.getAppFn.consumeMData.isConstOf localName) refs
          let refs ← refs.get
          if refs.size != 1 || refs[0]!.args.size != params.size then
            pure <| Json.mkObj [("locatable", false),
              ("reason", toJson s!"{refs.size} references; arity {refs.map (·.args.size)} for {params.size} parameters"),
              ("classification", toJson "not_locatable")]
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
                ("internal_to_local_proof", toJson internalJ), ("classification", toJson (classify bound all c2))]
      return Json.mkObj [
        ("binding", toJson binding), ("binding_detail", renameJ), ("parameters", paramsJ),
        ("local", Json.mkObj [("locatable", true), ("residual_goal", toJson pp), ("hypotheses", toJson localHypsJ),
                              ("classification", toJson (classify bound localHypsJ c2))]),
        ("whole", wholeJ),
        ("check2", toJson c2)]

def main (args : List String) : IO UInt32 := do
  let (flags, args) := args.partition (·.startsWith "--")
  let [path, localName, wholeName, residualPath, reportPath] := args
    | IO.eprintln "usage: r6-qualification-audit [--synthetic] [--force-abstraction] [--rename=RENAME.json] EXPORT LOCAL WHOLE RESIDUAL.txt|- REPORT.json"; return 2
  let rename? ← match flags.find? (·.startsWith "--rename=") with
    | none => pure none
    | some f =>
      let raw ← IO.FS.readFile (f.drop "--rename=".length).toString
      match Json.parse raw >>= fromJson? with
      | .ok (input : RenameInput) => pure (some input)
      | .error e => IO.eprintln s!"rename input: {e}"; return 2
  let forceAbstraction := flags.contains "--force-abstraction"
  let synthetic := flags.contains "--synthetic"
  if !synthetic && residualPath == "-" then IO.eprintln "a retained residual goal is required outside --synthetic"; return 2
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
  let residual ← if synthetic then pure none else some <$> (·.trimAsciiEnd.toString) <$> IO.FS.readFile residualPath
  let ctx : Core.Context := { fileName := "<audit>", fileMap := default, maxHeartbeats := 0,
                              options := Options.empty.setBool `Elab.async false }
  let (report, _) ← (do
      replayAll added
      auditExport localName.toName wholeName.toName residual rename? forceAbstraction
    : MetaM Json).run' {} |>.toIO ctx { env := base }
  let env := Json.mkObj [("init_shared_identical", toJson identical), ("init_shared_equal_up_to_annotations", toJson annotated),
                         ("replayed_through_addDecl", toJson added.size), ("lean", toJson Lean.versionString),
                         ("mode", toJson (if synthetic then "synthetic" else "real"))]
  IO.FS.writeFile reportPath ((Json.mkObj [("environment", env), ("audit", report)]).pretty ++ "\n")
  return 0

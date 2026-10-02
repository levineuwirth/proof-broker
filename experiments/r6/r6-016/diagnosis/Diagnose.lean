import AuditCore
open Lean Meta Elab

/-!
# R6-016: the bounded diagnosis of l070 draw 5

`experiments/r6/R6-016-PROPOSAL.md`, revision 2, section 4. One input: a `lean4export` export, and its local target. It is read
exactly as `qualification-audit-v2`'s program reads one: `AuditCore` is that program's `Audit.lean`, byte for byte, without its
`main` (the build checks this). Its parsing, its comparison with `Init`, its replay through `addDecl`, its fold location and its
atoms (`atomsOf`: maximal non-arithmetic subterms, a product of two non-numeral factors itself an atom) are used unchanged.

**The pairs.** In the local target's single fold `farkasContradictN s _ hpos`, every pair of atoms of `s` that print identically
under the default options but are not equal as expressions, after instantiating metavariables. For each pair, every attempt, in
order:
1. **printed:** the default printer (equal, by selection), and `pp.all`;
2. **syntactic:** `Expr` equality after instantiating metavariables; equality up to metadata; where they differ, the first
   differing subterm, its path, and both sides under `pp.all`. This is an observation, never a classification of distinctness;
3. **definitional:** `isDefEq` at reducible, instances and default transparency, each without and with `zetaDelta`; and in the
   kernel, `∀ xs, a = b := fun xs => rfl`, closed over the pair's free variables, definitions retained;
4. **arithmetic:** `∀ xs, a = b`, closed, in an empty context, by `intros; omega` and, separately, by `intros; grobner` (`grind`'s
   commutative-ring solver alone), each proof kernel-checked;
5. **a counterexample:** each free variable of type ℕ or ℤ at the numerals 0 to 3, definitions unfolded, and every instance of
   `a ≠ b` decided by `decide`, kernel-checked. A free variable of another type, a proof term, or more than six variables
   refuses.

**Outcomes** of 3 to 5: `established` (a kernel-accepted proof); `refused` (the tactic or check rejected the statement as outside
what it handles, with its message); `resource_exhausted` (heartbeats, recursion depth, or the kernel's own limits, with the
limits); `unsuccessful` (it ran to completion without a proof). Each attempt is one guarded unit (`guarded`, `counterexample`):
an exception at any step of it, building its statement included, becomes its outcome and never escapes. A meta-level `isDefEq`
is `established` only when the kernel accepts the same `rfl` proof. A failed proof is never a proof of the opposite.
`DiagnoseTest.lean`, run by the build, checks this at recursion limits from 1 upward.

**No classification is made here.** The driver computes it from these outcomes (`diagnose_l070.classify`), and the analysis
recomputes it.
-/

namespace R6016Diagnosis

/-- The heartbeat limit for each meta-level attempt, in thousands (twice Lean's default), counted from the attempt's start.
    The replay itself is unlimited, as in the audit. Recorded in the report. -/
def heartbeats : Nat := 400000

/-- One attempt, with its own heartbeat budget. -/
def withLimit (x : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeats * 1000 }) <| withCurrHeartbeats x

def transparencyName : TransparencyMode → String
  | .all => "all" | .default => "default" | .instances => "instances" | .reducible => "reducible" | .none => "none"

/-- Free variables in the counterexample's domain: at most this many, each at 0 to 3. -/
def maxVariables : Nat := 6

structure Attempt where
  outcome : String
  detail : String := ""
  deriving ToJson

def established (detail : String) : Attempt := { outcome := "established", detail }

/-- The kernel check of a closed theorem, without adding it. -/
def kernelCheck (name : Name) (type value : Expr) : MetaM Attempt := do
  if type.hasFVar || type.hasMVar || value.hasFVar || value.hasMVar then return { outcome := "refused", detail := "not closed" }
  let decl := Declaration.thmDecl { name, levelParams := [], type, value }
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl with
  | .ok _ => return established "kernel accepted"
  | .error ex =>
    let msg := ((← (ex.toMessageData (← getOptions)).toString).take 300).toString
    match ex with
    | .deterministicTimeout | .excessiveMemory | .deepRecursion => return { outcome := "resource_exhausted", detail := msg }
    | _ => return { outcome := "unsuccessful", detail := s!"kernel rejected: {msg}" }

/-- The limits in force, for a `resource_exhausted` outcome's detail. -/
def limits : MetaM String :=
  return s!"maxHeartbeats {heartbeats} per attempt, maxRecDepth {(← readThe Core.Context).maxRecDepth}"

/-- An exception's message; printing it may itself exhaust a limit. -/
def message (ex : Exception) : MetaM String :=
  tryCatchRuntimeEx (return ((← ex.toMessageData.toString).take 300).toString) fun _ => return "<message not printable>"

/-- A meta-level exception as an outcome: a runtime limit (heartbeats, recursion depth) is `resource_exhausted`, with the limits;
    a tactic's own failure `unsuccessful`; anything else `refused`. -/
def fromException (ex : Exception) (ownFailure : String → Bool := fun _ => false) : MetaM Attempt := do
  let msg ← message ex
  if ex.isRuntime then return { outcome := "resource_exhausted", detail := s!"{msg} ({← limits})" }
  if ownFailure msg then return { outcome := "unsuccessful", detail := msg }
  return { outcome := "refused", detail := msg }

/-- One complete attempt, with its own heartbeat budget. Any exception, at any step of it, becomes its outcome. -/
def guarded (x : MetaM Attempt) (ownFailure : String → Bool := fun _ => false) : MetaM Attempt :=
  tryCatchRuntimeEx (withLimit x) (fromException · ownFailure)

def attemptJson (r : Attempt) : Json := Json.mkObj [("outcome", toJson r.outcome), ("detail", toJson r.detail)]

partial def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | .app f x => .app (stripMData f) (stripMData x)
  | .lam n t b bi => .lam n (stripMData t) (stripMData b) bi
  | .forallE n t b bi => .forallE n (stripMData t) (stripMData b) bi
  | .letE n t v b nd => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .proj s i e => .proj s i (stripMData e)
  | e => e

/-- The first differing subterm, depth first, function before argument: its path and both sides. -/
partial def firstDifference (a b : Expr) (path : Array String := #[]) : Option (Array String × Expr × Expr) :=
  if a == b then none else
  match a, b with
  | .app f x, .app g y => (firstDifference f g (path.push "fn")).orElse fun _ => firstDifference x y (path.push "arg")
  | .mdata m x, .mdata n y => if m == n then firstDifference x y (path.push "mdata") else some (path, a, b)
  | .lam _ t x _, .lam _ u y _ | .forallE _ t x _, .forallE _ u y _ =>
    (firstDifference t u (path.push "binder_type")).orElse fun _ => firstDifference x y (path.push "body")
  | .letE _ t v x _, .letE _ u w y _ =>
    ((firstDifference t u (path.push "let_type")).orElse fun _ => firstDifference v w (path.push "let_value")).orElse
      fun _ => firstDifference x y (path.push "body")
  | .proj s i x, .proj s' i' y => if s == s' && i == i' then firstDifference x y (path.push "proj") else some (path, a, b)
  | _, _ => some (path, a, b)

def ppAll (e : Expr) : MetaM String :=
  if e.hasLooseBVars then return toString e
  else return toString (← withOptions (fun o => o.setBool `pp.all true) (ppExpr e))

/-- `a = b`, closed over the free variables it depends on, definitions retained; and those variables. -/
def closedEq (a b : Expr) : MetaM (Expr × Array FVarId) := do
  let eq ← mkEq a b
  let fvs ← closure eq (values := true)
  return (← mkForallFVars (fvs.map mkFVar) eq, fvs)

def kernelRfl (tag : String) (a b : Expr) : MetaM Attempt := guarded do
  let (stmt, fvs) ← closedEq a b
  kernelCheck (.mkSimple s!"_r6016_{tag}_rfl") stmt (← mkLambdaFVars (fvs.map mkFVar) (← mkEqRefl a))

def defeqAt (t : TransparencyMode) (zetaDelta : Bool) (a b : Expr) (kernel : Attempt) : MetaM Json := do
  let attempt ← guarded do
    let ok ← withNewMCtxDepth <| withTransparency t <| withConfig (fun c => { c with zetaDelta }) <| isDefEq a b
    if !ok then return { outcome := "unsuccessful", detail := "isDefEq false" }
    if kernel.outcome == "established" then return established "isDefEq true; the kernel accepts rfl"
    return { outcome := "unsuccessful", detail := s!"isDefEq true; the kernel did not confirm ({kernel.outcome})" }
  return Json.mkObj [("transparency", toJson (transparencyName t)), ("zeta_delta", toJson zetaDelta),
                     ("outcome", toJson attempt.outcome), ("detail", toJson attempt.detail)]

/-- A tactic on the closed statement, in an empty local context; the proof kernel-checked. One complete attempt. -/
def byTactic (tag : String) (stmt : Expr) (tac : TSyntax `tactic) (ownFailure : String → Bool) : MetaM Attempt :=
  guarded (ownFailure := ownFailure) <| withLCtx {} {} do
    if stmt.hasFVar || stmt.hasMVar then return { outcome := "refused", detail := "statement not closed" }
    let mv ← mkFreshExprMVar stmt
    let rest ← Term.TermElabM.run' (Tactic.run mv.mvarId! (Tactic.evalTactic tac))
    unless rest.isEmpty do return { outcome := "unsuccessful", detail := "goals remain" }
    kernelCheck (.mkSimple s!"_r6016_{tag}") stmt (← instantiateMVars mv)

def arithmetic (tag : String) (a b : Expr) : MetaM Json := do
  -- the statement itself is built inside an attempt too: if that fails, both attempts carry its outcome
  let setup : MetaM (Except Attempt (Expr × Bool × String)) := withLimit do
    let (stmt, fvs) ← closedEq a b
    return .ok (stmt, ← fvs.anyM (fun id => do isProp (← id.getDecl).type), toString (← ppExpr stmt))
  match ← tryCatchRuntimeEx setup (fun ex => return .error (← fromException ex)) with
  | .error r => return Json.mkObj [("omega", toJson r), ("grobner", toJson r)]
  | .ok (_, true, shown) =>
    let r : Attempt := { outcome := "refused", detail := "the statement mentions a proof term; not attempted" }
    return Json.mkObj [("statement", toJson shown), ("omega", toJson r), ("grobner", toJson r)]
  | .ok (stmt, false, shown) =>
    let omega ← byTactic s!"{tag}_omega" stmt (← `(tactic| (intros; omega))) (·.startsWith "omega could not prove the goal")
    let grobner ← byTactic s!"{tag}_grobner" stmt (← `(tactic| (intros; grobner))) (·.startsWith "`grind` failed")
    return Json.mkObj [("statement", toJson shown), ("omega", toJson omega), ("grobner", toJson grobner)]

/-- Every assignment of 0 to 3 to `n` variables, in lexicographic order. -/
def assignments : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (assignments n).flatMap fun rest => (List.range 4).map (· :: rest)

partial def zetaAll (e : Expr) : MetaM Expr := do
  let e' ← zetaReduce e
  if e' == e then return e else zetaAll e'

def counterexampleCore (tag : String) (a b : Expr) : MetaM Json := do
  let ne := mkNot (← mkEq a b)
  let ne ← zetaAll (← instantiateMVars ne)
  let vars := (collectFVars {} ne).fvarIds
  let refuse (why : String) : MetaM Json :=
    return Json.mkObj [("outcome", toJson "refused"), ("detail", toJson why)]
  if vars.size > maxVariables then return ← refuse s!"{vars.size} free variables, more than {maxVariables}"
  let mut kinds := #[]
  for id in vars do
    let d ← id.getDecl
    let ty ← whnfR d.type
    if ty.isConstOf ``Nat then kinds := kinds.push (id, false)
    else if ty.isConstOf ``Int then kinds := kinds.push (id, true)
    else return ← refuse s!"the free variable {d.userName} has type {← ppExpr d.type}, outside ℕ and ℤ"
  let mut tried := 0
  for values in assignments vars.size do
    let inst := (kinds.zip values.toArray).foldl (fun e ((id, isInt), k) =>
      e.replaceFVar (mkFVar id) (if isInt then toExpr (Int.ofNat k) else toExpr k)) ne
    tried := tried + 1
    let r ← kernelCheck (.mkSimple s!"_r6016_{tag}_cex") inst (← mkDecideProof inst)
    if r.outcome == "established" then
      let named ← (kinds.zip values.toArray).mapM fun ((id, _), k) => return (toString (← id.getDecl).userName, k)
      return Json.mkObj [("outcome", toJson "established"), ("instance", toJson named), ("statement", toJson (toString (← ppExpr inst))),
                         ("detail", toJson s!"kernel accepted, at instance {tried}")]
    if r.outcome == "resource_exhausted" then return Json.mkObj [("outcome", toJson r.outcome), ("detail", toJson r.detail)]
  return Json.mkObj [("outcome", toJson "unsuccessful"), ("detail", toJson s!"no instance of {tried} decided a ≠ b")]

/-- The counterexample, one complete attempt: any exception becomes its outcome (no decision procedure is `refused`). -/
def counterexample (tag : String) (a b : Expr) : MetaM Json :=
  tryCatchRuntimeEx (withLimit (counterexampleCore tag a b)) fun ex => return attemptJson (← fromException ex)

/-- An observation that may fail (printing): its value, or the outcome of its failure. -/
def observed (x : MetaM Json) : MetaM Json :=
  tryCatchRuntimeEx (withLimit x) fun ex => return attemptJson (← fromException ex)

def diagnosePair (i j : Nat) (a b : Expr) : MetaM Json := do
  let tag := s!"{i}_{j}"
  let a ← instantiateMVars a; let b ← instantiateMVars b
  let printed ← observed do
    return Json.mkObj [("default", toJson (toString (← ppExpr a))), ("default_equal", toJson true),
                       ("pp_all", toJson #[← ppAll a, ← ppAll b]), ("pp_all_equal", toJson ((← ppAll a) == (← ppAll b)))]
  let diffJ ← match firstDifference a b with
    | some (path, x, y) => observed do return Json.mkObj [("path", toJson path), ("a", toJson (← ppAll x)), ("b", toJson (← ppAll y))]
    | none => pure Json.null
  let syntactic := Json.mkObj [("equal_after_instantiation", toJson (a == b)),
                               ("equal_up_to_metadata", toJson (stripMData a == stripMData b)), ("first_difference", diffJ)]
  let kernel ← kernelRfl tag a b
  let mut definitional := #[]
  for t in [TransparencyMode.reducible, .instances, .default] do
    for zd in [false, true] do definitional := definitional.push (← defeqAt t zd a b kernel)
  return Json.mkObj [("atoms", toJson #[i, j]), ("printed", printed), ("syntactic", syntactic),
                     ("definitional", Json.mkObj [("meta", toJson definitional), ("kernel", toJson kernel)]),
                     ("arithmetic", ← arithmetic tag a b), ("counterexample", ← counterexample tag a b)]

def diagnose (localName : Name) : MetaM Json := do
  let some li := (← getEnv).find? localName | throwError "missing local target {localName}"
  let pick := (·.isAppOfArity `ProofBroker.TermMode.farkasContradictN 3)
  let folds ← IO.mkRef #[]
  withLCtx {} {} do visit (li.value? (allowOpaque := true)).get! {} pick folds
  let folds ← folds.get
  unless folds.size == 1 do
    return Json.mkObj [("located", toJson false), ("reason", toJson s!"{folds.size} fold applications")]
  let fold := folds[0]!
  withLCtx fold.lctx #[] do
    let ty ← instantiateMVars (← inferType fold.args[2]!)
    let s := ty.appArg!
    let atoms ← atomsOf s #[]
    let shown ← atoms.mapM fun a => return toString (← ppExpr a)
    let mut pairs := #[]
    for i in [0:atoms.size] do
      for j in [i+1:atoms.size] do
        if shown[i]! == shown[j]! then
          let a ← instantiateMVars atoms[i]!; let b ← instantiateMVars atoms[j]!
          unless a == b do pairs := pairs.push (← diagnosePair i j a b)
    let mut atomsJ := #[]
    for i in [0:atoms.size] do
      atomsJ := atomsJ.push (Json.mkObj [("index", toJson i), ("default", toJson shown[i]!), ("pp_all", toJson (← ppAll atoms[i]!))])
    return Json.mkObj [("located", toJson true), ("positivity", toJson (toString (← ppExpr ty))), ("atoms", toJson atomsJ),
                       ("pairs", toJson pairs)]

end R6016Diagnosis

open R6016Diagnosis in
def main (args : List String) : IO UInt32 := do
  let [path, localName, reportPath] := args
    | IO.eprintln "usage: r6-016-diagnose EXPORT LOCAL REPORT.json"; return 2
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
  let ctx : Core.Context := { fileName := "<diagnosis>", fileMap := default, maxHeartbeats := 0,
                              options := Options.empty.setBool `Elab.async false }
  let (report, _) ← (do
      replayAll added
      diagnose localName.toName
    : MetaM Json).run' {} |>.toIO ctx { env := base }
  let env := Json.mkObj [("init_shared_identical", toJson identical), ("init_shared_equal_up_to_annotations", toJson annotated),
                         ("replayed_through_addDecl", toJson added.size), ("lean", toJson Lean.versionString),
                         ("max_heartbeats", toJson heartbeats), ("max_rec_depth", toJson ctx.maxRecDepth),
                         ("max_variables", toJson maxVariables)]
  IO.FS.writeFile reportPath ((Json.mkObj [("environment", env), ("diagnosis", report)]).pretty ++ "\n")
  return 0

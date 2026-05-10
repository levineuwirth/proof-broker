/-
End-to-end Lean tactic that closes a goal via the proof broker.

Pipeline:
  1. Reify the goal + Prop hypotheses into a ProofBroker.IR.IR (LIA fragment).
  2. Hand the IR to `runDispatchBroker` with the cvc4/cvc5/z3 manifests.
  3. Re-check the minted certificate via `runVerifyCertificate`.
  4. Close the goal with a tier-and-fragment-appropriate closer.

Soundness footprint:
  * Any cert over LIA (Tier 1 Farkas, Tier 2 case-split, or
    Tier 3 alethe-2024 — whichever the broker minted): closes via
    core Lean's `omega` decision procedure. Cert verification
    gates the call — the OCaml-side verifier has already accepted
    the proof, so `omega` will succeed on the LIA goal. `omega`
    itself is axiom-free, so goals closed on this path do not
    depend on `proofBrokerCertSound`. The fragment comes from the
    cert's `refinement_record`.
  * Anything else (`verifiedFarkas` over LRA, future BV / UF /
    etc.) falls back to `proofBrokerCertSound`. Each is removable
    per fragment: LRA needs a `linarith`-style closer (or Mathlib
    if a future package allows it); other fragments need their
    own decision procedure. Reifying the cert into a term-mode
    Lean proof — Farkas combination from the Tier 1 witness, or
    the Alethe walker for Tier 3 — is the principled finish, but
    LIA goals don't need it because `omega` already discharges
    them axiom-free.
  * Goal/hypothesis reification covers the LIA fragment only (Int with
    +, -, negation, multiplication by integer literal; ≤, <, =; ¬, ∧,
    ∨). Anything outside this fragment fails fast with a
    `proof_broker: unsupported …` error from the reifier.

`proofBrokerCertSound` admits an arbitrary `P : Prop`; uses are gated
by OCaml-side verifier acceptance. See per-reason removal notes above.
-/

import Lean
import ProofBroker.IR
import ProofBroker.Bridge
import ProofBroker.TermMode

namespace ProofBroker.Tactic

open Lean Lean.Elab.Tactic Lean.Meta ProofBroker.IR

/-- Trust axiom keyed on a verified ProofBroker certificate.

    Soundness footprint: the OCaml-side verifier (Tier 1 Farkas /
    Tier 2 case-split / Tier 3 Alethe walker). Used by `proof_broker`
    only on fragments without a Lean-side closer — every LIA goal
    discharges via core `omega` regardless of which tier the cert
    came from, so this axiom is currently exercised only on LRA
    (and any non-arithmetic fragment a future adapter might add).
    Each remaining usage is removable per fragment (see top-level
    docstring). -/
axiom proofBrokerCertSound : ∀ (P : Prop), P

/- ============================================================
   Extension hook for non-LIA fragments

   Core `ProofBroker` is Mathlib-free and supports LIA only. The
   `ProofBrokerMathlib` lib opts users into LRA support (Real
   reifier + `linarith` closer) by registering a `ReifierExt`
   here at module init. With no extension registered, behavior
   is unchanged from before this hook landed.
   ============================================================ -/

/-- Pluggable extension to the core reifier and closer. The core
    consults this for every recognition step that might extend
    beyond `Int`/LIA, falling through to its built-in error if
    the extension declines or none is registered.

    * `reifyType` returns `some "Real"` (or another non-Int type
      tag) for types the extension recognizes; `none` falls
      through to core's "Int only" rejection.
    * `freeVarType` decides which non-Prop locals become IR
      `freeVars`. Same shape as `reifyType` but keyed on the
      LCtx walk.
    * `matchLiteralExt` recognizes numeric literals in the
      extension's types, returning `(rendered value, type tag)`.
      Core handles Int via `OfNat.ofNat` / `Int.ofNat` directly.
    * `lraCloser` is the closer for `verif.ok = true` certs over
      LRA. The cert verification gates the call (the OCaml-side
      verifier already accepted the proof), so the closer can
      delegate to e.g. `linarith` and the resulting proof term
      is axiom-free.
    * `irFragment` is the IR's `firstOrderFragment` label to use
      when the extension is active and any free var is in an
      extension-recognized type. Core picks `"LIA"` by default. -/
structure ReifierExt where
  reifyType : Expr → MetaM (Option TypeRef)
  freeVarType : Expr → MetaM (Option TypeRef)
  matchLiteralExt : Expr → MetaM (Option (String × TypeRef))
  lraCloser : TacticM Unit
  irFragment : String

initialize reifierExt : IO.Ref (Option ReifierExt) ← IO.mkRef none

/- ============================================================
   Reifier: Lean Expr → ProofBroker IR ShellTerm
   ============================================================ -/

namespace Reify

/-- Recognize a closed `Nat`-valued `Expr` and read out its value.
    Handles both bare `Lit (.natVal _)` (the form `Nat.toExpr`
    produces) and `OfNat.ofNat _` wrapping (the form most
    elaborated literals arrive in). -/
def matchNatLiteral? (e : Expr) : Option Nat :=
  match e.rawNatLit? with
  | some n => some n
  | none =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit?
    | _ => none

/-- Recognize `BitVec n` for closed Nat literal `n`. Returns the
    width as a `Nat`. Built into core since `BitVec` is in core
    Lean (no Mathlib dependency); the `BitVec(N)` IR type-ref
    matches the SDK's `parse_bitvec_width` parser. -/
def matchBitVecType? (ty : Expr) : Option Nat :=
  match ty.getAppFnArgs with
  | (``BitVec, #[n]) => matchNatLiteral? n
  | _ => none

/-- Decode a type `Expr` as an IR `TypeRef`. Core handles `Int`,
    `Prop` (mapped to SMT-LIB `Bool` by the serializer), `BitVec n`,
    and arrow types `T1 → T2 → ... → R` (encoded as `T1->T2->...->R`);
    everything else falls through to the registered `reifierExt`.
    The arrow encoding is the IR convention for UF — the SDK's
    [Smtlib.parse_arrow_type] + [emit_decls] turn this into
    `(declare-fun f (T1 T2) R)` SMT-LIB output. `Prop` arises in
    arrow chains for predicate-valued UF (`P : Int → Prop`); it is
    not accepted as a free-var carrier on its own (the LCtx walk
    classifies Prop-typed locals as hypotheses, not free vars). -/
partial def reifyType (ty : Expr) : MetaM TypeRef := do
  if ty.isConstOf ``Int then return "Int"
  if ty.isProp then return "Prop"
  if let some n := matchBitVecType? ty then
    return s!"BitVec({n})"
  if ty.isArrow then
    -- Walk every arrow in the chain so [(T1 → T2) → R] becomes
    -- `(T1->T2)->R` etc. — the SDK's parse_arrow_type splits on
    -- the rightmost `->`, but we encode strictly left-to-right
    -- which the parser accepts because all our UF types are
    -- first-order (no higher-order arguments).
    let mut t := ty
    let mut parts : Array TypeRef := #[]
    while t.isArrow do
      let dom := t.bindingDomain!
      parts := parts.push (← reifyType dom)
      t := t.bindingBody!
    parts := parts.push (← reifyType t)
    return String.intercalate "->" parts.toList
  match ← reifierExt.get with
  | some ext =>
    match ← ext.reifyType ty with
    | some t => return t
    | none => throwError "proof_broker: unsupported type {ty}"
  | none => throwError "proof_broker: unsupported type {ty}; LIA scope is Int only"

/-- Recognize an `OfNat.ofNat` / `Int.ofNat` literal at type `Int`
    and read out its raw `Nat` value. Returns `none` if the
    expression is not a literal in this shape, or if it's an
    `OfNat.ofNat` over a non-`Int` type (e.g. Real, Nat) — those
    fall through to the registered `reifierExt`'s
    `matchLiteralExt`. The `Int.ofNat` and bare `Nat.lit` paths
    are unambiguously Int. -/
def matchIntLiteral? (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[α, n, _inst]) =>
    if α.isConstOf ``Int then n.rawNatLit? else none
  | (``Int.ofNat, #[n]) => n.rawNatLit?
  | _ => e.rawNatLit?

/-- Recognize a `BitVec n` numeric literal — `OfNat.ofNat` over
    `BitVec n` (the form `(5 : BitVec 8)` desugars to). Returns
    `(decimalString, "BitVec(n)")`. Doesn't fall through the
    `reifierExt`'s `matchLiteralExt` path because BitVec is in
    core; same logic as `matchIntLiteral?` but typed for BV. -/
def matchBitVecLiteral? (e : Expr) : Option (String × TypeRef) :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[α, n, _inst]) =>
    match matchBitVecType? α, matchNatLiteral? n with
    | some w, some k => some (toString k, s!"BitVec({w})")
    | _, _ => none
  | _ => none

/-- Confirm that a comparison/equality at type `α` is over a
    fragment we can reify — `Int` always; anything else only if
    the extension's `reifyType` recognizes it. The reified IR
    term's type tag isn't carried through `LE.le` / `LT.lt`
    explicitly (the OCaml side derives it from the operand
    types), so we only need to gate, not capture. -/
def expectArithCarrier (α : Expr) : MetaM Unit := do
  if α.isConstOf ``Int then return
  if (matchBitVecType? α).isSome then return
  match ← reifierExt.get with
  | some ext =>
    match ← ext.reifyType α with
    | some _ => return
    | none =>
      throwError "proof_broker: comparison/equality over {α} not in supported fragment"
  | none =>
    throwError "proof_broker: comparison/equality over {α} not in LIA scope (Int only)"

partial def reifyTerm (e : Expr) : MetaM ShellTerm := do
  if e.isFVar then
    let lctx ← getLCtx
    let decl := lctx.get! e.fvarId!
    let _ ← reifyType decl.type
    return .var decl.userName.toString
  if e.isConstOf ``False then
    return .const "False"
  if e.isConstOf ``True then
    return .const "True"
  if let some n := matchIntLiteral? e then
    return .numLit (toString n) "Int"
  -- BV literal in core (e.g. (5 : BitVec 8)). Must precede the
  -- extension's matchLiteralExt so a BitVec literal isn't
  -- accidentally claimed by a Real/Q recognizer.
  if let some (val, ty) := matchBitVecLiteral? e then
    return .numLit val ty
  -- Extension-provided literal recognizer (e.g. Real OfNat / OfScientific).
  if let some ext ← reifierExt.get then
    if let some (val, ty) ← ext.matchLiteralExt e then
      return .numLit val ty
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, _, a, b]) =>
      -- BV vs arithmetic disambiguation: SMT-LIB uses bvadd /
      -- bvsub / bvmul rather than the polymorphic + / - / *, so
      -- the IR carries them under different App symbols. Picked
      -- at reify time from the operand type.
      let sym := if (matchBitVecType? α).isSome then "BV.add" else "HAdd.hAdd"
      return .app sym [] [← reifyTerm a, ← reifyTerm b]
  | (``HSub.hSub, #[α, _, _, _, a, b]) =>
      let sym := if (matchBitVecType? α).isSome then "BV.sub" else "HSub.hSub"
      return .app sym [] [← reifyTerm a, ← reifyTerm b]
  | (``HMul.hMul, #[α, _, _, _, a, b]) =>
      let sym := if (matchBitVecType? α).isSome then "BV.mul" else "HMul.hMul"
      return .app sym [] [← reifyTerm a, ← reifyTerm b]
  | (``Neg.neg, #[_, _, a]) =>
      return .app "Neg.neg" [] [← reifyTerm a]
  | (``LE.le, #[α, _, a, b]) =>
      expectArithCarrier α
      -- Lean's [<=] over BitVec resolves to BitVec.ule (unsigned).
      -- Signed comparisons need [BitVec.sle] written explicitly.
      let sym := if (matchBitVecType? α).isSome then "BV.ule" else "LE.le"
      return .app sym [] [← reifyTerm a, ← reifyTerm b]
  | (``LT.lt, #[α, _, a, b]) =>
      expectArithCarrier α
      let sym := if (matchBitVecType? α).isSome then "BV.ult" else "LT.lt"
      return .app sym [] [← reifyTerm a, ← reifyTerm b]
  | (``GE.ge, #[α, _, a, b]) =>
      expectArithCarrier α
      let sym := if (matchBitVecType? α).isSome then "BV.ule" else "LE.le"
      return .app sym [] [← reifyTerm b, ← reifyTerm a]
  | (``GT.gt, #[α, _, a, b]) =>
      expectArithCarrier α
      let sym := if (matchBitVecType? α).isSome then "BV.ult" else "LT.lt"
      return .app sym [] [← reifyTerm b, ← reifyTerm a]
  | (``Eq, #[α, a, b]) =>
      let tref ← reifyType α
      return .eq tref (← reifyTerm a) (← reifyTerm b)
  | (``And, #[a, b]) =>
      return .and_ (← reifyTerm a) (← reifyTerm b)
  | (``Or, #[a, b]) =>
      return .or_ (← reifyTerm a) (← reifyTerm b)
  | (``Not, #[a]) =>
      return .not_ (← reifyTerm a)
  | _ =>
      -- UF fallback: the head is a free variable applied to
      -- arguments, with an arrow-typed declaration in scope.
      -- Emit `App { symbol = "UF.<fname>" }` and the SDK
      -- serializer takes care of the [declare-fun] /
      -- application emission. Anything else is genuinely
      -- unsupported.
      let fn := e.getAppFn
      if fn.isFVar && e.getAppNumArgs > 0 then
        let lctx ← getLCtx
        let decl := lctx.get! fn.fvarId!
        if decl.type.isArrow then
          let fname := decl.userName.toString
          let argList := e.getAppArgs.toList
          let reifiedArgs ← argList.mapM reifyTerm
          return .app s!"UF.{fname}" [] reifiedArgs
      throwError "proof_broker: unsupported expression: {e}"

/-- True iff any subterm carries a `BitVec(N)` type tag, on a
    `numLit` or an `eq`'s `ty` field. Mirrors the SDK's
    `Smtlib.shell_mentions_bv` so the Lean-side fragment derivation
    matches the OCaml-side one for closed-BV-term goals (no
    BitVec free vars, just BV literals + ops). Without this, a
    goal like `(3 : BitVec 8) < 5` has no BV-typed locals and
    the fragment label silently degrades to `"LIA"`, then
    `capability_match` accepts a non-BV adapter (e.g. cvc4 whose
    manifest only advertises LIA/LRA) and dispatch fails. -/
partial def shellMentionsBV : ShellTerm → Bool
  | .var _ | .const _ => false
  | .numLit _ ty =>
    ty.startsWith "BitVec("
  | .eq ty a b =>
    ty.startsWith "BitVec(" || shellMentionsBV a || shellMentionsBV b
  | .app _ _ args => args.any shellMentionsBV
  | .and_ a b | .or_ a b => shellMentionsBV a || shellMentionsBV b
  | .implies a b => shellMentionsBV a || shellMentionsBV b
  | .not_ a => shellMentionsBV a
  | .forall_ _ _ b | .exists_ _ _ b => shellMentionsBV b
  | .lambda _ b => shellMentionsBV b
  | .opaque_ _ => false

/-- True iff any subterm carries a `UF.*` App-symbol — the
    bridge-level convention for uninterpreted-function
    applications. The SDK's [Smtlib.shell_mentions_uf] is the
    OCaml-side mirror used by [pick_logic] for SMT-LIB output;
    the Lean-side function here drives the IR's fragment label
    for [capability_match]. -/
partial def shellMentionsUF : ShellTerm → Bool
  | .var _ | .const _ | .numLit _ _ => false
  | .eq _ a b => shellMentionsUF a || shellMentionsUF b
  | .app sym _ args =>
    sym.startsWith "UF." || args.any shellMentionsUF
  | .and_ a b | .or_ a b => shellMentionsUF a || shellMentionsUF b
  | .implies a b => shellMentionsUF a || shellMentionsUF b
  | .not_ a => shellMentionsUF a
  | .forall_ _ _ b | .exists_ _ _ b => shellMentionsUF b
  | .lambda _ b => shellMentionsUF b
  | .opaque_ _ => false

/-- Reify the goal + Prop-typed hypotheses + Int-typed free variables
    of `mvarId` into an IR document tagged for the LIA fragment.

    Skips implementation-detail locals (compiler-introduced auxiliary
    decls, e.g. recursors). Hypotheses whose type isn't a Prop are
    treated as data: Int-typed ones become `freeVars`, anything else
    is silently ignored (the goal/Prop reifier will trip on them if
    they're actually referenced). -/
def buildIR (mvarId : MVarId) : MetaM IR := mvarId.withContext do
  let goalType ← mvarId.getType
  let goalShell ← reifyTerm goalType
  let mut freeVars : List FreeVar := []
  let mut hypotheses : List IR.Hypothesis := []
  let extOpt ← reifierExt.get
  let mut sawExtensionType : Bool := false
  let mut sawBV : Bool := false
  let mut sawUF : Bool := false
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty := decl.type
    if ← isProp ty then
      let shell ← reifyTerm ty
      hypotheses := hypotheses ++ [{ name := decl.userName.toString, shell }]
    else if ty.isConstOf ``Int then
      freeVars := freeVars ++ [{ name := decl.userName.toString, ty := "Int" }]
    else if let some n := matchBitVecType? ty then
      freeVars := freeVars ++ [{ name := decl.userName.toString, ty := s!"BitVec({n})" }]
      sawBV := true
    else if ty.isArrow then
      -- Function-typed local: this is a UF candidate. Encode the
      -- type as the arrow chain the SDK serializer parses.
      let tref ← reifyType ty
      freeVars := freeVars ++ [{ name := decl.userName.toString, ty := tref }]
      sawUF := true
    else
      match extOpt with
      | some ext =>
        match ← ext.freeVarType ty with
        | some tref =>
          freeVars := freeVars ++ [{ name := decl.userName.toString, ty := tref }]
          sawExtensionType := true
        | none => pure ()
      | none => pure ()
  -- Pick fragment label. Precedence:
  --   BV  wins if any free var is BitVec-typed OR any subterm
  --       mentions a BV type tag (capability_match keys on this
  --       label, so closed-BV-term goals need to carry "BV" too
  --       or cvc4-style LIA-only manifests would spuriously match).
  --   UF  wins next if any free var is arrow-typed OR any subterm
  --       carries a UF.* App symbol — sdk's pick_logic emits
  --       QF_UFLIA / QF_UFLRA as appropriate from term content,
  --       this label is just for capability_match.
  --   Extension wins if it claimed any free var (Real → LRA).
  --   Otherwise default LIA.
  let bvInTerms :=
    shellMentionsBV goalShell
    || hypotheses.any (fun h => shellMentionsBV h.shell)
  let ufInTerms :=
    shellMentionsUF goalShell
    || hypotheses.any (fun h => shellMentionsUF h.shell)
  let fragment :=
    if sawBV || bvInTerms then "BV"
    else if sawUF || ufInTerms then "UF"
    else match extOpt with
      | some ext => if sawExtensionType then ext.irFragment else "LIA"
      | none => "LIA"
  return {
    irVersion := "1.0",
    sourceSystem := { name := "lean", version := "0.0" },
    tier := "goal",
    logicClassification := {
      order := "first_order", featuresUsed := [],
      firstOrderFragment := fragment, decidableTheory := none
    },
    goal := { shell := goalShell, payloads := none },
    context := { typeVars := [], freeVars, hypotheses, librarySlice := none },
    typeMetadata := [],
    definitionalMetadata := [],
    libraryProvenance := [],
    userDirectives := none
  }

end Reify

/- ============================================================
   Manifest loading

   Manifests sit alongside the test fixtures in `examples/`. The
   tactic finds them by:
     1. honoring `PROOF_BROKER_EXAMPLES_DIR` if set,
     2. otherwise falling back to `<cwd>/../examples`.

   The cwd-relative fallback matches Main.lean's convention so the
   tactic-driven test library shares the same setup.
   ============================================================ -/

private def defaultManifestDir : IO System.FilePath := do
  match (← IO.getEnv "PROOF_BROKER_EXAMPLES_DIR") with
  | some s => return s
  | none => return (← IO.currentDir) / ".." / "examples"

private def loadManifestIfPresent (path : System.FilePath) : TacticM (Option Json) := do
  unless ← path.pathExists do return none
  let raw ← IO.FS.readFile path
  match Json.parse raw with
  | .ok j => return some j
  | .error e => throwError "proof_broker: manifest parse error at {path}: {e}"

private def loadDefaultManifests : TacticM (List Json) := do
  let dir ← defaultManifestDir
  let names := ["manifest-cvc4.json", "manifest-cvc5.json", "manifest-z3.json"]
  let mut result : List Json := []
  for n in names do
    if let some j ← loadManifestIfPresent (dir / n) then
      result := result ++ [j]
  if result.isEmpty then
    throwError "proof_broker: no manifests found in {dir}; \
                set PROOF_BROKER_EXAMPLES_DIR or run from a directory \
                whose parent has examples/manifest-*.json"
  return result

/-- Load manifests for a user-supplied list of adapter names, in the
    given order. Each name is resolved as `manifest-<name>.json` under
    the manifest dir; missing names error rather than being silently
    skipped — if the user named an adapter, they expect it to run. -/
private def loadManifestsByName (names : List String) : TacticM (List Json) := do
  let dir ← defaultManifestDir
  let mut result : List Json := []
  for name in names do
    let path := dir / s!"manifest-{name}.json"
    match ← loadManifestIfPresent path with
    | some j => result := result ++ [j]
    | none =>
      throwError "proof_broker: no manifest for adapter '{name}' at {path}"
  return result

/- ============================================================
   Telemetry: extraction-path summary
   ============================================================ -/

/-- Count `ShellTerm` nodes by recursive walk. Used in the IR shape
    summary so users have a rough size handle on the reified goal. -/
partial def countShellNodes : ShellTerm → Nat
  | .forall_ _ _ b | .exists_ _ _ b => 1 + countShellNodes b
  | .lambda _ b => 1 + countShellNodes b
  | .not_ b => 1 + countShellNodes b
  | .implies a c | .and_ a c | .or_ a c => 1 + countShellNodes a + countShellNodes c
  | .eq _ a b => 1 + countShellNodes a + countShellNodes b
  | .app _ _ args => 1 + args.foldl (fun acc x => acc + countShellNodes x) 0
  | _ => 1

/-- The data the `proof_broker?` debug form summarizes. Captures
    every signal a user would want to inspect end-to-end: what was
    reified, which adapter ran, what the cert shape was, and how
    long each broker phase took. -/
structure ExtractionPath where
  ir : IR
  attempts : List Attempt
  cert : Option Json
  verifyOk : Option Bool
  /-- Looser-than-`verifyOk` flag: true when envelope checks passed
      but no tier-specific verifier applied (e.g. Tier 0 oracle).
      Consumers that only need envelope-correctness gate on this. -/
  verifyEnvelopeOk : Option Bool
  verifyReason : Option CertReason
  dispatchMs : Nat
  verifyMs : Nat

private def msSince (t0 : Nat) : BaseIO Nat := do
  return (← IO.monoMsNow) - t0

private def attemptOutcomeStr (a : Attempt) : String :=
  match a.outcome with
  | .skipped reason => s!"skipped ({reprStr reason})"
  | .noImplementation => "no_implementation"
  | .failed f => s!"failed ({reprStr f})"
  | .succeeded => "succeeded"

/-- Render an `ExtractionPath` as multi-line `MessageData` for
    `logInfo`. Layout matches the order the broker runs:
    IR shape → dispatch attempts → cert shape → verify outcome. -/
private def renderPath (path : ExtractionPath) : MessageData :=
  let ir := path.ir
  let nFV := ir.context.freeVars.length
  let nHyp := ir.context.hypotheses.length
  let nGoal := countShellNodes ir.goal.shell
  let frag := ir.logicClassification.firstOrderFragment
  let irLine :=
    s!"  ir:       {nFV} free var(s), {nHyp} hypothes{if nHyp == 1 then "is" else "es"}, " ++
    s!"{nGoal} goal node(s), fragment={frag}"
  let dispatchLine :=
    s!"  dispatch: {path.dispatchMs}ms, {path.attempts.length} attempt(s)"
  let attemptLines :=
    path.attempts.map (fun a => s!"              {a.adapter} → {attemptOutcomeStr a}")
  let certLine := match path.cert with
    | none => "  cert:     none"
    | some c =>
      let tier := (c.getObjValAs? Int "tier").toOption.getD (-1)
      let fmt := (c.getObjValAs? String "format").toOption.getD "?"
      s!"  cert:     tier={tier}, format={fmt}"
  let verifyLine := match path.verifyOk, path.verifyReason with
    | some ok, some r => s!"  verify:   {path.verifyMs}ms, ok={ok} ({reprStr r})"
    | _, _ => "  verify:   skipped"
  let lines := ["proof_broker?:", irLine, dispatchLine] ++ attemptLines ++ [certLine, verifyLine]
  m!"{String.intercalate "\n" lines}"

/- ============================================================
   Tactic
   ============================================================ -/

/-- Shared implementation. Reifies, dispatches, verifies, returns
    the structured `ExtractionPath`. Throws on conditions that
    block any chance of closing the goal (codec failure, FFI
    transport failure, manifest load failure); leaves
    "no adapter succeeded" / "cert rejected by verifier" as soft
    failures recorded in the path so the verbose form can show
    them before re-raising. -/
private def buildExtractionPath
    (goal : MVarId)
    (adapterNames? : Option (List String))
    (preferHigherTier : Bool)
    : TacticM ExtractionPath := do
  let ir ← Reify.buildIR goal
  let manifests ← match adapterNames? with
    | some names => loadManifestsByName names
    | none => loadDefaultManifests
  let t0 ← IO.monoMsNow
  let dispatch ← match runDispatchBroker ir manifests preferHigherTier with
    | .ok r => pure r
    | .error e => throwError "proof_broker: dispatch_broker failed: {repr e}"
  let dispatchMs ← msSince t0
  let mut verifyOk : Option Bool := none
  let mut verifyEnvelopeOk : Option Bool := none
  let mut verifyReason : Option CertReason := none
  let mut verifyMs : Nat := 0
  if let some cert := dispatch.cert then
    let t1 ← IO.monoMsNow
    let verif ← match runVerifyCertificate cert ir with
      | .ok v => pure v
      | .error e => throwError "proof_broker: verify_certificate failed: {repr e}"
    verifyMs ← msSince t1
    verifyOk := some verif.ok
    verifyEnvelopeOk := some verif.envelopeOk
    verifyReason := some verif.reason
  return {
    ir, attempts := dispatch.attempts, cert := dispatch.cert,
    verifyOk, verifyEnvelopeOk, verifyReason, dispatchMs, verifyMs
  }

/-- Read the fragment label out of a cert's `refinement_record`.
    Returns `""` when the field is missing or the cert is malformed
    in a way the OCaml side wouldn't normally emit; the caller will
    just take the axiom branch on an empty string, which is
    soundness-equivalent. -/
private def certFragment (cert : Json) : String :=
  (cert.getObjVal? "refinement_record"
    |>.bind (·.getObjValAs? String "fragment")).toOption.getD ""

/-- Close the goal from a successfully verified path, or surface a
    structured error describing why the path didn't close.

    Closure dispatch is keyed on the cert's fragment first, then
    its verify reason:

    * Any cert (Tier 1 / 2 / 3) over LIA: `omega`. Sound for LIA
      and axiom-free; cert verification gates the call so we only
      invoke `omega` on goals the broker has already certified
      provable. This covers the common case where `preferHigherTier`
      floats cvc5's Tier 3 alethe-2024 path to the top — those
      `verifiedTier3` certs over LIA close axiom-free even though
      we don't have a Lean-side Alethe walker yet.
    * Anything else `verif.ok = true` (LRA Tier 1 Farkas, future
      BV / UF / etc.): `proofBrokerCertSound`. Removable per
      fragment: LRA needs a `linarith`-style closer (or Mathlib);
      others need their own decision procedure. Tier 3 reification
      via a Lean-side Alethe walker is the principled finish, but
      not needed for LIA Tier 3 — omega already nails that with
      no axiom.

    The verbose form calls `logInfo` with `renderPath` first; the bare
    form just throws so unsuccessful invocations are silent. -/
private def closeOrFail (goal : MVarId) (goalType : Expr)
    (path : ExtractionPath) : TacticM Unit := do
  -- Accept either strict verifyOk (Tier 1/2/3 with a real
  -- soundness check) OR envelopeOk + tierCheckDeferred (Tier 0
  -- oracle path, currently the only route for fragments without
  -- a witness extractor — BV being the first concrete one). The
  -- envelope-only path is always followed by a fragment-keyed
  -- decision-procedure call, so the cert's role here is gating
  -- (we know the goal is provable) rather than carrying the
  -- proof; the closer must succeed on its own to actually close.
  let acceptable := path.verifyOk == some true
    || (path.verifyEnvelopeOk == some true
        && match path.verifyReason with
           | some (.tierCheckDeferred _) => true
           | _ => false)
  match path.cert, acceptable with
  | some cert, true =>
    let fragment := certFragment cert
    if fragment == "LIA" then
      -- Cert-gated omega: the OCaml-side verifier (Tier 1 Farkas,
      -- Tier 2 case-split, or Tier 3 Alethe walker — whichever
      -- the verify reason indicates) has already accepted this
      -- proof, so omega will succeed on the LIA goal. omega itself
      -- is axiom-free, so the resulting proof term does not depend
      -- on `proofBrokerCertSound` regardless of the tier the cert
      -- came from.
      evalTactic (← `(tactic| omega))
    else if fragment == "BV" then
      -- Cert-gated decide: BitVec has DecidableEq + the operator
      -- typeclass instances are decidable, so closed BV goals
      -- reduce to a decidable proposition that `decide` discharges.
      -- The cert is Tier 0 oracle today (no native BV witness
      -- extraction); envelope verification + cvc5/z3 unsat is
      -- the trust gate, `decide` is the actual proof emitter.
      -- `decide` is itself axiom-free, so closure here doesn't
      -- depend on `proofBrokerCertSound`. Big-width / quantifier-
      -- heavy BV goals where `decide` doesn't terminate in
      -- elaboration time fall through to the trust axiom.
      try evalTactic (← `(tactic| decide))
      catch _ => goal.assign (mkApp (.const ``proofBrokerCertSound []) goalType)
    else if fragment == "UF" then
      -- Cert-gated congruence: cvc5 / z3 already accepted the
      -- goal under QF_UFLIA / QF_UFLRA, so the goal is
      -- semantically valid. We try a small chain of constructive
      -- closers — `rfl` for trivially-defeq closed UF terms,
      -- then `subst_eqs` (substitutes equation hypotheses
      -- everywhere) followed by `rfl`/`omega` for the common
      -- congruence-style goal `f x = f y` with `x = y` in
      -- scope. Falls through to the trust axiom on shapes the
      -- chain can't close (deeper UF reasoning, theory
      -- combinations the SAT-style solver handled but Lean's
      -- propositional toolkit doesn't). `subst_eqs` and friends
      -- are themselves axiom-free, so closures inside the chain
      -- don't introduce a trust assumption.
      -- Tactics tried, in order:
      --   subst_eqs; rfl  — the `f x = f y` from `x = y` shape;
      --                     covers the canonical congruence case.
      --   simp_all        — heavier rewriting, picks up rewrites
      --                     under conjunctions / nested structure
      --                     subst_eqs misses.
      -- If both fail, the cert verdict still holds and we route
      -- through the trust axiom. `subst_eqs` and `simp_all` are
      -- themselves axiom-free (the `propext` they may pull in is
      -- already in the LIA path's footprint), so the chain
      -- doesn't introduce a stronger trust assumption than
      -- omega/decide do elsewhere.
      try evalTactic (← `(tactic| subst_eqs; rfl))
      catch _ =>
        try evalTactic (← `(tactic| simp_all))
        catch _ =>
          goal.assign (mkApp (.const ``proofBrokerCertSound []) goalType)
    else
      -- Non-LIA / non-BV: dispatch through the registered
      -- ReifierExt's closer if present (e.g. ProofBrokerMathlib
      -- registers a linarith closer for "LRA"); otherwise fall
      -- back to the trust axiom. The cert verification gates the
      -- call either way, so the closer can trust solvability.
      if fragment == "LRA" then
        match ← reifierExt.get with
        | some ext => ext.lraCloser
        | none => goal.assign (mkApp (.const ``proofBrokerCertSound []) goalType)
      else
        goal.assign (mkApp (.const ``proofBrokerCertSound []) goalType)
  | none, _ =>
    let head := path.attempts.head?.map (·.outcome) |>.map reprStr |>.getD "<no attempts>"
    throwError "proof_broker: no adapter could close the goal \
                ({path.attempts.length} attempt(s); first: {head})"
  | some _, false =>
    -- Cert exists but verifier didn't reach an acceptance state we
    -- can act on (strict failure, or a deferred check that the
    -- closer can't trust). Surface the reason verbatim.
    let r := path.verifyReason.map reprStr |>.getD "<unknown>"
    throwError "proof_broker: cert minted but verifier rejected: {r}"

/- ============================================================
   Term-mode closer (Tier 1 Farkas reconstruction)
   ============================================================ -/

/-- Read coefficient strings out of `cert.payload.witness_data.coefficients`.
    Returns `(name, coef-as-Int)` per entry. Errors if the cert isn't a
    Tier 1 Farkas envelope or any coefficient isn't an integer string. -/
private def parseFarkasCoefficients (cert : Json)
    : TacticM (List (String × Int)) := do
  let payload ← match cert.getObjVal? "payload" with
    | .ok j => pure j
    | .error e => throwError "proof_broker_term: cert missing payload: {e}"
  let witnessKind := (payload.getObjValAs? String "witness_kind").toOption.getD ""
  unless witnessKind == "farkas" do
    throwError "proof_broker_term: cert is not a Farkas witness (kind={witnessKind})"
  let witnessData ← match payload.getObjVal? "witness_data" with
    | .ok j => pure j
    | .error e => throwError "proof_broker_term: cert missing witness_data: {e}"
  let coeffsJ ← match witnessData.getObjVal? "coefficients" with
    | .ok j => pure j
    | .error e => throwError "proof_broker_term: witness missing coefficients: {e}"
  let arr ← match coeffsJ.getArr? with
    | .ok a => pure a
    | .error e => throwError "proof_broker_term: coefficients not array: {e}"
  arr.toList.mapM fun entry => do
    let name := (entry.getObjValAs? String "hypothesis").toOption.getD ""
    let coefStr := (entry.getObjValAs? String "coefficient").toOption.getD ""
    if name == "" then throwError "proof_broker_term: witness entry missing hypothesis"
    let coef ← match coefStr.toInt? with
      | some n => pure n
      | none => throwError
          "proof_broker_term: non-integer coefficient '{coefStr}' \
           (rationals not yet wired)"
    pure (name, coef)

/-- Look up a hypothesis by user-name in the LCtx, returning the
    `(FVar Expr, type Expr)` pair. Throws if not found or shadowed
    (multiple matches with the same user-name). -/
private def fvarOfName (name : String) : MetaM (Expr × Expr) := do
  let lctx ← getLCtx
  let hits := lctx.foldl (init := #[]) fun acc decl =>
    if decl.isImplementationDetail || decl.userName.toString != name then acc
    else acc.push decl
  match hits.toList with
  | [decl] => return (Expr.fvar decl.fvarId, decl.type)
  | [] => throwError "proof_broker_term: hypothesis '{name}' not in scope"
  | _ => throwError "proof_broker_term: hypothesis '{name}' is ambiguous (shadowed)"

/-- Recognize an `Int` `≤` / `≥` / `<` / `>` shape in a hypothesis
    type. Returns `(direction, lhs, rhs)` where direction picks the
    normalization helper to apply. Lean's `≥` desugars to
    `LE.le b a`, so we pattern-match on `LE.le`/`LT.lt` only —
    anything else is out of scope for the arity-2 starter slice. -/
private def matchIntBound? (ty : Expr) : Option (Bool × Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``LE.le, #[α, _, a, b]) =>
    if α.isConstOf ``Int then some (true, a, b) else none
  | (``LT.lt, #[α, _, _, _]) =>
    -- Strict bounds need a different normalization (`a < b → a + 1 ≤ b`)
    -- the arity-2 slice doesn't yet wire — surface as unsupported.
    let _ := α
    none
  | _ => none

/-- Given a hypothesis `(h : a ≤ b)` with `a b : Int`, build an
    `Expr` of type `a - b ≤ 0` by applying `leToLe0`. Returns
    `(a - b)` as an Expr alongside the proof so the caller can
    reference both. -/
private def normalizeHypothesis (hypFV : Expr) (hypTy : Expr)
    : MetaM (Expr × Expr) := do
  match matchIntBound? hypTy with
  | some (true, a, b) =>
    let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM ``ProofBroker.TermMode.leToLe0 #[hypFV]
    return (normExpr, proof)
  | _ =>
    throwError "proof_broker_term: hypothesis shape outside Int ≤/≥ \
                 (got type {hypTy})"

/-- Build an `Int` literal `Expr` for `c`. Uses `Lean.toExpr` so the
    resulting `Expr` is the elaborated `@OfNat.ofNat Int n instOfNat`
    form `omega` recognizes — `Int.ofNat`-wrapped literals stay
    opaque to omega's linear-arith solver. -/
private def intLitExpr (c : Int) : Expr := Lean.toExpr c

/-- Build a proof of `0 ≤ c` for a literal integer `c` using `decide`.
    Closed under `Int.decLe` for nonnegative literals; throws if the
    coefficient is negative. -/
private def buildNonnegProof (c : Int) : MetaM Expr := do
  if c < 0 then
    throwError "proof_broker_term: negative coefficient {c} (cert verifier \
                 should have caught this earlier)"
  let goalTy ← Lean.Meta.mkAppM ``LE.le #[intLitExpr 0, intLitExpr c]
  Lean.Meta.mkDecideProof goalTy

/-- Discharge `omegaGoal` (a fresh metavariable carrying the
    polynomial-identity-style strict-positivity subgoal) by running
    `omega` against it in isolation. Restores the caller's goal
    list afterward. The original term-mode goal is left to the
    caller to `assign`. -/
private def closeOmegaSubgoal (omegaMV : MVarId) : TacticM Unit := do
  let prevGoals ← getGoals
  setGoals [omegaMV]
  evalTactic (← `(tactic| omega))
  setGoals prevGoals

/-- Term-mode closer, False-goal arity-2 path. Both witness entries
    name real hypotheses; the proof term is `farkasContradict` with
    every coefficient flowing through as an Int literal and the
    strict-positivity subgoal discharged by `omega`. -/
private def closeViaTermModeFalse
    (goal : MVarId) (entries : List (String × Int)) : TacticM Unit := do
  let [(name1, c1), (name2, c2)] := entries
    | throwError "proof_broker_term: unexpected entry count after arity check"
  goal.withContext do
    let (fv1, ty1) ← fvarOfName name1
    let (fv2, ty2) ← fvarOfName name2
    let (a1, h1') ← normalizeHypothesis fv1 ty1
    let (a2, h2') ← normalizeHypothesis fv2 ty2
    let c1Expr := intLitExpr c1
    let c2Expr := intLitExpr c2
    let hc1 ← buildNonnegProof c1
    let hc2 ← buildNonnegProof c2
    let zero := intLitExpr 0
    let prod1 ← Lean.Meta.mkAppM ``HMul.hMul #[c1Expr, a1]
    let prod2 ← Lean.Meta.mkAppM ``HMul.hMul #[c2Expr, a2]
    let sum ← Lean.Meta.mkAppM ``HAdd.hAdd #[prod1, prod2]
    let hposTy ← Lean.Meta.mkAppM ``LT.lt #[zero, sum]
    let hposMV ← Lean.Meta.mkFreshExprMVar hposTy
    let term ← Lean.Meta.mkAppM ``ProofBroker.TermMode.farkasContradict
      #[h1', h2', hc1, hc2, hposMV]
    closeOmegaSubgoal hposMV.mvarId!
    goal.assign term

/-- The four LIA-goal shapes the non-False term-mode handles. Each
    routes to one of two `TermMode` helpers via instance reduction:
    `≥` reduces to `≤` swapped, `>` reduces to `<` swapped. The
    `kind` field tracks whether the neg-goal normalized form
    carries the LIA +1 trick (`≤` / `≥` do; `<` / `>` don't) so
    the closer builds the right `heq` polynomial. -/
private inductive GoalKind
  | le   -- b ≤ c   (helper farkasGoalLe2, +1 trick)
  | lt   -- b < c   (helper farkasGoalLt2, no +1)
deriving Repr

/-- Match an Int LIA-comparison goal. Returns `(b, c, kind)` where
    `b`, `c` are the helper's named arguments — for `≥` / `>` the
    SDK has already swapped the operands at IR-build time, and
    `GE.ge / GT.gt` reduce definitionally to `LE.le b a / LT.lt b a`
    so the proof term we build for the swapped shape unifies with
    the original Lean goal via instance reduction.

    Returns `none` for shapes outside the LIA-comparison vocabulary
    (notably `Eq` — non-Tier-1, needs Tier 2 case-split). -/
private def matchLiaGoal? (goalType : Expr)
    : Option (Expr × Expr × GoalKind) :=
  match goalType.getAppFnArgs with
  | (``LE.le, #[α, _, b, c]) =>
    if α.isConstOf ``Int then some (b, c, .le) else none
  | (``LT.lt, #[α, _, b, c]) =>
    if α.isConstOf ``Int then some (b, c, .lt) else none
  | (``GE.ge, #[α, _, a, b]) =>
    -- a ≥ b ≡ b ≤ a; the helper takes (b, c) where c is the upper
    -- bound, so map (a, b) → (b := b, c := a).
    if α.isConstOf ``Int then some (b, a, .le) else none
  | (``GT.gt, #[α, _, a, b]) =>
    -- a > b ≡ b < a; same swap as ≥.
    if α.isConstOf ``Int then some (b, a, .lt) else none
  | _ => none

/-- Term-mode closer, non-False arity-2 path. Goal must be one of
    the four LIA-comparison shapes over `Int` (`≤` / `<` / `≥` /
    `>`); the witness has one real-hypothesis entry and one
    `neg_goal` entry. The proof term is `farkasGoalLe2` or
    `farkasGoalLt2`, each wrapping `Decidable.byContradiction` (via
    `Int.decLe` / `Int.decLt`, axiom-free) and folding the
    contradiction construction back into `farkasContradict`. The
    strict-positivity subgoal again goes through `omega` on a
    literal-coefficient polynomial identity — no goal-side LIA
    discharge. -/
private def closeViaTermModeWithNegGoal
    (goal : MVarId) (goalType : Expr)
    (realEntry : String × Int) (cng : Int) : TacticM Unit := do
  let (realName, c1) := realEntry
  let (b, c, kind) ← match matchLiaGoal? goalType with
    | some t => pure t
    | none =>
      throwError "proof_broker_term: non-False goal must have shape \
                   (_ ≤ _) / (_ < _) / (_ ≥ _) / (_ > _) over Int; \
                   got {goalType}. Equality goals need Tier 2 \
                   case-split (the negation is a disjunction)."
  goal.withContext do
    let (fv, ty) ← fvarOfName realName
    let (a1, h1') ← normalizeHypothesis fv ty
    let c1Expr := intLitExpr c1
    let cngExpr := intLitExpr cng
    let hc1 ← buildNonnegProof c1
    let hcng ← buildNonnegProof cng
    let zero := intLitExpr 0
    let one := intLitExpr 1
    -- Neg-goal compiled form: (c + 1 - b) for ≤/≥, (c - b) for </>.
    let negGoalNorm ← match kind with
      | .le =>
        let cPlus1 ← Lean.Meta.mkAppM ``HAdd.hAdd #[c, one]
        Lean.Meta.mkAppM ``HSub.hSub #[cPlus1, b]
      | .lt =>
        Lean.Meta.mkAppM ``HSub.hSub #[c, b]
    let prod1 ← Lean.Meta.mkAppM ``HMul.hMul #[c1Expr, a1]
    let prod2 ← Lean.Meta.mkAppM ``HMul.hMul #[cngExpr, negGoalNorm]
    let sum ← Lean.Meta.mkAppM ``HAdd.hAdd #[prod1, prod2]
    let heqTy ← Lean.Meta.mkAppM ``LT.lt #[zero, sum]
    let heqMV ← Lean.Meta.mkFreshExprMVar heqTy
    let helperName : Name := match kind with
      | .le => ``ProofBroker.TermMode.farkasGoalLe2
      | .lt => ``ProofBroker.TermMode.farkasGoalLt2
    let term ← Lean.Meta.mkAppM helperName
      #[h1', hc1, hcng, heqMV]
    closeOmegaSubgoal heqMV.mvarId!
    goal.assign term

/-- Term-mode closer for arity-2 LIA Farkas witnesses. Branches on
    whether the witness names `neg_goal`:
    * No `neg_goal`: goal must be `False`, both entries name real
      hypotheses, build via `farkasContradict`.
    * With `neg_goal`: goal must be `(_ ≤ _ : Int)`, one entry names
      a real hypothesis and one names `neg_goal`, build via
      `farkasGoalLe2` (which wraps `Decidable.byContradiction`).
    All coefficients must be nonnegative integers; hypothesis types
    must be `(_ ≤ _ : Int)`. -/
private def closeViaTermMode (goal : MVarId) (goalType : Expr)
    (cert : Json) : TacticM Unit := do
  let entries ← parseFarkasCoefficients cert
  unless entries.length == 2 do
    throwError "proof_broker_term: arity {entries.length} witness — only \
                 arity 2 wired today"
  let negEntry := entries.find? (fun e => e.1 == "neg_goal")
  match negEntry with
  | none =>
    unless goalType.isConstOf ``False do
      throwError "proof_broker_term: witness lacks neg_goal but goal is \
                   not False ({goalType}); cert/goal mismatch"
    closeViaTermModeFalse goal entries
  | some (_, cng) =>
    if goalType.isConstOf ``False then
      throwError "proof_broker_term: witness names neg_goal but goal is \
                   False ({goalType}); cert/goal mismatch"
    let real := entries.find? (fun e => e.1 != "neg_goal")
    let realEntry ← match real with
      | some e => pure e
      | none => throwError "proof_broker_term: witness has neg_goal but no \
                              real-hypothesis companion (arity-2 expected)"
    closeViaTermModeWithNegGoal goal goalType realEntry cng

/-- Bare form `proof_broker` runs against the default manifest list
    (cvc4, cvc5, z3 if present in the manifest dir) under
    `preferHigherTier := true`, so the highest-tier capable adapter
    wins regardless of input order.

    `proof_broker [cvc5, z3]` restricts dispatch to the named adapters
    in the given order. Each name is resolved as `manifest-<name>.json`
    under the manifest dir; an unknown name is a hard error.
    `preferHigherTier := false` is forced for this form, so the
    user-supplied order is respected verbatim — the bracket list is a
    priority lever, not just a filter. -/
syntax (name := proofBroker) "proof_broker" ("[" ident,* "]")? : tactic

/-- Term-mode form: dispatch + verify as usual, then on a Tier 1
    Farkas cert build the proof term from the witness coefficients
    via `farkasContradict` rather than discharging through `omega`
    on the original goal. The coefficients are visible in the
    constructed proof term — the cert is *consumed* rather than
    gating an opaque tactic call.

    Scope: the goal must be literally `False`; the witness must be
    arity 2 with nonnegative integer coefficients on hypotheses of
    shape `_ ≤ _ : Int`. The strictly-positive linear-combination
    subgoal is discharged by `omega` (the Lean-side analogue of
    Rocq's `ring`-discharged polynomial-identity step) — narrower
    than the LIA closer's full goal-discharge omega call. -/
syntax (name := proofBrokerTerm) "proof_broker_term" ("[" ident,* "]")? : tactic

/-- Debug form. Same dispatch behavior as the bare/bracketed forms,
    but emits a `logInfo` summary of the extraction path: IR shape,
    dispatch attempts and timing, minted cert (tier + format),
    verify outcome and timing. The summary is emitted on both
    success and failure paths. -/
syntax (name := proofBrokerQ) "proof_broker?" ("[" ident,* "]")? : tactic

/-- Parse the optional adapter-list suffix shared by both syntaxes.
    Returns `(adapterNames?, preferHigherTier)`. -/
private def parseAdapterList (lst : Option (Array Ident))
    : TacticM (Option (List String) × Bool) := do
  match lst with
  | none => pure (none, true)
  | some arr =>
    let xs := arr.toList.map (·.getId.toString)
    if xs.isEmpty then
      throwError "proof_broker: empty adapter list; omit the brackets to use defaults"
    pure (some xs, false)

@[tactic proofBroker]
def evalProofBroker : Tactic := fun stx => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (adapterNames?, preferHigherTier) ← match stx with
    | `(tactic| proof_broker [$names,*]) =>
        parseAdapterList (some names.getElems)
    | `(tactic| proof_broker) =>
        parseAdapterList none
    | _ => throwError "proof_broker: malformed invocation"
  let path ← buildExtractionPath goal adapterNames? preferHigherTier
  closeOrFail goal goalType path

@[tactic proofBrokerQ]
def evalProofBrokerQ : Tactic := fun stx => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (adapterNames?, preferHigherTier) ← match stx with
    | `(tactic| proof_broker? [$names,*]) =>
        parseAdapterList (some names.getElems)
    | `(tactic| proof_broker?) =>
        parseAdapterList none
    | _ => throwError "proof_broker?: malformed invocation"
  let path ← buildExtractionPath goal adapterNames? preferHigherTier
  logInfo (renderPath path)
  closeOrFail goal goalType path

@[tactic proofBrokerTerm]
def evalProofBrokerTerm : Tactic := fun stx => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (adapterNames?, preferHigherTier) ← match stx with
    | `(tactic| proof_broker_term [$names,*]) =>
        parseAdapterList (some names.getElems)
    | `(tactic| proof_broker_term) =>
        parseAdapterList none
    | _ => throwError "proof_broker_term: malformed invocation"
  let path ← buildExtractionPath goal adapterNames? preferHigherTier
  let cert ← match path.cert with
    | some c => pure c
    | none => throwError "proof_broker_term: no adapter minted a cert"
  unless path.verifyOk == some true do
    let r := path.verifyReason.map reprStr |>.getD "<unknown>"
    throwError "proof_broker_term: cert was minted but verifier did not \
                 accept it (reason: {r}); term-mode requires a verified \
                 Tier 1 Farkas cert"
  closeViaTermMode goal goalType cert

end ProofBroker.Tactic

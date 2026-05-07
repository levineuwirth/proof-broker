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

/-- Decode a type `Expr` as an IR `TypeRef`. Core handles `Int`;
    everything else falls through to the registered `reifierExt`,
    erroring only when no extension recognizes it either. -/
def reifyType (ty : Expr) : MetaM TypeRef := do
  if ty.isConstOf ``Int then return "Int"
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

/-- Confirm that a comparison/equality at type `α` is over a
    fragment we can reify — `Int` always; anything else only if
    the extension's `reifyType` recognizes it. The reified IR
    term's type tag isn't carried through `LE.le` / `LT.lt`
    explicitly (the OCaml side derives it from the operand
    types), so we only need to gate, not capture. -/
def expectArithCarrier (α : Expr) : MetaM Unit := do
  if α.isConstOf ``Int then return
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
  -- Extension-provided literal recognizer (e.g. Real OfNat / OfScientific).
  if let some ext ← reifierExt.get then
    if let some (val, ty) ← ext.matchLiteralExt e then
      return .numLit val ty
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      return .app "HAdd.hAdd" [] [← reifyTerm a, ← reifyTerm b]
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      return .app "HSub.hSub" [] [← reifyTerm a, ← reifyTerm b]
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      return .app "HMul.hMul" [] [← reifyTerm a, ← reifyTerm b]
  | (``Neg.neg, #[_, _, a]) =>
      return .app "Neg.neg" [] [← reifyTerm a]
  | (``LE.le, #[α, _, a, b]) =>
      expectArithCarrier α
      return .app "LE.le" [] [← reifyTerm a, ← reifyTerm b]
  | (``LT.lt, #[α, _, a, b]) =>
      expectArithCarrier α
      return .app "LT.lt" [] [← reifyTerm a, ← reifyTerm b]
  | (``GE.ge, #[α, _, a, b]) =>
      expectArithCarrier α
      return .app "LE.le" [] [← reifyTerm b, ← reifyTerm a]
  | (``GT.gt, #[α, _, a, b]) =>
      expectArithCarrier α
      return .app "LT.lt" [] [← reifyTerm b, ← reifyTerm a]
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
      throwError "proof_broker: unsupported expression: {e}"

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
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty := decl.type
    if ← isProp ty then
      let shell ← reifyTerm ty
      hypotheses := hypotheses ++ [{ name := decl.userName.toString, shell }]
    else if ty.isConstOf ``Int then
      freeVars := freeVars ++ [{ name := decl.userName.toString, ty := "Int" }]
    else
      match extOpt with
      | some ext =>
        match ← ext.freeVarType ty with
        | some tref =>
          freeVars := freeVars ++ [{ name := decl.userName.toString, ty := tref }]
          sawExtensionType := true
        | none => pure ()
      | none => pure ()
  -- Pick fragment label: extension wins if it claimed any free var,
  -- otherwise default to LIA. The OCaml-side adapters derive the
  -- effective fragment from term types anyway, so this label is
  -- mostly about routing through the right capability_match path.
  let fragment :=
    match extOpt with
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
  let mut verifyReason : Option CertReason := none
  let mut verifyMs : Nat := 0
  if let some cert := dispatch.cert then
    let t1 ← IO.monoMsNow
    let verif ← match runVerifyCertificate cert ir with
      | .ok v => pure v
      | .error e => throwError "proof_broker: verify_certificate failed: {repr e}"
    verifyMs ← msSince t1
    verifyOk := some verif.ok
    verifyReason := some verif.reason
  return {
    ir, attempts := dispatch.attempts, cert := dispatch.cert,
    verifyOk, verifyReason, dispatchMs, verifyMs
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
  match path.cert, path.verifyOk with
  | some cert, some true =>
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
    else
      -- Non-LIA: dispatch through the registered ReifierExt's
      -- closer if present (e.g. ProofBrokerMathlib registers a
      -- linarith closer for "LRA"); otherwise fall back to the
      -- trust axiom. The cert verification gates the call either
      -- way, so the closer can trust solvability.
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
  | some _, some false =>
    let r := path.verifyReason.map reprStr |>.getD "<unknown>"
    throwError "proof_broker: cert minted but verifier rejected: {r}"
  | some _, none =>
    -- Should not happen: cert present implies verify ran. Treat as a bug.
    throwError "proof_broker: internal — cert present but verify outcome missing"

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

end ProofBroker.Tactic

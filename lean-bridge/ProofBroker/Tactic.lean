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
    depend on any axiom. The fragment comes from the cert's
    `refinement_record`.
  * Anything else (`verifiedFarkas` over LRA via the registered
    `linarith` closer, BV via `decide`, UF via `subst_eqs`/`simp_all`)
    closes with an axiom-free Lean tactic. If no sound closer can
    discharge a certified goal, the tactic FAILS (`throwError`) and
    leaves the goal open — it never closes via an admitted axiom.
    Reifying the cert into a term-mode Lean proof — Farkas
    combination from the Tier 1 witness, or the Alethe walker for
    Tier 3 (now wired in for alethe-2024 traces on LIA:
    `tryAletheWalker` / `ProofBroker.Alethe`, omega as the
    fallback) — is the principled finish; until a fragment has one,
    an uncloseable certified goal is a tactic error, not a theorem.
  * The LLM `lean-tactic-script` Tier-3 cert (an untrusted oracle
    the OCaml verifier deliberately leaves soundness-unchecked,
    `tier3ReplayDeferred`) takes a distinct path:
    `replayLlmScriptOrFail` elaborates the script as `(by …)`
    against the goal, then accepts iff the *replayed* proof term's
    transitive axiom footprint ⊆ `{propext, Classical.choice,
    Quot.sound}`. `sorry`/`admit` (`sorryAx`), `native_decide`
    (`Lean.ofReduceBool`), or any bespoke axiom ⇒ tactic failure,
    never an admitted theorem. The LLM cannot widen the trust base.
  * Goal/hypothesis reification covers the LIA fragment only (Int with
    +, -, negation, multiplication by integer literal; ≤, <, =; ¬, ∧,
    ∨). Anything outside this fragment fails fast with a
    `proof_broker: unsupported …` error from the reifier.

There is NO trust axiom: the broker's verdict gates which closer is
invoked, but the Lean proof term is always produced by an axiom-free
tactic (`omega`/`decide`/`subst_eqs`/`linarith`). A certified goal
with no sound closer is reported as a tactic failure (audit H1).
-/

import Lean
import ProofBroker.IR
import ProofBroker.Bridge
import ProofBroker.TermMode
import ProofBroker.Alethe

namespace ProofBroker.Tactic

open Lean Lean.Elab.Tactic Lean.Meta ProofBroker.IR

/- Audit H1: the former `axiom proofBrokerCertSound : ∀ (P : Prop), P`
   was removed. It was an inconsistent axiom (it proves `False`) used
   as an unconditional fallback when no Lean-side closer could
   discharge a broker-certified goal. Kernel soundness for non-LIA
   fragments rested entirely on a CI allowlist gate rather than on
   Lean's kernel. The fallback sites now `throwError` instead, so an
   uncloseable certified goal is a tactic failure — never an admitted
   theorem. Reintroducing a closer for a fragment is the way to
   discharge such goals; reintroducing the axiom is not. -/

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
    * `tier2CaseSplitCloser` is the term-mode closer for Tier 2
      `case_split_farkas` certs over LRA. The cert payload carries
      per-disjunct Farkas witnesses keyed on a `case` hypothesis
      name; the closer destructs the disjunctive IR hypothesis and
      applies the matching witness per branch via Mathlib-side
      Real-typed `rFarkasContradict` helpers. Core delegates here
      whenever the cert payload is a Tier 2 case-split lemma list
      and the fragment is the extension's `irFragment` (LRA). LIA
      Tier 2 isn't reachable today (cvc5's adapter only mints Tier 2
      case-split for LRA goals), but if a future adapter does, core
      would handle that path directly without consulting the
      extension.
    * `irFragment` is the IR's `firstOrderFragment` label to use
      when the extension is active and any free var is in an
      extension-recognized type. Core picks `"LIA"` by default. -/
structure ReifierExt where
  reifyType : Expr → MetaM (Option TypeRef)
  freeVarType : Expr → MetaM (Option TypeRef)
  matchLiteralExt : Expr → MetaM (Option (String × TypeRef))
  lraCloser : TacticM Unit
  /-- Tier 2 case-split closer. Arguments:
      `cert` — the full cert JSON (extension parses `payload.lemmas_used`
      and `payload.structural_hint.disjunctive_hypothesis`),
      `ir` — the IR the cert is over (needed to look up the
      disjunctive hypothesis shell + extend per branch with the
      case hypothesis matching the SDK's "case" name). -/
  tier2CaseSplitCloser : Lean.Json → IR → TacticM Unit
  /-- Tier 1 Farkas closer for the extension's fragment. Called when
      the cert is a verified Tier 1 Farkas witness and the IR's
      first-order fragment matches the extension's `irFragment`
      (eg LRA). Handles both False-goal and comparison-goal cases —
      the extension's closer is responsible for goal-shape dispatch
      (False vs ≤ / < / ≥ / > / =) within those branches. Core
      delegates here instead of running its own Int-only closer
      whenever the extension claims the fragment, so Int / LIA goals
      stay on the core path. Equality goals are pre-split by core
      before this is invoked (see `tier1EqSplit`). -/
  tier1FarkasCloser : Lean.Json → IR → TacticM Unit
  /-- Equality-goal split tactic for the extension's fragment.
      Invoked by core's `evalProofBrokerTerm` when the goal is an
      `Eq α a b` with `α` claimed by `reifyType`. The extension's
      tactic typically calls `apply le_antisymm` (the Mathlib
      generic, not `Int.le_antisymm` — that's the core-Int path's
      antisym lemma and lives outside the extension's scope).
      Core relies on the extension for this because the antisym
      lemma name isn't resolvable in core (Mathlib-free), and using
      a syntax quotation here would surface as `le_antisymm✝`. -/
  tier1EqSplit : TacticM Unit
  irFragment : String
  /-- Closer for a broker-certified higher-order / FOL goal
      (fragment `"HOL"` / `"FOL"`), i.e. a Vampire Tier-3 TSTP
      (`verifiedTier3Provenance`) or Tier-0 oracle cert. The cert
      gates the call (the OCaml `Tier3_tptp` provenance check, or
      Vampire's SZS Theorem, already accepted the goal as
      provable), so the closer may delegate to general
      automation — `ProofBrokerMathlib` registers `aesop` — and
      the resulting Lean proof term is axiom-free (aesop builds a
      kernel term; the cert never enters the trust footprint —
      audit H1). With no extension registered, core `throwError`s
      rather than admit, exactly as the LRA path does. -/
  holCloser : TacticM Unit

initialize reifierExt : IO.Ref (Option ReifierExt) ← IO.mkRef none

/-- Applied global constants encountered during reification that
    are not connectives/quantifiers (e.g. `Function.comp`) — the
    higher-order/FOL path treats them as uninterpreted symbols and
    must declare them as IR `freeVars` so the TPTP serializer has a
    monomorphic type. Threaded as a module ref because `reifyTerm`
    is a standalone `def`; `buildIR` clears it on entry, folds the
    collected `(name, typeRef)` pairs into `freeVars` on exit, and
    nothing else touches it (single-goal reification is
    sequential). -/
initialize reifyConsts : IO.Ref (Array (String × TypeRef)) ← IO.mkRef #[]

/-- R3-M1: nonlinear-ℕ atomization table, `payload_id ↦ the ℕ
    subterm it stands for` (e.g. `Zmax * zhigh`). Filled by
    `Reify.reifyNatTerm` when a product with no literal factor (or a
    non-foldable power) is atomized to an IR `Opaque` node; consumed
    by `buildIR` (payloads + nonneg hypotheses) and by the ℕ→ℤ lift
    (the walker context maps the id back to `↑<subterm>`). Same
    threading discipline as `reifyConsts`: `buildIR` clears it on
    entry, single-goal reification is sequential. -/
initialize reifyNatAtoms : IO.Ref (Array (String × Expr)) ← IO.mkRef #[]

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
    -- Walk every arrow in the chain. A domain that is *itself* an
    -- arrow (a higher-order argument, e.g. the `(Nat→Nat)` in
    -- `(Nat→Nat)→Prop`) is parenthesized so the encoding is
    -- unambiguous: `(Nat->Nat)->Prop`. The SDK's TPTP
    -- `parse_ty` handles these parens; the SMT `parse_arrow_type`
    -- (rightmost-split, first-order only) is never reached for
    -- higher-order goals because they route to Vampire, not SMT.
    let mut t := ty
    let mut parts : Array TypeRef := #[]
    while t.isArrow do
      let dom := t.bindingDomain!
      let d ← reifyType dom
      parts := parts.push (if dom.isArrow then "(" ++ d ++ ")" else d)
      t := t.bindingBody!
    parts := parts.push (← reifyType t)
    return String.intercalate "->" parts.toList
  match ← reifierExt.get with
  | some ext =>
    match ← ext.reifyType ty with
    | some t => return t
    | none =>
      -- A bare type constant the extension declined (e.g. `Nat`,
      -- `String`, a user inductive) is an uninterpreted base sort
      -- for the FOL/HOL (Vampire) path: the TPTP serializer
      -- declares it as a `$tType`. Not reachable on the LIA/LRA
      -- paths (Int/Real handled above / by the ext).
      if ty.isConst then return toString ty.constName!
      throwError "proof_broker: unsupported type {ty}"
  | none =>
    if ty.isConst then return toString ty.constName!
    throwError "proof_broker: unsupported type {ty}; LIA scope is Int only"

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

/- ============================================================
   R3-M1: ℕ→ℤ specialization — the ℕ reifier

   A ℕ goal is reified as its ℤ image (what `zify` produces): every
   ℕ atom occurrence sits under the IR cast symbol `Int.ofNat`,
   literals become Int numerals, `+`/`*`-by-literal distribute, and
   the ℕ-ness of each atom is carried by explicit `0 ≤ ↑x`
   hypotheses `buildIR` appends (`_pb_nonneg_*`). The specialization
   is DOCUMENTED, not silent: `buildIR` emits a `primitive`-kind
   type_metadata entry for `Nat` whose theory_tags name the
   embedding and its witness lemmas (`embedding_witness:` tags →
   the refinement record's real soundness_witness), plus
   library_provenance entries with content hashes for those lemmas.

   Fail-fast scope (the truncation attack surface): ℕ subtraction,
   division, modulo are REJECTED — `a - b` over ℕ is truncated and
   a naive cast to `↑a - ↑b` would be unsound. A product with no
   literal factor (the D1 `Zmax * zhigh` shape) or a non-foldable
   power is atomized to an `Opaque` node: a fresh Int atom, nonneg
   like every ℕ atom, whose payload records the original term.
   ============================================================ -/

/-- Recognize an `OfNat.ofNat` literal at type `Nat` (the form
    `(5 : ℕ)` elaborates to) or a bare raw ℕ literal. -/
def matchNatLiteralAtNat? (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[α, n, _inst]) =>
    if α.isConstOf ``Nat then n.rawNatLit? else none
  | _ => e.rawNatLit?

/-- The IR cast symbol both bridges normalize their surface heads
    to (Lean `Int.ofNat`/`Nat.cast`, Rocq `Z.of_nat`); the SDK's
    `Farkas.linearize` / `Smtlib.emit` / `Tier3_alethe` treat it as
    transparent. -/
def natCastSymbol : String := "Int.ofNat"

/-- Atomize a nonlinear ℕ subterm: reuse the existing payload id if
    this exact `Expr` was seen before (structural equality — the
    same product mentioned twice is one atom), else mint
    `_pb_atom_<k>` and record it. The shell is the atom under the
    cast, like any ℕ atom. -/
def atomizeNatTerm (e : Expr) : MetaM ShellTerm := do
  let atoms ← reifyNatAtoms.get
  let id ← match atoms.find? (fun (_, e') => e' == e) with
    | some (id, _) => pure id
    | none =>
      let id := s!"_pb_atom_{atoms.size}"
      reifyNatAtoms.modify (·.push (id, e))
      pure id
  return .app natCastSymbol [] [.opaque_ id]

/-- Reify a ℕ-typed `Expr` into the ℤ image of its value (casts
    pushed to atoms). Scope: variables, literals, `+`, `*` (with a
    literal factor — otherwise atomized), `^` with literal base and
    exponent (constant-folded; otherwise atomized). ℕ subtraction /
    division / modulo fail fast — never cast naively. -/
partial def reifyNatTerm (e : Expr) : MetaM ShellTerm := do
  if let some n := matchNatLiteralAtNat? e then
    return .numLit (toString n) "Int"
  if e.isFVar then
    let decl := (← getLCtx).get! e.fvarId!
    unless decl.type.isConstOf ``Nat do
      throwError "proof_broker: ℕ reifier reached non-ℕ variable \
        {decl.userName} : {decl.type}"
    return .app natCastSymbol [] [.var decl.userName.toString]
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, _, a, b]) =>
    unless α.isConstOf ``Nat do
      throwError "proof_broker: ℕ reifier reached + at {α}"
    return .app "HAdd.hAdd" [] [← reifyNatTerm a, ← reifyNatTerm b]
  | (``HMul.hMul, #[α, _, _, _, a, b]) =>
    unless α.isConstOf ``Nat do
      throwError "proof_broker: ℕ reifier reached * at {α}"
    -- Linear iff a factor is a literal; otherwise the product is a
    -- nonlinear atom (the D1 `Zmax * zhigh` shape).
    if let some k := matchNatLiteralAtNat? a then
      return .app "HMul.hMul" [] [.numLit (toString k) "Int", ← reifyNatTerm b]
    else if let some k := matchNatLiteralAtNat? b then
      return .app "HMul.hMul" [] [← reifyNatTerm a, .numLit (toString k) "Int"]
    else
      atomizeNatTerm e
  | (``HPow.hPow, #[_, _, _, _, a, b]) =>
    (match matchNatLiteralAtNat? a, matchNatLiteralAtNat? b with
     | some base, some exp =>
       -- Constant-fold closed powers (`2^24` is the numeral
       -- 16777216 in the image; the lift re-folds by kernel defeq).
       -- The bound keeps a pathological exponent from building a
       -- gigantic numeral at reify time; 2^64-scale literals (R4
       -- D2) stay comfortably inside.
       if exp > 256 then
         throwError "proof_broker: ℕ power exponent {exp} exceeds the \
           constant-folding bound (256)"
       else
         return .numLit (toString (base ^ exp)) "Int"
     | _, _ => atomizeNatTerm e)
  | (``HSub.hSub, #[_, _, _, _, _, _]) =>
    throwError "proof_broker: ℕ subtraction is truncated (`a - b` is \
      not the ℤ difference), so the ℕ→ℤ specialization refuses it \
      rather than cast naively; restate without ℕ subtraction (e.g. \
      move the subtrahend to the other side as an addition)"
  | (``HDiv.hDiv, _) | (``HMod.hMod, _) =>
    throwError "proof_broker: ℕ division/modulo are outside the ℕ→ℤ \
      specialization (scope: +, *, ^ with literal exponent, literals, \
      variables; nonlinear products atomize)"
  | _ =>
    throwError "proof_broker: unsupported ℕ term {e} (ℕ→ℤ scope: +, \
      * with a literal factor, ^ with literal base and exponent, \
      literals, variables; nonlinear products atomize)"

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
  -- Implication / universal quantification (higher-order & FOL
  -- reach). `A → B` is a non-dependent `forallE` (`isArrow`):
  -- reify as `.implies`. `∀ (x : T), body` with the body
  -- depending on `x`, or any non-Prop binder, is a real
  -- quantifier: introduce the binder as a local so the bound
  -- occurrences reify as `.var`, then `.forall_`. A dependent
  -- Prop-binder (`∀ (_ : P), Q[_]`) collapses to `.implies`
  -- ignoring the unused proof term — the LIA path never produced
  -- these so behavior there is unchanged.
  if e.isArrow then
    return .implies (← reifyTerm e.bindingDomain!) (← reifyTerm e.bindingBody!)
  if e.isForall then
    return ← forallBoundedTelescope e (some 1) fun xs body => do
      let x := xs[0]!
      let decl := (← getLCtx).get! x.fvarId!
      let dom := decl.type
      if ← isProp dom then
        return .implies (← reifyTerm dom) (← reifyTerm body)
      else
        -- R3-M1 scope: a ℕ-sorted quantifier inside a shell has no
        -- ℤ image yet (it would need the bounded-∀ transform); a
        -- TOP-LEVEL ∀ (n : ℕ) goal is handled by the tactic
        -- front-end, which introduces the binder before reifying.
        if dom.isConstOf ``Nat then
          throwError "proof_broker: ∀ over ℕ inside a formula is \
            outside the ℕ→ℤ specialization (a leading ∀ (n : ℕ) on \
            the goal is introduced automatically; nested ℕ \
            quantifiers are not yet translated)"
        let tref ← reifyType dom
        return .forall_ decl.userName.toString tref (← reifyTerm body)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, _, a, b]) =>
      -- BV vs arithmetic disambiguation: SMT-LIB uses bvadd /
      -- bvsub / bvmul rather than the polymorphic + / - / *, so
      -- the IR carries them under different App symbols. Picked
      -- at reify time from the operand type.
      let sym := if (matchBitVecType? α).isSome then "BV.add" else "HAdd.hAdd"
      return .app sym [] [← reifyTerm a, ← reifyTerm b]
  | (``HSub.hSub, #[α, _, _, _, a, b]) =>
      -- R3-M1 attack surface: ℕ subtraction is truncated — never
      -- cast naively, never reify as ordinary subtraction.
      if α.isConstOf ``Nat then
        throwError "proof_broker: ℕ subtraction is truncated (`a - b` \
          is not the ℤ difference); the ℕ→ℤ specialization refuses it \
          — restate without ℕ subtraction"
      let sym := if (matchBitVecType? α).isSome then "BV.sub" else "HSub.hSub"
      return .app sym [] [← reifyTerm a, ← reifyTerm b]
  | (``HMul.hMul, #[α, _, _, _, a, b]) =>
      let sym := if (matchBitVecType? α).isSome then "BV.mul" else "HMul.hMul"
      return .app sym [] [← reifyTerm a, ← reifyTerm b]
  | (``Neg.neg, #[_, _, a]) =>
      return .app "Neg.neg" [] [← reifyTerm a]
  | (``LE.le, #[α, _, a, b]) =>
      -- R3-M1: ℕ comparisons reify as their ℤ image.
      if α.isConstOf ``Nat then
        return .app "LE.le" [] [← reifyNatTerm a, ← reifyNatTerm b]
      expectArithCarrier α
      -- Lean's [<=] over BitVec resolves to BitVec.ule (unsigned).
      -- Signed comparisons need [BitVec.sle] written explicitly.
      let sym := if (matchBitVecType? α).isSome then "BV.ule" else "LE.le"
      return .app sym [] [← reifyTerm a, ← reifyTerm b]
  | (``LT.lt, #[α, _, a, b]) =>
      if α.isConstOf ``Nat then
        return .app "LT.lt" [] [← reifyNatTerm a, ← reifyNatTerm b]
      expectArithCarrier α
      let sym := if (matchBitVecType? α).isSome then "BV.ult" else "LT.lt"
      return .app sym [] [← reifyTerm a, ← reifyTerm b]
  | (``GE.ge, #[α, _, a, b]) =>
      if α.isConstOf ``Nat then
        return .app "LE.le" [] [← reifyNatTerm b, ← reifyNatTerm a]
      expectArithCarrier α
      let sym := if (matchBitVecType? α).isSome then "BV.ule" else "LE.le"
      return .app sym [] [← reifyTerm b, ← reifyTerm a]
  | (``GT.gt, #[α, _, a, b]) =>
      if α.isConstOf ``Nat then
        return .app "LT.lt" [] [← reifyNatTerm b, ← reifyNatTerm a]
      expectArithCarrier α
      let sym := if (matchBitVecType? α).isSome then "BV.ult" else "LT.lt"
      return .app sym [] [← reifyTerm b, ← reifyTerm a]
  | (``Eq, #[α, a, b]) =>
      -- R3-M1: an equality at ℕ images to an Int equality of the
      -- cast operands.
      if α.isConstOf ``Nat then
        return .eq "Int" (← reifyNatTerm a) (← reifyNatTerm b)
      let tref ← reifyType α
      return .eq tref (← reifyTerm a) (← reifyTerm b)
  | (``Ne, #[α, a, b]) =>
      -- `a ≠ b` unfolds to `¬(a = b)`; reify it that way so the
      -- SMT serializer sees the ordinary (not (= a b)) shape
      -- instead of an uninterpreted `Ne` symbol.
      if α.isConstOf ``Nat then
        return .not_ (.eq "Int" (← reifyNatTerm a) (← reifyNatTerm b))
      let tref ← reifyType α
      return .not_ (.eq tref (← reifyTerm a) (← reifyTerm b))
  | (``Nat.cast, #[α, _, a]) | (``NatCast.natCast, #[α, _, a]) =>
      -- R3-M1: an explicit ℕ→ℤ cast in the source (a hand-zify'd
      -- goal) reifies as the operand's ℤ image — same shell the ℕ
      -- reifier produces, so mixed `↑x`-style Int goals join the
      -- specialization path.
      if α.isConstOf ``Int then reifyNatTerm a
      else throwError "proof_broker: ℕ cast into {α} unsupported \
             (only ↑(ℕ) : ℤ)"
  | (``Int.ofNat, #[a]) =>
      reifyNatTerm a
  | (``Exists, #[α, p]) =>
      -- `∃ x : T, body` is `Exists fun x => body`. Open the
      -- lambda binder as a local so bound occurrences reify as
      -- `.var`, then emit the IR's `Exists` shell (the SDK
      -- serializer renders `(exists ((x T)) body)`).
      (match p with
       | .lam nm _ _ _ => do
         -- R3-M1 scope: same rule as ∀ — no ℕ-sorted binders in
         -- shells (see the forall arm).
         if α.isConstOf ``Nat then
           throwError "proof_broker: ∃ over ℕ is outside the ℕ→ℤ \
             specialization (nested ℕ quantifiers are not yet \
             translated)"
         let tref ← reifyType α
         withLocalDeclD nm α fun x => do
           let body := (p.bindingBody!).instantiate1 x
           return .exists_ nm.toString tref (← reifyTerm body)
       | _ =>
         throwError "proof_broker: unsupported ∃ shape (expected a \
           lambda body): {e}")
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
      -- Higher-order / FOL: an applied (or nullary) global
      -- constant that isn't a connective — e.g. `Function.comp`.
      -- Treat it as an uninterpreted symbol: keep only the
      -- explicit (non-type, non-instance) arguments, register the
      -- constant with its monomorphic arrow type so `buildIR`
      -- declares it as an IR `freeVar` (the TPTP serializer
      -- requires a declaration), and emit a plain `.app`.
      if fn.isConst then
        let cname := toString fn.constName!
        let allArgs := e.getAppArgs
        let mut explicit : Array Expr := #[]
        for a in allArgs do
          let ta ← inferType a
          let isType := ta.isSort
          let isInst := (← Lean.Meta.isClass? ta).isSome
          if !isType && !isInst then explicit := explicit.push a
        let parenIfArrow (ex : Expr) (s : String) : String :=
          if ex.isArrow then "(" ++ s ++ ")" else s
        let argTyParts ← explicit.toList.mapM (fun a => do
          let ta ← inferType a
          return parenIfArrow ta (← reifyType ta))
        let resTy ← inferType e
        let tref := String.intercalate "->" (argTyParts ++ [← reifyType resTy])
        reifyConsts.modify (·.push (cname, tref))
        let reifiedArgs ← explicit.toList.mapM reifyTerm
        return .app cname [] reifiedArgs
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

/-- Node-presence flags for the honest `features_used` label (R2):
    `(hasForall, hasExists, hasEq)`, walked over one shell. The
    reifier reports only features it actually emitted, with tags
    drawn from the registry's `logical_features` ids. -/
partial def shellQuantEqFlags : ShellTerm → Bool × Bool × Bool
  | .var _ | .const _ | .numLit _ _ | .opaque_ _ => (false, false, false)
  | .forall_ _ _ b => let (_, e, q) := shellQuantEqFlags b; (true, e, q)
  | .exists_ _ _ b => let (f, _, q) := shellQuantEqFlags b; (f, true, q)
  | .lambda _ b | .not_ b => shellQuantEqFlags b
  | .eq _ a b =>
    let (f1, e1, _) := shellQuantEqFlags a
    let (f2, e2, _) := shellQuantEqFlags b
    (f1 || f2, e1 || e2, true)
  | .implies a b | .and_ a b | .or_ a b =>
    let (f1, e1, q1) := shellQuantEqFlags a
    let (f2, e2, q2) := shellQuantEqFlags b
    (f1 || f2, e1 || e2, q1 || q2)
  | .app _ _ args =>
    args.foldl (fun (f, e, q) a =>
      let (f', e', q') := shellQuantEqFlags a
      (f || f', e || e', q || q')) (false, false, false)

/-- The embedding-witness lemmas the ℕ→ℤ lift applies (all core
    Lean, axiom-free): the comparison/equality transfer iffs plus
    the nonneg fact behind every `_pb_nonneg_*` hypothesis. Their
    names flow into the metadata's `embedding_witness:` tags →
    the refinement record's `soundness_witness`, and each gets a
    `library_provenance` entry with a real content hash. -/
def natEmbeddingWitnessLemmas : List Name :=
  [``Int.ofNat_le, ``Int.ofNat_lt, ``Int.ofNat_inj, ``Int.natCast_nonneg]

/-- Provenance entry for one embedding-witness lemma: the defining
    module from the environment, content hash = SHA-256 (via the
    SDK's `content_hash` FFI) of the lemma's pretty-printed
    statement. -/
def natWitnessProvenance (name : Name) : MetaM (String × Provenance) := do
  let env ← Lean.getEnv
  let some info := env.find? name
    | throwError "proof_broker: embedding-witness lemma {name} not found"
  let stmt ← Lean.Meta.ppExpr info.type
  let hash ← match runContentHash (toString stmt) with
    | .ok h => pure h
    | .error e =>
      throwError "proof_broker: content_hash FFI failed: {repr e}"
  let modulePath := env.getModuleIdxFor? name |>.map fun idx =>
    toString env.allImportedModuleNames[idx.toNat]!
  return (name.toString, {
    library := "lean-core",
    version := Lean.versionString,
    modulePath,
    contentHash := hash })

/-- The `primitive`-kind type_metadata entry for `Nat` (spec §4.6;
    the `type_variable` alternative was rejected — its schema
    requires a typeclass instance object ℕ does not have; decision
    recorded in delta.md §5). The `embedding_witness:` tags name
    the lemmas in `natEmbeddingWitnessLemmas`; the SDK refinement
    pass copies them into the `type_specialization` record's
    `soundness_witness`, and check.py requires each to resolve in
    `library_provenance`. -/
def natTypeMetadata : Json :=
  Json.mkObj [
    ("kind", "primitive"),
    ("name", "Nat"),
    ("theory_tags", Json.arr (
      #[Json.str "embeds_into:Int_for_universal_LIA"]
      ++ natEmbeddingWitnessLemmas.toArray.map
           (fun n => Json.str s!"embedding_witness:{n}")))]

/-- Reify the goal + Prop-typed hypotheses + Int-typed free variables
    of `mvarId` into an IR document tagged for the LIA fragment.

    Skips implementation-detail locals (compiler-introduced auxiliary
    decls, e.g. recursors). Hypotheses whose type isn't a Prop are
    treated as data: Int-typed ones become `freeVars`, anything else
    is silently ignored (the goal/Prop reifier will trip on them if
    they're actually referenced). -/
def buildIR (mvarId : MVarId) : MetaM (IR × Array (String × Expr)) :=
  mvarId.withContext do
  -- Instantiate metavariables in the goal type. `apply`-introduced
  -- subgoals may carry deferred unification metavars in their types;
  -- without this, `reifyTerm` sees `?_uniq.N` (pretty-prints as the
  -- user-facing name) and the FVar branch falls through.
  -- Reset the applied-constant accumulator; `reifyTerm` (on the
  -- goal and each hypothesis below) pushes any non-connective
  -- global constant it treats as uninterpreted (e.g.
  -- `Function.comp`) so it can be declared as a `freeVar`.
  reifyConsts.set #[]
  reifyNatAtoms.set #[]
  let goalType ← Lean.instantiateMVars (← mvarId.getType)
  let goalShell ← reifyTerm goalType
  let mut freeVars : List FreeVar := []
  let mut hypotheses : List IR.Hypothesis := []
  let extOpt ← reifierExt.get
  let mut sawExtensionType : Bool := false
  let mut sawBV : Bool := false
  let mut sawUF : Bool := false
  let mut sawNat : Bool := false
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
    else if ty.isConstOf ``Nat then
      -- R3-M1: ℕ locals are arithmetic free vars declared at their
      -- TRUE carrier "Nat"; the SDK refinement pass substitutes
      -- Nat → Int (recorded with a real witness) before the SMT
      -- serializer runs. Shell occurrences sit under the
      -- `Int.ofNat` cast (see `reifyNatTerm`).
      freeVars := freeVars ++ [{ name := decl.userName.toString, ty := "Nat" }]
      sawNat := true
    else if ty.isProp then
      -- A local `p : Prop` is a Boolean ATOM, not a hypothesis
      -- (`isProp ty` above matched locals whose type IS a
      -- proposition; here the type is `Prop` itself). Declare it
      -- as a free var — the SDK serializer maps the `Prop` type
      -- ref to SMT-LIB `Bool` — so pure-propositional goals
      -- (`∀ p q : Prop, …`) dispatch with their atoms declared.
      freeVars := freeVars ++ [{ name := decl.userName.toString, ty := "Prop" }]
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
  -- Fold the applied global constants (`Function.comp`, …) into
  -- freeVars so the TPTP serializer has a monomorphic declaration
  -- for every applied symbol. Skip names already contributed by
  -- the LCtx walk (a constant shadowing a local is not expected,
  -- but dedup keeps the declaration set well-formed).
  for (cname, ctref) in (← reifyConsts.get) do
    if !(freeVars.any (fun fv => fv.name == cname)) then
      freeVars := freeVars ++ [{ name := cname, ty := ctref }]
  let bvInTerms :=
    shellMentionsBV goalShell
    || hypotheses.any (fun h => shellMentionsBV h.shell)
  let ufInTerms :=
    shellMentionsUF goalShell
    || hypotheses.any (fun h => shellMentionsUF h.shell)
  -- Higher-order: a freeVar whose type takes a function argument
  -- (a parenthesized arrow domain, the only source of `(` in a
  -- reified type-ref) — e.g. `P : (Nat->Nat)->Prop` or
  -- `Function.comp : (Nat->Nat)->...`. Such goals route to
  -- Vampire (THF): `order = higher_order` makes `capability_match`
  -- skip the first-order SMT adapters, and `firstOrderFragment =
  -- none` makes it skip the fragment check (the Vampire manifest
  -- advertises FOL/HOL/UF; the cert's refinement fragment is the
  -- closer key, set to "HOL" by the adapter for the THF dialect).
  let isHO := freeVars.any (fun fv => fv.ty.any (· == '('))
  -- R3-M1: ℕ mode = a ℕ free var or an atomized ℕ subterm was seen.
  -- M1 scope: the ℕ→ℤ specialization does not compose with UF / BV /
  -- HO / extension carriers yet — mixing is a named failure, not a
  -- silent mistranslation.
  let natAtoms ← reifyNatAtoms.get
  let natMode := sawNat || !natAtoms.isEmpty
  if natMode && (sawBV || bvInTerms || sawUF || ufInTerms || isHO
                 || sawExtensionType) then
    throwError "proof_broker: ℕ variables cannot mix with UF / BV / \
      higher-order / extension carriers yet (R3-M1 scope: pure ℕ \
      linear arithmetic)"
  if natMode then
    -- Nonneg hypotheses — what `zify` adds: `0 ≤ ↑x` per ℕ free
    -- var, `0 ≤ ↑<subterm>` per atomized ℕ product. These carry the
    -- ℕ-ness of the atoms into the ℤ image; the lift proves them
    -- via `Int.natCast_nonneg`.
    for fv in freeVars do
      if fv.ty == "Nat" then
        hypotheses := hypotheses ++ [{
          name := s!"_pb_nonneg_{fv.name}",
          shell := .app "LE.le" [] [
            .numLit "0" "Int",
            .app natCastSymbol [] [.var fv.name]] }]
    for (id, _) in natAtoms do
      hypotheses := hypotheses ++ [{
        name := "_pb_nonneg_" ++ id.drop "_pb_".length,
        shell := .app "LE.le" [] [
          .numLit "0" "Int",
          .app natCastSymbol [] [.opaque_ id]] }]
  let order := if isHO then "higher_order" else "first_order"
  let fragment :=
    if isHO then "none"
    else if sawBV || bvInTerms then "BV"
    else if sawUF || ufInTerms then "UF"
    else match extOpt with
      | some ext => if sawExtensionType then ext.irFragment else "LIA"
      | none => "LIA"
  -- R2 honesty: the context tier is "structural" whenever typed
  -- hypotheses ride along (spec §4.5: "goal" = proposition only),
  -- and features_used reports what the reifier actually emitted.
  let tier := if hypotheses.isEmpty then "goal" else "structural"
  let (hasForall, hasExists, hasEq) :=
    (goalShell :: hypotheses.map (·.shell)).foldl
      (fun (f, e, q) s =>
        let (f', e', q') := shellQuantEqFlags s
        (f || f', e || e', q || q'))
      (false, false, false)
  let featuresUsed :=
    (if hasForall then ["universal_quantification_over_first_order"] else [])
    ++ (if hasExists then ["existential_quantification_over_first_order"] else [])
    ++ (if hasEq then ["equality_at_first_order_type"] else [])
    ++ (if isHO then ["function_quantification"] else [])
  -- R3-M1: the ℕ→ℤ specialization is documented in the IR itself —
  -- metadata naming the embedding + witnesses, provenance with real
  -- content hashes, and one payload per atomized subterm.
  let typeMetadata := if natMode then [("Nat", natTypeMetadata)] else []
  let libraryProvenance ←
    if natMode then natEmbeddingWitnessLemmas.mapM natWitnessProvenance
    else pure []
  let payloads ←
    if natAtoms.isEmpty then pure none
    else do
      let entries ← natAtoms.toList.mapM (fun (id, e) => do
        let pp ← Lean.Meta.ppExpr e
        return (id, Json.mkObj [
          ("kind", "nat_nonlinear_atom"),
          ("lean", Json.str (toString pp))]))
      pure (some (Json.mkObj entries))
  -- The atom table rides on the RETURN VALUE, not the module ref:
  -- Lean elaborates theorems in parallel, so a ref read at
  -- closer time can race another invocation's `buildIR` reset
  -- (observed as an unknown-free-variable failure). The ref is
  -- only the accumulator WITHIN this reify.
  return ({
    irVersion := "1.0",
    sourceSystem := { name := "lean", version := "0.0" },
    tier,
    logicClassification := {
      order, featuresUsed,
      firstOrderFragment := fragment, decidableTheory := none
    },
    goal := { shell := goalShell, payloads },
    context := { typeVars := [], freeVars, hypotheses, librarySlice := none },
    typeMetadata,
    definitionalMetadata := [],
    libraryProvenance,
    userDirectives := none
  }, natAtoms)

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
  -- vampire last: capability_match skips it for first-order LIA/LRA/BV
  -- goals (its manifest advertises FOL/HOL/UF, not the arithmetic
  -- fragments), and the higher-order goals it does serve have the
  -- SMT adapters skipped via the order check — so ordering is for
  -- determinism, not precedence.
  let names := ["manifest-cvc4.json", "manifest-cvc5.json",
                "manifest-z3.json", "manifest-vampire.json"]
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
  /-- R2: the broker's rewrite trace for this dispatch. Its
      `isIdentity` is the identity-trace guard's input: the
      term-mode / walker closers consume the cert against the
      ORIGINAL goal, so they only run when the trace proves the
      dispatched IR is that goal (`none` — no trace returned —
      fails the guard, closed). -/
  trace : Option Trace.Document
  /-- R2: raw passthrough of the broker's `final_ir` — the IR the
      cert addresses. Verification runs against this, never the
      reified input. -/
  finalIr : Option Json
  /-- R3-M1: `payload_id ↦ ℕ subterm` for every atomized nonlinear
      ℕ product of this extraction (see `Reify.reifyNatAtoms`).
      Carried here — NOT re-read from the module ref — because
      parallel theorem elaboration can reset the ref between the
      reify and the closer. -/
  natAtoms : Array (String × Expr) := #[]
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
  let traceLine := match path.trace with
    | none => "  trace:    none"
    | some d =>
      let idty := if d.isIdentity then "identity" else "NON-IDENTITY"
      s!"  trace:    {idty}, {d.entries.length} pass(es)"
  let verifyLine := match path.verifyOk, path.verifyReason with
    | some ok, some r => s!"  verify:   {path.verifyMs}ms, ok={ok} ({reprStr r})"
    | _, _ => "  verify:   skipped"
  let lines := ["proof_broker?:", irLine, dispatchLine] ++ attemptLines
    ++ [certLine, traceLine, verifyLine]
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
    (tierPreference : Option (List String) := none)
    : TacticM ExtractionPath := do
  let (ir, natAtoms) ← Reify.buildIR goal
  -- Walker-strict callers pass `tierPreference := some ["3"]`:
  -- the IR's `user_directives.tier_preference` (spec §5.4) tells
  -- the cvc5 adapter to mint the verified Tier-3 alethe trace
  -- ahead of the term-mode-friendly Tier-2/1 witnesses. The
  -- default dispatch is unchanged.
  let ir := match tierPreference with
    | none => ir
    | some tp =>
      { ir with userDirectives := some {
          preferredBackend := none, tierPreference := some tp,
          rewriterPreferences := none, budget := none } }
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
    -- R2: the cert addresses the dispatch pipeline's output IR
    -- (`final_ir`), not the reified input — verify against that,
    -- with the trace, so a cert/trace/IR triple that doesn't
    -- cohere is a hash mismatch here rather than a silent pass.
    let irForVerify := dispatch.finalIr.getD (ProofBroker.IR.IR.toJson ir)
    let verif ← match runVerifyCertificateJson cert irForVerify dispatch.trace with
      | .ok v => pure v
      | .error e => throwError "proof_broker: verify_certificate failed: {repr e}"
    verifyMs ← msSince t1
    verifyOk := some verif.ok
    verifyEnvelopeOk := some verif.envelopeOk
    verifyReason := some verif.reason
  return {
    ir, attempts := dispatch.attempts, cert := dispatch.cert,
    trace := dispatch.trace, finalIr := dispatch.finalIr,
    verifyOk, verifyEnvelopeOk, verifyReason, dispatchMs, verifyMs,
    natAtoms
  }

/-- Identity-trace guard (R2 soundness rule). The term-mode and
    walker closers consume the cert's content against the ORIGINAL
    goal, but the cert addresses the dispatch pipeline's output IR.
    Until R3 lands lifting, those closers may only run when the
    trace proves the two coincide: every pass skipped/no-op and
    equal endpoint hashes (`Trace.Document.isIdentity`). A missing
    trace fails the guard — closed. Decision-procedure closers
    (omega & co.) are exempt: they re-prove the original goal
    themselves, so the cert is only a gate there. The guard is
    removed pass-by-pass in R3 as each inversion lands. -/
private def identityTraceOk (path : ExtractionPath) : Bool :=
  match path.trace with
  | some d => d.isIdentity
  | none => false

/- ============================================================
   R3-M1: the ℕ→ℤ lift

   The reifier hands the broker the ℤ image of a ℕ goal; the cert
   addresses that image. To keep "the cert IS the proof" true, the
   cert-consuming closers rebuild the ℕ proof from the ℤ one by
   TERM CONSTRUCTION: apply the `TermMode.natCast*` shims (each a
   direct use of the recorded embedding-witness lemmas) to every
   hypothesis the cert consumes, prove the `_pb_nonneg_*` facts by
   `natCastNonneg`, and run the ordinary Int machinery (Farkas fold
   / Alethe walker) over those ℤ facts. No decision procedure
   touches the original goal on these paths; the byContra step is
   `Decidable.byContradiction` (term mode) or `falseOrByContra`
   (walker, classical baseline).
   ============================================================ -/

/-- ℕ mode of an extraction: the reified IR declared a ℕ free var
    or atomized a ℕ subterm (payloads present). -/
private def natModeOf (ir : IR) : Bool :=
  ir.context.freeVars.any (·.ty == "Nat") || ir.goal.payloads.isSome

/-- Fail-closed specialization gate — the R3 analog of R2's
    identity-trace guard, lifted pass-by-pass as inversions land: a
    cert-consuming closer runs only when every specialization the
    cert records is one this bridge inverts. Today that is exactly
    the ℕ→ℤ type specialization on a ℕ-mode extraction; on any
    other extraction the list must be empty. In ℕ mode the record
    must be PRESENT — a cert minted over a ℕ IR with no recorded
    specialization means refinement did not happen honestly. -/
private def checkCertSpecializations (cert : Json) (natMode : Bool)
    : TacticM Unit := do
  let specs := ((cert.getObjVal? "refinement_record").bind
    (·.getObjVal? "specializations")).toOption.bind
    (·.getArr?.toOption) |>.getD #[]
  let mut sawNatSpec := false
  for s in specs do
    let kind := (s.getObjValAs? String "kind").toOption.getD ""
    let source := (s.getObjValAs? String "source").toOption.getD ""
    let target := (s.getObjValAs? String "target").toOption.getD ""
    if natMode && kind == "type_specialization" && source == "Nat"
        && target == "Int" then
      sawNatSpec := true
    else
      throwError "proof_broker: the cert records a specialization this \
        bridge cannot invert (kind={kind}, {source} → {target}); the \
        goal is left OPEN rather than closed from a cert whose \
        translation has no lift (fail closed)"
  if natMode && !sawNatSpec then
    throwError "proof_broker: ℕ goal, but the cert records no \
      Nat → Int type specialization — refusing to consume it \
      (fail closed)"

/-- `(atom name ↦ its ℕ-level Expr)` for the extraction: ℕ free
    vars resolved in the local context by name, atomized subterms
    from the path's `natAtoms` table. -/
private def natAtomExprs (ir : IR) (tableAtoms : Array (String × Expr))
    : TacticM (Array (String × Expr)) := do
  let lctx ← getLCtx
  let mut out := #[]
  for fv in ir.context.freeVars do
    if fv.ty == "Nat" then
      match lctx.findFromUserName? (Name.mkSimple fv.name) with
      | some decl => out := out.push (fv.name, decl.toExpr)
      | none =>
        throwError "proof_broker: ℕ free var {fv.name} from the IR is \
          not in the local context"
  return out ++ tableAtoms

/-- Shape-dispatch cast: from `h : ty` with `ty` an ℕ comparison /
    equality (possibly negated), build the ℤ-image fact via the
    `TermMode.natCast*` shims. `none` for shapes the lift does not
    cover yet (compound props; the caller decides whether that is
    an error). -/
private def castNatHyp? (h : Expr) (ty : Expr) : MetaM (Option Expr) := do
  -- `falseOrByContra` leaves the negated goal behind an assigned
  -- metavariable (and possibly metadata); resolve both everywhere
  -- or `getAppFnArgs` sees no application.
  let ty := (← Lean.instantiateMVars ty).consumeMData
  let app1 (n : Name) : MetaM (Option Expr) := do
    return some (← Lean.Meta.mkAppM n #[h])
  let matchPos (ty : Expr) : Option Name :=
    match ty.consumeMData.getAppFnArgs with
    | (``LE.le, #[α, _, _, _]) =>
      if α.isConstOf ``Nat then some ``ProofBroker.TermMode.natCastLe else none
    | (``LT.lt, #[α, _, _, _]) =>
      if α.isConstOf ``Nat then some ``ProofBroker.TermMode.natCastLt else none
    | (``GE.ge, #[α, _, _, _]) =>
      if α.isConstOf ``Nat then some ``ProofBroker.TermMode.natCastGe else none
    | (``GT.gt, #[α, _, _, _]) =>
      if α.isConstOf ``Nat then some ``ProofBroker.TermMode.natCastGt else none
    | (``Eq, #[α, _, _]) =>
      if α.isConstOf ``Nat then some ``ProofBroker.TermMode.natCastEq else none
    | _ => none
  -- Negation arrives as `Not P` or as the unfolded `P → False`
  -- (`falseOrByContra` introduces the latter); treat both.
  let notInner? : Option Expr :=
    match ty.getAppFnArgs with
    | (``Not, #[inner]) => some inner
    | _ =>
      if ty.isArrow && ty.bindingBody!.isConstOf ``False
      then some ty.bindingDomain! else none
  match matchPos ty with
  | some lemma_ => app1 lemma_
  | none =>
    match notInner? with
    | some inner =>
      (match matchPos inner with
       | some l =>
         if l == ``ProofBroker.TermMode.natCastLe then
           app1 ``ProofBroker.TermMode.natCastNotLe
         else if l == ``ProofBroker.TermMode.natCastLt then
           app1 ``ProofBroker.TermMode.natCastNotLt
         else if l == ``ProofBroker.TermMode.natCastGe then
           app1 ``ProofBroker.TermMode.natCastNotGe
         else if l == ``ProofBroker.TermMode.natCastGt then
           app1 ``ProofBroker.TermMode.natCastNotGt
         else if l == ``ProofBroker.TermMode.natCastEq then
           app1 ``ProofBroker.TermMode.natCastNotEq
         else return none
       | none => return none)
    | none =>
      match ty.getAppFnArgs with
      | (``Ne, #[α, _, _]) =>
        if α.isConstOf ``Nat then app1 ``ProofBroker.TermMode.natCastNotEq
        else return none
      | _ => return none

/-- Read the fragment label out of a cert's `refinement_record`.
    Returns `""` when the field is missing or the cert is malformed
    in a way the OCaml side wouldn't normally emit; the caller will
    just take the axiom branch on an empty string, which is
    soundness-equivalent. -/
private def certFragment (cert : Json) : String :=
  (cert.getObjVal? "refinement_record"
    |>.bind (·.getObjValAs? String "fragment")).toOption.getD ""

/-- Read `payload.trace_format` (`""` if absent). -/
private def certTraceFormat (cert : Json) : String :=
  (cert.getObjVal? "payload"
    |>.bind (·.getObjValAs? String "trace_format")).toOption.getD ""

/-- Read `payload.trace_data` as a string (`none` if absent or
    non-string — the only shape `Adapter_llm` emits is a JSON
    string). -/
private def certTraceData? (cert : Json) : Option String :=
  (cert.getObjVal? "payload"
    |>.bind (·.getObjValAs? String "trace_data")).toOption

/-- Walk a parsed Alethe proof into a kernel term and assign it
    to `goal`. Shared between the production `tryAletheWalker`
    and the test-only `alethe_walker_test` tactic so both close
    goals through the same logic.

    Two trace shapes are recognized:

    * **Refutation traces** (`Proof.steps.getLast?` has empty
      clause `(cl)`). cvc5's actual output: the walker produces
      a `False`-typed term. For non-`False` user goals, we first
      `MVarId.falseOrByContra` to expose `¬goal` as a hypothesis
      and reduce the goal to `False`; the walker's
      `elabAssumeLiteral` then matches the trace's
      `(assume _ (not goal))` step against that hypothesis by
      `isDefEq`. `falseOrByContra` itself is axiom-safe
      (`Classical.byContradiction`, classical baseline).
    * **Direct traces** (final step's clause non-empty). Used by
      per-rule unit tests (e.g. a standalone `la_generic` leaf
      proving `(cl (<= 0 5))`). The walked term's type matches
      the goal directly — no byContra wrapping.

    Throws on walker failure or walked-term-type mismatch.
    Callers that want a fallback (the production path) wrap in
    try/catch; the test entry point lets failures surface so the
    test reports a clean error. -/
private def walkProofIntoGoal (goal : MVarId) (proof : Alethe.Proof)
    : TacticM Unit := do
  let goalType ← goal.getType
  let isRefutation := match proof.steps.getLast? with
    | some last => last.clause.isEmpty
    | none => false
  if isRefutation && !goalType.isConstOf ``False then
    match ← goal.falseOrByContra with
    | none => pure ()
    | some falseGoal =>
      falseGoal.withContext do
        let ctx ← Alethe.mkContext
        let proofTerm ← Alethe.walkProof ctx proof
        falseGoal.assign proofTerm
  else
    goal.withContext do
      let ctx ← Alethe.mkContext
      let proofTerm ← Alethe.walkProof ctx proof
      let termType ← Meta.inferType proofTerm
      unless ← Meta.isDefEq termType goalType do
        throwError "alethe walker: walker produced a proof of \
          {termType}, but the goal is {goalType}"
      goal.assign proofTerm

/-- Alethe walker: try to close a goal by walking the cert's
    alethe-2024 trace into a kernel proof term. The "cert IS the
    proof" play — the cvc5 refutation trace is elaborated
    step-by-step rather than the goal being re-proven by `omega`.

    Returns `true` iff the walker fully closed the goal; `false`
    on any failure (no trace data, parse failure, unsupported
    rule, walked-term type mismatch). A `false` return leaves
    the goal untouched so the caller falls through to `omega` —
    audit H1 preserved: walker failure is a tactic failure, not
    an admitted theorem. The walker builds the proof term purely
    (`mkAppM`, no mvar assignment) until the final assignment,
    so a mid-walk failure can't leave a partial assignment. -/
private def tryAletheWalker (cert : Json) : TacticM Bool := do
  match certTraceData? cert with
  | none => return false
  | some traceData =>
    match Alethe.runParseAletheProof traceData with
    | .error _ => return false
    | .ok proof =>
      -- `tryCatchRuntimeEx`: a failing walk may blow the recursion
      -- budget (runtime exception, not caught by plain try/catch)
      -- before failing cleanly; the fallback contract must hold
      -- either way.
      tryCatchRuntimeEx
        (do walkProofIntoGoal (← getMainGoal) proof; return true)
        (fun _ => return false)

/-- R3-M1: walk an Alethe refutation trace into a kernel proof of a
    ℕ goal — the cast layer in front of `walkProof`. The trace's
    atoms and assumes live at ℤ (the reified image), so:

    1. `falseOrByContra` normalizes the ℕ goal to `False`, exposing
       the ℕ counterexample facts;
    2. every ℕ-shaped Prop local (user hypotheses AND the byContra
       hypothesis) is cast to its ℤ image via the `natCast*` shims
       and asserted; the IR's `_pb_nonneg_*` facts are proved by
       `natCastNonneg` on each atom;
    3. the walker runs with its atom map overridden so every ℕ var
       and atomized subterm resolves to `Int.ofNat <term>` — the
       trace's assumes then match the asserted ℤ facts by defeq
       (kernel defeq folds the cast through `+`/`*`/literals).

    Throws on failure (caller catches for the fallback paths). -/
private def walkNatProofIntoGoal (goal : MVarId) (proof : Alethe.Proof)
    (ir : IR) (tableAtoms : Array (String × Expr)) : TacticM Unit := do
  let isRefutation := match proof.steps.getLast? with
    | some last => last.clause.isEmpty
    | none => false
  unless isRefutation do
    throwError "alethe walker (ℕ): only refutation traces are lifted"
  let falseGoal ← do
    if (← goal.getType).isConstOf ``False then pure goal
    else match ← goal.falseOrByContra with
      | some g => pure g
      | none => pure goal
  falseGoal.withContext do
    let atoms ← natAtomExprs ir tableAtoms
    -- Cast layer: ℤ images of every castable ℕ-shaped local, plus
    -- the nonneg facts. Opportunistic — the walker matches what the
    -- trace needs; an assume with no matching fact fails the walk
    -- honestly.
    let mut facts : Array Lean.Meta.Hypothesis := #[]
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      if ← Lean.Meta.isProp decl.type then
        if let some proofZ ← castNatHyp? decl.toExpr decl.type then
          facts := facts.push {
            userName := Name.mkSimple s!"_pb_z_{decl.userName.toString}",
            type := ← Lean.Meta.inferType proofZ,
            value := proofZ }
    for (id, e) in atoms do
      let proofZ ← Lean.Meta.mkAppM ``ProofBroker.TermMode.natCastNonneg #[e]
      facts := facts.push {
        userName := Name.mkSimple s!"_pb_z_nonneg_{id}",
        type := ← Lean.Meta.inferType proofZ,
        value := proofZ }
    let (_, walkGoal) ← falseGoal.assertHypotheses facts
    walkGoal.withContext do
      let ctx ← Alethe.mkContext
      -- Atom override in `Nat.cast` form — the head omega's frontend
      -- recognizes (`Int.ofNat` is an opaque atom to it), so the
      -- walker's la_generic leaf closure connects the cast facts.
      -- Defeq-equal to the `Int.ofNat` constructor form either way.
      let mut vars := ctx.vars
      for (name, e) in atoms do
        vars := vars.insert (Name.mkSimple name)
          (← Lean.Meta.mkAppOptM ``Nat.cast
             #[some (mkConst ``Int), none, some e])
      let proofTerm ← Alethe.walkProof { vars } proof
      walkGoal.assign proofTerm

/-- ℕ variant of `tryAletheWalker`: same gate/fallback contract
    (`false` leaves the goal untouched), cast layer + atom override
    per `walkNatProofIntoGoal`. -/
private def tryAletheWalkerNat (cert : Json) (ir : IR)
    (tableAtoms : Array (String × Expr)) : TacticM Bool := do
  match certTraceData? cert with
  | none => return false
  | some traceData =>
    match Alethe.runParseAletheProof traceData with
    | .error _ => return false
    | .ok proof =>
      -- Runtime-exception-proof for the same reason as
      -- `tryAletheWalker`.
      tryCatchRuntimeEx
        (do walkNatProofIntoGoal (← getMainGoal) proof ir tableAtoms
            return true)
        (fun _ => return false)

/-- Axioms the home kernel already tolerates everywhere else a
    `proof_broker` closer runs (the classical footprint `omega` /
    `decide` / `aesop` pull in). The LLM-replay gate accepts a
    replayed proof term iff its transitive axiom set is a subset of
    this — never widening the trust base. Deliberately EXCLUDES
    `sorryAx` (`sorry`/`admit`) and `Lean.ofReduceBool`/
    `Lean.ofReduceNat` (`native_decide`, compiler trust, not
    kernel-checked). -/
private def llmReplayAxiomAllowlist : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Replay an LLM-suggested Lean tactic script — the Tier-3
    `lean-tactic-script` cert payload `Adapter_llm` mints — through
    the home kernel.

    The cert is an UNTRUSTED oracle: the OCaml verifier returns
    `tier3ReplayDeferred` and never soundness-checks it. Soundness
    is entirely home-side and rests on two kernel-level facts
    (audit H1):

    1. The script is elaborated by Lean itself (`exact (by …)`
       against the goal type). A script that does not actually
       prove the goal raises a tactic error and the goal is left
       OPEN — a replay failure is a tactic failure, never an
       admitted theorem.
    2. The replayed proof term's transitive axiom footprint is
       collected and must be a subset of `llmReplayAxiomAllowlist`.
       A hallucinated `sorry`/`admit` (→ `sorryAx`), `native_decide`
       (→ `Lean.ofReduceBool`), or any bespoke axiom is REJECTED
       here — the LLM cert never enters the trust footprint.

    So the LLM can only ever get a goal closed by a proof the home
    kernel independently accepts under the very same axioms every
    other closer already uses; it cannot widen what `proof_broker`
    trusts. -/
private def replayLlmScriptOrFail (goal : MVarId)
    (cert : Json) : TacticM Unit := do
  let raw ← match certTraceData? cert with
    | some s => pure s
    | none => throwError "proof_broker: LLM `lean-tactic-script` cert \
        carries no string `payload.trace_data`; nothing to replay."
  -- LLMs frequently echo a leading `by` / `:= by` despite the
  -- prompt asking for the bare body; strip one so the script
  -- parses as the body of the `by` we wrap it in. Anything left
  -- that doesn't parse is a tactic failure below (goal stays open).
  let trimS := fun (s : String) => s.trimAscii.toString
  let body :=
    let t := trimS raw
    let t := if t.startsWith ":=" then trimS (t.drop 2).toString else t
    if t.startsWith "by" then trimS (t.drop 2).toString else t
  if body.isEmpty then
    throwError "proof_broker: the LLM returned an empty tactic script. \
      The goal is left OPEN (audit H1)."
  -- Wrap as a `by` term, indented so the tactic block sits to the
  -- right of `by` for the layout-sensitive parser.
  let src :=
    "by\n" ++ String.intercalate "\n"
      ((body.splitOn "\n").map (fun l => "  " ++ l))
  let stx ← match Lean.Parser.runParserCategory (← getEnv) `term src with
    | .ok s => pure s
    | .error e => throwError "proof_broker: the LLM tactic script does not \
        parse as a Lean `by` block ({e}). The goal is left OPEN — a parse \
        failure is a tactic failure, never an admitted theorem.\n\
        --- script ---\n{raw}"
  -- Replay: elaborate `(by <script>)` against the goal type and
  -- close the goal with it. `exact` failing (script doesn't prove
  -- the goal / errors) propagates as a tactic error — goal OPEN.
  let tstx : TSyntax `term := ⟨stx⟩
  try
    evalTactic (← `(tactic| exact $tstx))
  catch ex =>
    throwError "proof_broker: the LLM tactic script failed to replay \
      through the kernel: {ex.toMessageData}. The goal is left OPEN — a \
      failed replay is a tactic failure, never an admitted theorem \
      (audit H1)."
  unless (← goal.isAssigned) do
    throwError "proof_broker: the LLM tactic script ran without error but \
      did not close the goal. The goal is left OPEN, never admitted \
      (audit H1)."
  -- Audit H1: gate the *replayed* term's transitive axiom footprint.
  let pf ← instantiateMVars (mkMVar goal)
  let mut bad : NameSet := {}
  for c in pf.getUsedConstantsAsSet.toList do
    for a in (← collectAxioms c) do
      unless llmReplayAxiomAllowlist.contains a do bad := bad.insert a
  unless bad.toList.isEmpty do
    -- Undo the assignment narrative-wise: the cert is rejected, the
    -- goal is treated as never closed (audit H1). `throwError`
    -- aborts the tactic so the metavariable assignment is discarded
    -- with the tactic state.
    throwError "proof_broker: the LLM tactic script closed the goal, but \
      its proof term depends on axiom(s) outside the allowed classical \
      footprint: {bad.toList}. REJECTED — the goal is treated as OPEN, \
      never admitted via an LLM-introduced axiom (audit H1). (`sorry`/\
      `admit` ⇒ `sorryAx`; `native_decide` ⇒ `Lean.ofReduceBool`.)"

/- ============================================================
   LLM-assisted Tier-3 reconstruction (roadmap §Phase 3 #4)
   ============================================================

   When the broker mints a Tier-3 cert whose `trace_format` the
   home system has no symbolic replayer for (e.g., a future ATP
   that emits a dialect Lean's `omega`/`linarith`/`aesop` chain
   can't act on), the closer asks the configured LLM to translate
   the trace into a candidate Lean tactic script, then routes
   that script through the {e same} audit-H1 gate
   `replayLlmScriptOrFail` uses for primary LLM certs — kernel
   replay plus a transitive-axiom subset check against the
   classical allowlist. The LLM never widens the trust base:
   a hallucinated `sorry`/`native_decide`/bespoke-axiom
   translation is a tactic failure, never an admitted theorem.

   The fallback is silent when the endpoint is unconfigured (the
   SDK returns a structured error; the caller re-raises the
   primary failure) — i.e., no LLM endpoint behaves exactly as if
   this branch were not wired in. -/

/-- Replay a candidate script (from a reconstruction translator)
    through `replayLlmScriptOrFail`, wrapping it in a synthetic
    `lean-tactic-script` cert payload so the same audit-H1 gate
    fires. Returns `true` on a successful, axiom-gated closure;
    `false` if the gate rejected the script. Never raises — a
    rejection is reported as `false` so the caller can re-raise
    its own primary error for the user. -/
private def replayReconstructedScript (goal : MVarId)
    (traceFormat : String) (script : String) : TacticM Bool := do
  let candidate : Json := Json.mkObj [
    ("payload", Json.mkObj [
      ("trace_format", Json.str "lean-tactic-script"),
      ("trace_data", Json.str script)])]
  try
    replayLlmScriptOrFail goal candidate
    Lean.logInfo m!"proof_broker: closed via LLM Tier-3 reconstruction \
      ({traceFormat} trace → Lean tactic script, kernel-checked, audit H1)."
    pure true
  catch _ =>
    pure false

/-- Try LLM-assisted reconstruction on `cert?`. Returns `true`
    iff a candidate script came back from the SDK AND the
    audit-H1 gate accepted the replayed proof term.

    Gate (no-op unless all hold):
    * a cert is in hand,
    * tier is 3,
    * `payload.trace_format` exists and is not already
      `lean-tactic-script` (which the primary LLM-replay branch
      at the top of `closeOrFail` handles),
    * the SDK's `llm_translate_trace` returns a non-empty script
      (so this is silent when no endpoint is configured). -/
private def tryLlmReconstruct? (goal : MVarId) (ir : IR)
    (cert? : Option Json) : TacticM Bool := do
  match cert? with
  | none => pure false
  | some cert =>
    let tier := (cert.getObjValAs? Int "tier").toOption.getD 0
    let traceFmt := certTraceFormat cert
    if tier != 3 || traceFmt == "" || traceFmt == "lean-tactic-script" then
      pure false
    else
      match runLlmTranslateTrace ir cert with
      | .error _ => pure false
      | .ok script => replayReconstructedScript goal traceFmt script

/-- Primary fragment-keyed closer chain. Dispatch on (cert's
    fragment × verify reason); on any failure (verifier
    rejection, fragment closer can't discharge, no closer for
    this fragment) `throwError`s rather than leaving the goal
    closed by an unjustified axiom. Wrapped by `closeOrFail`,
    which catches a primary failure and hands it to the
    LLM-assisted Tier-3 reconstruction fallback (audit-H1-gated)
    before re-raising — see `tryLlmReconstruct?`.

    Closure dispatch is keyed on the cert's fragment first, then
    its verify reason:

    * Any cert (Tier 1 / 2 / 3) over LIA: `omega`. Sound for LIA
      and axiom-free; cert verification gates the call so we only
      invoke `omega` on goals the broker has already certified
      provable. This covers the common case where `preferHigherTier`
      floats cvc5's Tier 3 alethe-2024 path to the top — those
      `verifiedTier3` certs over LIA close axiom-free even though
      we don't have a Lean-side Alethe walker yet.
    * Anything else `verif.ok = true` (LRA Tier 1 Farkas via the
      registered `linarith` closer, BV via `decide`, UF via
      `subst_eqs`/`simp_all`): an axiom-free Lean tactic. If none
      can discharge the goal the tactic `throwError`s — the goal
      is left open, never closed by an axiom (audit H1). Tier 3
      reification via a Lean-side Alethe walker is the principled
      finish for the not-yet-covered shapes; LIA Tier 3 doesn't
      need it — omega already nails that axiom-free.

    `goal` is unused here — every primary closer operates on the
    tactic state (`omega`/`decide`/…) or `throwError`s. It's
    kept in the signature because `closeOrFail`'s shared signature
    threads it through; the LLM-replay/reconstruction paths in
    the wrapper do use it. -/
private def closeOrFailPrimary (_goal : MVarId) (path : ExtractionPath)
    : TacticM Unit := do
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
      -- on any axiom regardless of the tier the cert came from.
      --
      -- Alethe walker: for alethe-2024 traces, try walking the
      -- trace into a kernel proof term first ("cert IS the
      -- proof"). The walker calls `MVarId.falseOrByContra`
      -- internally to handle non-`False` user goals — the Alethe
      -- proof always concludes `False`, so any goal is normalized
      -- to that refutation shape with the negated goal exposed
      -- as a hypothesis the trace's `assume`s match against. On
      -- any walker failure (parse error, unsupported rule, walk
      -- exception, type mismatch) we fall through to omega —
      -- audit H1 preserved. The walker's rule inventory is the
      -- `PARITY:walker-rules` dispatch block in
      -- `ProofBroker.Alethe.elabStep` (kept in lockstep with the
      -- Rocq walker by `tools/check_walker_parity.py`; rule counts:
      -- the generated status table in README.md,
      -- `python3 tools/status_table.py`); omega catches anything
      -- outside that scope.
      let walkerHandled ← do
        -- Identity-trace guard (R2): the walker elaborates the
        -- cert's trace against the ORIGINAL goal, so it only runs
        -- when the dispatch pipeline provably didn't rewrite it.
        -- R3-M1: a ℕ extraction routes through the cast-layer
        -- variant — the trace addresses the reified ℤ image, and
        -- the lift rebuilds the ℕ proof from it.
        if certTraceFormat cert == "alethe-2024" && identityTraceOk path then
          if natModeOf path.ir then
            tryAletheWalkerNat cert path.ir path.natAtoms
          else tryAletheWalker cert
        else
          pure false
      unless walkerHandled do
        evalTactic (← `(tactic| omega))
    else if fragment == "BV" then
      -- Cert-gated decide: BitVec has DecidableEq + the operator
      -- typeclass instances are decidable, so closed BV goals
      -- reduce to a decidable proposition that `decide` discharges.
      -- The cert is Tier 0 oracle today (no native BV witness
      -- extraction); envelope verification + cvc5/z3 unsat is
      -- the trust gate, `decide` is the actual proof emitter.
      -- `decide` is itself axiom-free, so closure here doesn't
      -- depend on any axiom. Big-width / quantifier-heavy BV goals
      -- where `decide` doesn't terminate in elaboration time are
      -- reported as a tactic failure (no axiom fallback — audit H1).
      try evalTactic (← `(tactic| decide))
      catch _ =>
        throwError "proof_broker: the broker certified this BV goal but \
          Lean's `decide` could not discharge it (typically too wide or \
          quantifier-heavy for elaboration-time evaluation). There is no \
          Lean-side BV witness reconstruction yet, so the goal is left \
          OPEN rather than closed by an unjustified axiom — this is a \
          tactic failure, not an admitted theorem."
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
      -- Walker-first (R1.3): a UF cert carrying an alethe-2024
      -- trace goes through the Alethe walker ("cert IS the
      -- proof") before the re-proving chain; any walker failure
      -- falls through to it — audit H1 preserved.
      let walkerHandled ← do
        -- Identity-trace guard (R2): the walker elaborates the
        -- cert's trace against the ORIGINAL goal, so it only runs
        -- when the dispatch pipeline provably didn't rewrite it.
        if certTraceFormat cert == "alethe-2024" && identityTraceOk path then
          tryAletheWalker cert
        else
          pure false
      unless walkerHandled do
        try evalTactic (← `(tactic| subst_eqs; rfl))
        catch _ =>
          try evalTactic (← `(tactic| simp_all))
          catch _ =>
            throwError "proof_broker: the broker certified this UF goal \
              but neither the Alethe walker nor the Lean closer chain \
              (`subst_eqs; rfl`, then `simp_all`) could discharge it. \
              The goal is left OPEN rather than closed by an \
              unjustified axiom — this is a tactic failure, not an \
              admitted theorem."
    else if fragment == "UFLIA" then
      -- Quantified UF+LIA (R1.3). `Smtlib.fragment_of_logic` maps
      -- the quantifier-free UF logics to "UF" but passes a
      -- quantified UFLIA logic through verbatim — and this arm
      -- previously did not exist, so such goals had no closer at
      -- all. Walker-first like LIA/UF, then a `simp_all` /
      -- `omega` fallback chain (both axiom-free), then an honest
      -- tactic failure.
      let walkerHandled ← do
        -- Identity-trace guard (R2): the walker elaborates the
        -- cert's trace against the ORIGINAL goal, so it only runs
        -- when the dispatch pipeline provably didn't rewrite it.
        if certTraceFormat cert == "alethe-2024" && identityTraceOk path then
          tryAletheWalker cert
        else
          pure false
      unless walkerHandled do
        try evalTactic (← `(tactic| simp_all))
        catch _ =>
          try evalTactic (← `(tactic| omega))
          catch _ =>
            throwError "proof_broker: the broker certified this UFLIA \
              goal but neither the Alethe walker nor the fallback \
              chain (`simp_all`, then `omega`) could discharge it. The \
              goal is left OPEN rather than closed by an unjustified \
              axiom — this is a tactic failure, not an admitted \
              theorem."
    else
      -- Non-LIA / non-BV: dispatch through the registered
      -- ReifierExt's closer if present (e.g. ProofBrokerMathlib
      -- registers a linarith closer for "LRA"); otherwise fall
      -- back to the trust axiom. The cert verification gates the
      -- call either way, so the closer can trust solvability.
      if fragment == "LRA" then
        match ← reifierExt.get with
        | some ext => ext.lraCloser
        | none =>
          throwError "proof_broker: the broker certified this LRA goal \
            but no LRA closer is registered. `import ProofBrokerMathlib` \
            to enable the linarith closer. The goal is left OPEN rather \
            than closed by an unjustified axiom."
      else if fragment == "HOL" || fragment == "FOL" then
        -- Vampire path: a Tier-3 TSTP (`verifiedTier3Provenance`)
        -- or Tier-0 oracle cert over a higher-order / FOL goal.
        -- The cert gates the call; the registered extension's
        -- `holCloser` (ProofBrokerMathlib → `aesop`) emits the
        -- actual kernel proof term, so closure is axiom-free and
        -- the cert never enters the trust footprint (audit H1).
        -- No extension ⇒ tactic failure, never an admitted axiom.
        match ← reifierExt.get with
        | some ext => ext.holCloser
        | none =>
          throwError "proof_broker: the broker certified this \
            {fragment} goal but no higher-order closer is registered. \
            `import ProofBrokerMathlib` to enable the aesop closer. \
            The goal is left OPEN rather than closed by an unjustified \
            axiom."
      else
        throwError "proof_broker: the broker certified this goal for \
          fragment '{fragment}', but there is no sound Lean-side closer \
          for that fragment. The goal is left OPEN rather than closed by \
          an unjustified axiom — implement a fragment closer (or a \
          Tier-3 Alethe term reconstruction) to discharge it."
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

/-- Close the goal from an extracted broker path, with the full
    Phase-3 audit-H1 closer stack:

    1. LLM-as-backend primary (#3) — a `lean-tactic-script`
       Tier-3 cert with reason `tier3ReplayDeferred` is the
       untrusted oracle the OCaml verifier deliberately leaves
       soundness-unchecked. Routed straight to
       `replayLlmScriptOrFail` (kernel replay + axiom-footprint
       gate); never enters the fragment chain.
    2. Primary fragment-keyed closers (`closeOrFailPrimary`) —
       `omega`/`decide`/`subst_eqs`/`linarith`/`aesop` per the
       cert's fragment.
    3. LLM-assisted Tier-3 reconstruction fallback (#4) — if (2)
       throws and a Tier-3 trace cert (in any format other than
       `lean-tactic-script`) is in hand, ask the SDK to translate
       the trace into a candidate Lean tactic script via
       `runLlmTranslateTrace`, then route the script through the
       SAME audit-H1 gate (`replayReconstructedScript` →
       `replayLlmScriptOrFail`). On success the goal closes and
       a `logInfo` records the reconstruction step. On any
       rejection (no endpoint, parse failure, sorry/native_decide
       in the script, …) the primary failure is re-raised so the
       user sees the original reason, not a misleading
       "LLM didn't help" message.

    Soundness across all three: no closer ever assigns the goal
    metavariable directly with a trusted axiom; every kernel
    proof either comes from an axiom-free decision procedure or
    from `replayLlmScriptOrFail`'s subset check against the
    classical allowlist. The LLM never widens the trust base.

    The verbose form (`proof_broker?`) calls `logInfo` with
    `renderPath` first; the bare form just throws so unsuccessful
    invocations are silent. `_goalType` is retained for the
    shared closer signature but unused; `goal` is used only by
    the LLM-replay paths. -/
private def closeOrFail (goal : MVarId) (_goalType : Expr)
    (path : ExtractionPath) : TacticM Unit := do
  -- (1) LLM-as-backend primary path — its untrusted-oracle cert
  -- bypasses the fragment chain entirely.
  if let some cert := path.cert then
    if certTraceFormat cert == "lean-tactic-script"
        && path.verifyEnvelopeOk == some true
        && (match path.verifyReason with
            | some (.tier3ReplayDeferred _) => true
            | _ => false) then
      replayLlmScriptOrFail goal cert
      return
  -- (2) Primary closer chain; on failure, (3) try LLM-assisted
  -- reconstruction before surfacing the error.
  try
    closeOrFailPrimary goal path
  catch primary =>
    if (← tryLlmReconstruct? goal path.ir path.cert) then
      return
    else
      throw primary

/- ============================================================
   Term-mode closer (Tier 1 Farkas reconstruction)
   ============================================================ -/

/-- Parse a coefficient string into `(numerator, denominator)`.
    Accepts plain integers ("5", "-3"), rationals ("1/2", "-3/4"),
    and canonicalizes negative denominators by flipping the
    numerator's sign. Returns `none` on parse failure or zero
    denominator. Decimal forms (eg "0.5") are not handled here —
    SDK-side, solvers that emit Real-typed coefficients almost
    always serialize as fractions, and the Linear_arith parser
    used SDK-side is authoritative for any decimal handling. -/
private def parseRatString (s : String) : Option (Int × Int) :=
  match s.splitOn "/" with
  | [n] =>
    match n.toInt? with
    | some i => some (i, 1)
    | none => none
  | [n, d] =>
    match n.toInt?, d.toInt? with
    | some i, some j =>
      if j == 0 then none
      else if j < 0 then some (-i, -j)
      else some (i, j)
    | _, _ => none
  | _ => none

/-- Clear denominators across a list of `(label, num, den)` entries.
    Computes the LCM of all denominators (via `Nat.lcm` over
    `natAbs`, safe because every entry's denominator is positive)
    and scales each numerator by `LCM / den`. Mirror of the SDK's
    `Linear_arith.clear_denominators_list`. Soundness: multiplying
    every Farkas coefficient by a single positive integer preserves
    each premise's compiled non-positivity, scales the residual sum
    by the same factor (sign preserved), and leaves premise
    strictness unchanged. The closer's `omega`-discharged residual
    sees the integer-scaled linear combination. -/
private def clearDenominators
    (entries : List (String × Int × Int)) : List (String × Int) :=
  let lcdNat : Nat :=
    entries.foldl (fun acc (_, _, d) => Nat.lcm acc d.natAbs) 1
  let lcd : Int := lcdNat
  entries.map fun (name, n, d) => (name, n * (lcd / d))

/-- Read coefficient strings out of `cert.payload.witness_data.coefficients`.
    Returns `(name, coef-as-Int)` per entry — solver-emitted rational
    coefficients are normalized to integers via LCM-of-denominators
    scaling here. Errors if the cert isn't a Tier 1 Farkas envelope
    or a coefficient string fails rational parsing. -/
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
  let rats ← arr.toList.mapM fun entry => do
    let name := (entry.getObjValAs? String "hypothesis").toOption.getD ""
    let coefStr := (entry.getObjValAs? String "coefficient").toOption.getD ""
    if name == "" then throwError "proof_broker_term: witness entry missing hypothesis"
    let (n, d) ← match parseRatString coefStr with
      | some pair => pure pair
      | none => throwError
          "proof_broker_term: malformed coefficient '{coefStr}' \
           (expected integer or n/d)"
    pure (name, n, d)
  pure (clearDenominators rats)

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

/-- The four hypothesis-shape kinds the term-mode closer normalizes
    to the canonical `a' ≤ 0` form:
    * `.le` — `(h : a ≤ b)` → `a - b ≤ 0`
    * `.ge` — `(h : a ≥ b)` → `b - a ≤ 0`
    * `.lt` — `(h : a < b)` → `(a + 1) - b ≤ 0` (LIA +1 trick)
    * `.gt` — `(h : a > b)` → `(b + 1) - a ≤ 0` (LIA +1 trick)

    Lean's `GE.ge` / `GT.gt` are `def`-defined rather than typeclass
    aliases, so they don't auto-reduce to swapped `≤` / `<`; the
    matcher matches them explicitly. -/
private inductive HypKind
  | le | ge | lt | gt
deriving Repr

/-- Recognize an `Int` comparison shape in a hypothesis type. Returns
    `(kind, lhs, rhs)` where the kind picks the normalization helper
    to apply (see `HypKind` for the form). All four shapes are
    matched explicitly — `getAppFnArgs` doesn't reduce
    `GE.ge` / `GT.gt`. -/
private def matchIntBound? (ty : Expr) : Option (HypKind × Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``LE.le, #[α, _, a, b]) =>
    if α.isConstOf ``Int then some (.le, a, b) else none
  | (``GE.ge, #[α, _, a, b]) =>
    if α.isConstOf ``Int then some (.ge, a, b) else none
  | (``LT.lt, #[α, _, a, b]) =>
    if α.isConstOf ``Int then some (.lt, a, b) else none
  | (``GT.gt, #[α, _, a, b]) =>
    if α.isConstOf ``Int then some (.gt, a, b) else none
  | _ => none

/-- Detect an Int Eq hypothesis: `h : a = b` with `a b : Int`. Used
    by the closer to permit signed coefficients on Eq while keeping
    the positive-coefficient invariant on inequalities. -/
private def matchIntEqHyp? (ty : Expr) : Option (Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``Eq, #[α, a, b]) =>
    if α.isConstOf ``Int then some (a, b) else none
  | _ => none

/-- Detect an Int Not-hypothesis: `h : ¬(a <op> b)` for
    `<op> ∈ {≤, ≥, <, >}`. Returns the inner kind + operands. The
    closer applies the matching `notLeToLe0` / `notGeToLe0` /
    `notLtToLe0` / `notGtToLe0` helper to normalize. -/
private def matchIntNotBound? (ty : Expr) : Option (HypKind × Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``Not, #[inner]) =>
    match inner.getAppFnArgs with
    | (``LE.le, #[α, _, a, b]) =>
      if α.isConstOf ``Int then some (.le, a, b) else none
    | (``GE.ge, #[α, _, a, b]) =>
      if α.isConstOf ``Int then some (.ge, a, b) else none
    | (``LT.lt, #[α, _, a, b]) =>
      if α.isConstOf ``Int then some (.lt, a, b) else none
    | (``GT.gt, #[α, _, a, b]) =>
      if α.isConstOf ``Int then some (.gt, a, b) else none
    | _ => none
  | _ => none

/-- Given a hypothesis `(h : <shape> : Int)` and a flip flag, build
    an `Expr` of type `a' ≤ 0` for the kind-specific normalized LHS
    `a'`. The flip flag is meaningful only on Eq hypotheses — for
    `h : a = b`, `flipped=false` gives `a - b ≤ 0` via `eqToLe0`
    and `flipped=true` gives `b - a ≤ 0` via `eqToLe0Flipped`. For
    inequality shapes, the flip flag is unused (callers should
    never pass `true`; the closer enforces this upstream). -/
private def normalizeHypothesis (hypFV : Expr) (hypTy : Expr)
    (flipped : Bool) : MetaM (Expr × Expr) := do
  match matchIntEqHyp? hypTy with
  | some (a, b) =>
    if flipped then
      let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
      let proof ← Lean.Meta.mkAppM ``ProofBroker.TermMode.eqToLe0Flipped #[hypFV]
      return (normExpr, proof)
    else
      let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
      let proof ← Lean.Meta.mkAppM ``ProofBroker.TermMode.eqToLe0 #[hypFV]
      return (normExpr, proof)
  | none =>
  match matchIntNotBound? hypTy with
  | some (.le, a, b) =>
    -- ¬(a ≤ b) → b < a → (b + 1) - a ≤ 0 via LIA +1 trick.
    let one := Lean.toExpr (1 : Int)
    let bPlus1 ← Lean.Meta.mkAppM ``HAdd.hAdd #[b, one]
    let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[bPlus1, a]
    let proof ← Lean.Meta.mkAppM ``ProofBroker.TermMode.notLeToLe0 #[hypFV]
    return (normExpr, proof)
  | some (.ge, a, b) =>
    -- ¬(a ≥ b) → a < b → (a + 1) - b ≤ 0.
    let one := Lean.toExpr (1 : Int)
    let aPlus1 ← Lean.Meta.mkAppM ``HAdd.hAdd #[a, one]
    let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[aPlus1, b]
    let proof ← Lean.Meta.mkAppM ``ProofBroker.TermMode.notGeToLe0 #[hypFV]
    return (normExpr, proof)
  | some (.lt, a, b) =>
    -- ¬(a < b) → b ≤ a → b - a ≤ 0 (loose, no +1).
    let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
    let proof ← Lean.Meta.mkAppM ``ProofBroker.TermMode.notLtToLe0 #[hypFV]
    return (normExpr, proof)
  | some (.gt, a, b) =>
    -- ¬(a > b) → a ≤ b → a - b ≤ 0 (loose, no +1).
    let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM ``ProofBroker.TermMode.notGtToLe0 #[hypFV]
    return (normExpr, proof)
  | none =>
  match matchIntBound? hypTy with
  | some (.le, a, b) =>
    let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM ``ProofBroker.TermMode.leToLe0 #[hypFV]
    return (normExpr, proof)
  | some (.ge, a, b) =>
    let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
    let proof ← Lean.Meta.mkAppM ``ProofBroker.TermMode.geToLe0 #[hypFV]
    return (normExpr, proof)
  | some (.lt, a, b) =>
    let one := Lean.toExpr (1 : Int)
    let aPlus1 ← Lean.Meta.mkAppM ``HAdd.hAdd #[a, one]
    let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[aPlus1, b]
    let proof ← Lean.Meta.mkAppM ``ProofBroker.TermMode.ltToLe0 #[hypFV]
    return (normExpr, proof)
  | some (.gt, a, b) =>
    let one := Lean.toExpr (1 : Int)
    let bPlus1 ← Lean.Meta.mkAppM ``HAdd.hAdd #[b, one]
    let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[bPlus1, a]
    let proof ← Lean.Meta.mkAppM ``ProofBroker.TermMode.gtToLe0 #[hypFV]
    return (normExpr, proof)
  | none =>
    throwError "proof_broker_term: hypothesis shape outside Int ≤/≥/</>/= \
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

/-- Term-mode closer, False-goal arity-N path. Folds the witness's
    coefficient list:

      1. For each `(name, c)`: normalize hypothesis to `a ≤ 0`,
         build `c * a` and a proof via
         `Int.mul_nonpos_of_nonneg_of_nonpos`.
      2. Left-associative fold sums the products, accumulating
         `s_i ≤ 0` via `Int.add_nonpos`.
      3. Apply `farkasContradictN` with the final sum + an evar
         for `0 < s` discharged by `omega` (a literal-coefficient
         polynomial-identity check, narrower than a goal-side
         omega call).

    Arity 1 degenerates to a single product; arity 2 produces the
    same shape `farkasContradict` does; arity N ≥ 3 is the new
    reach. -/
private def closeViaTermModeFalse
    (goal : MVarId) (entries : List (String × Int)) : TacticM Unit := do
  if entries.isEmpty then
    throwError "proof_broker_term: empty witness — arity ≥ 1 required"
  goal.withContext do
    -- Pre-process: drop zero-coefficient entries (they contribute
    -- nothing), and split each remaining signed coefficient into
    -- (|c|, flipped). [flipped=true] is sound only on Eq hypotheses;
    -- inequality hypotheses with c < 0 surface a clear error.
    let stepped ← entries.mapM fun (name, c) => do
      if c == 0 then return none
      let (fv, ty) ← fvarOfName name
      let isEq := (matchIntEqHyp? ty).isSome
      let flipped : Bool := decide (c < 0)
      if flipped && !isEq then
        throwError "proof_broker_term: negative coefficient {c} on \
                     non-Eq hypothesis '{name}' — SDK verifier should \
                     have rejected this cert"
      let cAbs := if flipped then -c else c
      return some (name, fv, ty, cAbs, flipped)
    let processed := stepped.filterMap id
    if processed.isEmpty then
      throwError "proof_broker_term: all coefficients are zero — \
                   need at least one nonzero entry"
    -- Normalize each entry to (cExpr, hcProof, aExpr, haProof).
    let normalized ← processed.mapM fun (_name, fv, ty, c, flipped) => do
      let (a, ha) ← normalizeHypothesis fv ty flipped
      let cExpr := intLitExpr c
      let hc ← buildNonnegProof c
      return (cExpr, hc, a, ha)
    -- Build (c_i * a_i, proof c_i * a_i ≤ 0) for each.
    let products ← normalized.mapM fun (cExpr, hc, a, ha) => do
      let prod ← Lean.Meta.mkAppM ``HMul.hMul #[cExpr, a]
      let proof ← Lean.Meta.mkAppM
                    ``Int.mul_nonpos_of_nonneg_of_nonpos #[hc, ha]
      return (prod, proof)
    -- Left-associative fold: sum + ≤ 0 proof.
    let (sum, sumProof) ← match products with
      | [] => throwError "proof_broker_term: empty fold (internal)"
      | (p0, h0) :: rest =>
        rest.foldlM (fun (accE, accH) (p, h) => do
          let newSum ← Lean.Meta.mkAppM ``HAdd.hAdd #[accE, p]
          let newProof ← Lean.Meta.mkAppM ``Int.add_nonpos #[accH, h]
          return (newSum, newProof)) (p0, h0)
    -- Build hpos evar (0 < sum), closed by omega.
    let zero := intLitExpr 0
    let hposTy ← Lean.Meta.mkAppM ``LT.lt #[zero, sum]
    let hposMV ← Lean.Meta.mkFreshExprMVar hposTy
    let term ← Lean.Meta.mkAppM
                 ``ProofBroker.TermMode.farkasContradictN
                 #[sum, sumProof, hposMV]
    closeOmegaSubgoal hposMV.mvarId!
    goal.assign term

/-- The four LIA-goal shapes the non-False term-mode handles. `≥`
    reduces to `≤` swapped and `>` to `<` swapped by instance
    reduction; the `kind` field tracks whether the neg-goal normalized
    form carries the LIA +1 trick (`≤` / `≥` do; `<` / `>` don't) so
    the closer builds the right `hpos` polynomial. -/
private inductive GoalKind
  | le   -- b ≤ c   (+1 trick)
  | lt   -- b < c   (no +1)
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

/-- Unified arity-N comparison-goal closer. Converts `b ≤ c` /
    `b < c` (and their `≥` / `>` swapped forms) to `False` by
    applying a wrapper of shape `(c <(=) b → False) → b <(=) c`,
    introducing `neg_goal` as a regular Coq hypothesis, and
    delegating to `closeViaTermModeFalse`. The arity-N strict-aware
    fold in `closeViaTermModeFalse` handles all premises uniformly —
    including `neg_goal`, whose +1-trick normalization flows through
    the existing per-universe machinery. -/
private def closeViaTermModeComparison
    (goal : MVarId) (goalType : Expr)
    (entries : List (String × Int)) : TacticM Unit := do
  let (b, c, kind) ← match matchLiaGoal? goalType with
    | some t => pure t
    | none =>
      throwError "proof_broker_term: non-False goal must have shape \
                   (_ ≤ _) / (_ < _) / (_ ≥ _) / (_ > _) over Int; \
                   got {goalType}. Equality goals need Tier 2 \
                   case-split (the negation is a disjunction)."
  let (wrapperName, negHead) := match kind with
    | .le => (``ProofBroker.TermMode.intLeViaLt, ``LT.lt)
    | .lt => (``ProofBroker.TermMode.intLtViaLe, ``LE.le)
  let bodyMV ← goal.withContext do
    let negTy ← Lean.Meta.mkAppM negHead #[c, b]
    let bodyTy ← mkArrow negTy (mkConst ``False)
    let bodyMV ← Lean.Meta.mkFreshExprMVar bodyTy
    let term ← Lean.Meta.mkAppOptM wrapperName
                 #[some b, some c, some bodyMV]
    goal.assign term
    return bodyMV
  let (_, newGoal) ← bodyMV.mvarId!.intro `neg_goal
  closeViaTermModeFalse newGoal entries

/-- Term-mode closer for LIA Farkas witnesses. Branches on whether
    the witness names `neg_goal`:
    * No `neg_goal`: goal must be `False`, all entries name real
      hypotheses; the strict-aware arity-N fold closes via
      `farkasContradictN`.
    * With `neg_goal`: goal must be a comparison shape over `Int`;
      the unified path applies the appropriate wrapper, introduces
      `neg_goal`, and recurses into the same arity-N False-fold. -/
private def closeViaTermMode (goal : MVarId) (goalType : Expr)
    (cert : Json) : TacticM Unit := do
  let entries ← parseFarkasCoefficients cert
  if entries.isEmpty then
    throwError "proof_broker_term: empty witness — arity ≥ 1 required"
  let negEntry := entries.find? (fun e => e.1 == "neg_goal")
  match negEntry with
  | none =>
    unless goalType.isConstOf ``False do
      throwError "proof_broker_term: witness lacks neg_goal but goal is \
                   not False ({goalType}); cert/goal mismatch"
    closeViaTermModeFalse goal entries
  | some _ =>
    if goalType.isConstOf ``False then
      throwError "proof_broker_term: witness names neg_goal but goal is \
                   False ({goalType}); cert/goal mismatch"
    closeViaTermModeComparison goal goalType entries

/- ============================================================
   R3-M1: term-mode closer for ℕ goals (the lift, Farkas leg)
   ============================================================ -/

/-- Match a ℕ LIA-comparison goal; the `≥`/`>` swap mirrors
    `matchLiaGoal?` (the SDK's IR already swapped, and `GE.ge`/
    `GT.gt` reduce definitionally to the swapped forms). -/
private def matchNatGoal? (goalType : Expr)
    : Option (Expr × Expr × GoalKind) :=
  match goalType.getAppFnArgs with
  | (``LE.le, #[α, _, b, c]) =>
    if α.isConstOf ``Nat then some (b, c, .le) else none
  | (``LT.lt, #[α, _, b, c]) =>
    if α.isConstOf ``Nat then some (b, c, .lt) else none
  | (``GE.ge, #[α, _, a, b]) =>
    if α.isConstOf ``Nat then some (b, a, .le) else none
  | (``GT.gt, #[α, _, a, b]) =>
    if α.isConstOf ``Nat then some (b, a, .lt) else none
  | _ => none

/-- The `_pb_z_`-prefixed name the ℕ cast layer asserts a witness
    hypothesis under (distinct from the ℕ original — the fold's
    by-name lookup must not see a shadowed pair). -/
private def natZName (n : String) : String := s!"_pb_z_{n}"

/-- Assert the ℤ image of every witness-named fact into `goal` (a
    `False` goal whose context holds the ℕ originals): IR
    `_pb_nonneg_*` hypotheses are proved by `natCastNonneg` on
    their atom; every other name must be a local ℕ-shaped
    hypothesis, cast via the `natCast*` shims. A witness name the
    layer cannot produce is an ERROR — term mode consumes the
    witness or fails, it never guesses. -/
private def assertNatWitnessFacts (goal : MVarId) (ir : IR)
    (tableAtoms : Array (String × Expr)) (names : List String)
    : TacticM MVarId := do
  goal.withContext do
  let atoms ← natAtomExprs ir tableAtoms
  let mut facts : Array Lean.Meta.Hypothesis := #[]
  for name in names.eraseDups do
    let proofZ ←
      if name.startsWith "_pb_nonneg_" then
        let key := (name.drop "_pb_nonneg_".length).toString
        let atomKey := if key.startsWith "atom_" then "_pb_" ++ key else key
        match atoms.find? (·.1 == atomKey) with
        | some (_, e) =>
          Lean.Meta.mkAppM ``ProofBroker.TermMode.natCastNonneg #[e]
        | none =>
          throwError "proof_broker_term: witness names {name} but the \
            extraction has no atom '{atomKey}'"
      else
        match (← getLCtx).findFromUserName? (Name.mkSimple name) with
        | none =>
          throwError "proof_broker_term: witness names hypothesis \
            '{name}' which is not in scope"
        | some decl =>
          match ← castNatHyp? decl.toExpr decl.type with
          | some p => pure p
          | none =>
            throwError "proof_broker_term: hypothesis '{name}' has a \
              shape the ℕ→ℤ lift cannot cast yet ({decl.type})"
    facts := facts.push {
      userName := Name.mkSimple (natZName name),
      type := ← Lean.Meta.inferType proofZ,
      value := proofZ }
  let (_, goal') ← goal.assertHypotheses facts
  return goal'

/-- Term-mode closer for a ℕ goal: the first real lift. Shape
    mirrors `closeViaTermMode`, with the ℕ wrappers in front:

    * `False` goal: cast every witness-named fact to ℤ
      (`assertNatWitnessFacts`) and run the Int Farkas fold over
      the images.
    * Comparison goal: apply `natLeViaLt` / `natLtViaLe`
      (`Decidable.byContradiction` at ℕ — axiom-free), intro the
      positive ℕ counterexample as `neg_goal`, cast it alongside
      the other witness facts, fold.

    The fold's entries are renamed to the `_pb_z_*` images; the
    proof term visibly consumes the cert's coefficients AND the
    cast shims — no tactic call ever touches the original goal. -/
private def closeNatViaTermMode (goal : MVarId) (goalType : Expr)
    (cert : Json) (ir : IR) (tableAtoms : Array (String × Expr))
    : TacticM Unit := do
  let entries ← parseFarkasCoefficients cert
  if entries.isEmpty then
    throwError "proof_broker_term: empty witness — arity ≥ 1 required"
  let zEntries := entries.map (fun (n, c) => (natZName n, c))
  let negEntry := entries.find? (fun e => e.1 == "neg_goal")
  match negEntry with
  | none =>
    unless goalType.isConstOf ``False do
      throwError "proof_broker_term: witness lacks neg_goal but goal is \
                   not False ({goalType}); cert/goal mismatch"
    let g ← assertNatWitnessFacts goal ir tableAtoms (entries.map (·.1))
    closeViaTermModeFalse g zEntries
  | some _ =>
    let (b, c, kind) ← match matchNatGoal? goalType with
      | some t => pure t
      | none =>
        throwError "proof_broker_term: non-False ℕ goal must have shape \
                     (_ ≤ _) / (_ < _) / (_ ≥ _) / (_ > _); got \
                     {goalType}. Equality goals are pre-split via \
                     Nat.le_antisymm."
    let (wrapperName, negHead) := match kind with
      | .le => (``ProofBroker.TermMode.natLeViaLt, ``LT.lt)
      | .lt => (``ProofBroker.TermMode.natLtViaLe, ``LE.le)
    let bodyMV ← goal.withContext do
      let negTy ← Lean.Meta.mkAppM negHead #[c, b]
      let bodyTy ← mkArrow negTy (mkConst ``False)
      let bodyMV ← Lean.Meta.mkFreshExprMVar bodyTy
      let term ← Lean.Meta.mkAppOptM wrapperName
                   #[some b, some c, some bodyMV]
      goal.assign term
      return bodyMV
    let (_, newGoal) ← bodyMV.mvarId!.intro `neg_goal
    let g ← assertNatWitnessFacts newGoal ir tableAtoms (entries.map (·.1))
    closeViaTermModeFalse g zEntries

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

/-- Walker-STRICT form: dispatch + verify as usual, then close the
    goal ONLY via the Alethe walker on the minted cert — NO `omega`
    fallback. The tactic fails unless a live solve mints a Tier-3
    alethe-2024 cert AND `walkProofIntoGoal` reconstructs it into a
    kernel term. Plain `proof_broker` runs the walker then falls
    through to `omega`, so a regression in the LIVE walker path (cert
    shape, trace extraction, the walk) is masked there; this guards
    it end-to-end. Test-only — production goals use `proof_broker`. -/
syntax (name := proofBrokerWalker) "proof_broker_walker" ("[" ident,* "]")? : tactic

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

/-- R3-M1: introduce every LEADING `∀ (n : ℕ)` binder of the goal
    before reification. ℕ universals have no shell translation yet
    (the bounded-∀ transform is future work), but a leading goal
    binder is just a free variable — introducing it is the standard
    sound move and the cert then addresses the introduced form.
    Goals with other binder types (notably ∀-Int, which the walker
    corpus reifies as `forall_` shells) are untouched. The result
    is installed as the main goal. -/
private partial def introLeadingNatForalls (goal : MVarId) : TacticM MVarId := do
  let ty ← goal.withContext do Lean.instantiateMVars (← goal.getType)
  match ty with
  | .forallE _ dom _ _ =>
    if dom.isConstOf ``Nat then
      let (_, goal') ← goal.intro1P
      let goal'' ← introLeadingNatForalls goal'
      replaceMainGoal [goal'']
      return goal''
    else return goal
  | _ => return goal

@[tactic proofBroker]
def evalProofBroker : Tactic := fun stx => do
  let goal ← getMainGoal
  let goal ← introLeadingNatForalls goal
  let goalType ← goal.getType
  let (adapterNames?, preferHigherTier) ← match stx with
    | `(tactic| proof_broker [$names,*]) =>
        parseAdapterList (some names.getElems)
    | `(tactic| proof_broker) =>
        parseAdapterList none
    | _ => throwError "proof_broker: malformed invocation"
  let path ← buildExtractionPath goal adapterNames? preferHigherTier
  closeOrFail goal goalType path

@[tactic proofBrokerWalker]
def evalProofBrokerWalker : Tactic := fun stx => do
  let goal ← getMainGoal
  let goal ← introLeadingNatForalls goal
  let (adapterNames?, preferHigherTier) ← match stx with
    | `(tactic| proof_broker_walker [$names,*]) =>
        parseAdapterList (some names.getElems)
    | `(tactic| proof_broker_walker) =>
        parseAdapterList none
    | _ => throwError "proof_broker_walker: malformed invocation"
  let path ← buildExtractionPath goal adapterNames? preferHigherTier
    (tierPreference := some ["3"])
  let cert ← match path.cert with
    | some c => pure c
    | none => throwError "proof_broker_walker: no adapter minted a cert; \
        attempts: {path.attempts.map (·.adapter)}"
  -- Identity-trace guard (R2): walker-strict has no fallback, so a
  -- rewritten (or traceless) dispatch is a named failure here.
  unless identityTraceOk path do
    throwError "proof_broker_walker: identity-trace guard — the dispatch \
      pipeline rewrote the goal (or returned no trace), so the cert \
      addresses the rewritten IR, not this goal. Until lifting lands (R3) \
      the walker only closes goals its cert directly addresses; use plain \
      `proof_broker`, which falls back to a decision procedure on the \
      original goal."
  -- R3-M1 specialization gate: every recorded specialization must be
  -- one this bridge inverts (ℕ→ℤ via the cast layer); otherwise the
  -- cert is refused, fail closed.
  let natMode := natModeOf path.ir
  checkCertSpecializations cert natMode
  -- Walker-strict: require the Alethe walker to close from the live
  -- cert; no `omega` fallback (that is what `proof_broker` adds).
  -- A ℕ extraction routes through the cast-layer variant; strict
  -- mode surfaces the walk's own error rather than swallowing it.
  if natMode then
    let traceData ← match certTraceData? cert with
      | some t => pure t
      | none => throwError "proof_broker_walker: cert carries no trace \
          data (tier/format not a walkable alethe-2024 trace)"
    let proof ← match Alethe.runParseAletheProof traceData with
      | .ok p => pure p
      | .error e => throwError "proof_broker_walker: trace parse \
          failed: {repr e}"
    walkNatProofIntoGoal (← getMainGoal) proof path.ir path.natAtoms
  else
    unless (← tryAletheWalker cert) do
      throwError "proof_broker_walker: the Alethe walker did not close the \
        goal from the live cert (no omega fallback). Cert tier/format may \
        not be a walkable alethe-2024 trace, or the walk failed."

@[tactic proofBrokerQ]
def evalProofBrokerQ : Tactic := fun stx => do
  let goal ← getMainGoal
  let goal ← introLeadingNatForalls goal
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

/-- Read the cert's payload strategy_hint, returning `""` if absent. -/
private def certStrategyHint (cert : Json) : String :=
  (cert.getObjVal? "payload"
    |>.bind (·.getObjValAs? String "strategy_hint")).toOption.getD ""

/-- Single-goal term-mode pipeline: build the IR + dispatch + verify
    + close the given mvar. Extracted so the equality-goal split
    can run it twice (once per direction of `Int.le_antisymm`)
    without re-parsing the adapter list.

    Dispatches on (cert payload × IR fragment):
    * Tier 2 `case_split_farkas` → registered extension's
      `tier2CaseSplitCloser` (LRA-only today; LIA Tier 2 isn't
      reachable since no adapter mints it).
    * Tier 1 Farkas, IR fragment matches extension's `irFragment`
      (eg LRA) → extension's `tier1FarkasCloser`. The extension
      handles its own goal-shape dispatch (False vs ≤ / < / ≥ / > / =)
      and any pre-normalization. Core delegates here whenever an
      extension is registered for the fragment, so Int / LIA goals
      stay on the core path.
    * Tier 1 Farkas, anything else → core `closeViaTermMode` (Int). -/
private def runTermModeOnGoal
    (goal : MVarId) (adapterNames? : Option (List String))
    (preferHigherTier : Bool) : TacticM Unit := do
  let goalType ← goal.getType
  let path ← buildExtractionPath goal adapterNames? preferHigherTier
  let cert ← match path.cert with
    | some c => pure c
    | none => throwError "proof_broker_term: no adapter minted a cert"
  -- Identity-trace guard (R2): the term-mode closers rebuild the
  -- proof from the cert's witness against the ORIGINAL goal, so a
  -- rewritten (or traceless) dispatch is a named failure — term
  -- mode has no decision-procedure fallback by design.
  unless identityTraceOk path do
    throwError "proof_broker_term: identity-trace guard — the dispatch \
      pipeline rewrote the goal (or returned no trace), so the cert's \
      witness addresses the rewritten IR, not this goal. Until lifting \
      lands (R3) term mode only consumes certs that directly address the \
      goal; use plain `proof_broker` for a decision-procedure closure."
  unless path.verifyOk == some true do
    let r := path.verifyReason.map reprStr |>.getD "<unknown>"
    throwError "proof_broker_term: cert was minted but verifier did not \
                 accept it (reason: {r}); term-mode requires a verified \
                 Tier 1 Farkas or Tier 2 case-split cert"
  -- R3-M1 specialization gate (fail closed; see
  -- `checkCertSpecializations`) + the ℕ lift: a ℕ extraction's
  -- Tier-1 Farkas witness is consumed by `closeNatViaTermMode`,
  -- which casts the witness-named facts to ℤ by term construction
  -- and runs the Int fold over the images.
  let natMode := natModeOf path.ir
  checkCertSpecializations cert natMode
  if natMode then
    if certStrategyHint cert == "case_split_farkas" then
      throwError "proof_broker_term: Tier 2 case-split over a ℕ \
        extraction is not lifted yet"
    closeNatViaTermMode goal goalType cert path.ir path.natAtoms
    return
  if certStrategyHint cert == "case_split_farkas" then
    match ← reifierExt.get with
    | some ext => ext.tier2CaseSplitCloser cert path.ir
    | none =>
      throwError "proof_broker_term: Tier 2 case_split_farkas cert \
                   minted but no extension closer registered (import \
                   `ProofBrokerMathlib` for the LRA case-split term \
                   builder)"
  else
    -- Tier 1 Farkas: delegate to extension if it claims the
    -- fragment; otherwise core's Int closer.
    let fragment := path.ir.logicClassification.firstOrderFragment
    let extOpt ← reifierExt.get
    match extOpt with
    | some ext =>
      if fragment == ext.irFragment then
        ext.tier1FarkasCloser cert path.ir
      else
        closeViaTermMode goal goalType cert
    | none =>
      closeViaTermMode goal goalType cert

/-- Match an Int equality goal `Eq Int a b`. Returns `(a, b)` if so;
    `none` otherwise. The closer pre-splits equality goals via
    `Int.le_antisymm` because `¬(a = b)` is a disjunction
    (`a < b ∨ b < a`) outside single-witness Farkas scope —
    splitting trades one cert for two, but each direction is a
    plain Int ≤ goal the existing term-mode handles axiom-free. -/
private def matchIntEqGoal? (goalType : Expr) : Option (Expr × Expr) :=
  match goalType.getAppFnArgs with
  | (``Eq, #[α, a, b]) =>
    if α.isConstOf ``Int then some (a, b) else none
  | _ => none

/-- Match an extension-claimed equality goal `Eq α a b` where the
    extension's `reifyType` recognizes `α`. Returns the type
    expression `α` if matched; `none` otherwise. Used to dispatch
    Real eq goals (and any future extension-typed eq) through the
    generic `le_antisymm` split. -/
private def matchExtensionEqGoal? (goalType : Expr) : MetaM (Option Expr) := do
  match goalType.getAppFnArgs with
  | (``Eq, #[α, _, _]) =>
    match ← reifierExt.get with
    | some ext =>
      match ← ext.reifyType α with
      | some _ => return some α
      | none => return none
    | none => return none
  | _ => return none

@[tactic proofBrokerTerm]
def evalProofBrokerTerm : Tactic := fun stx => do
  let goal ← getMainGoal
  let goal ← introLeadingNatForalls goal
  let goalType ← goal.getType
  let (adapterNames?, preferHigherTier) ← match stx with
    | `(tactic| proof_broker_term [$names,*]) =>
        parseAdapterList (some names.getElems)
    | `(tactic| proof_broker_term) =>
        parseAdapterList none
    | _ => throwError "proof_broker_term: malformed invocation"
  -- Equality-goal split. Int uses Int.le_antisymm directly (core's
  -- Int.le_antisymm is in scope here). Extension-claimed types
  -- delegate the antisym apply to the extension via its `tier1EqSplit`
  -- slot (the Mathlib `le_antisymm` isn't visible from core's
  -- Mathlib-free scope; embedding it in a syntax quotation here
  -- surfaces as `le_antisymm✝`). Each direction is a ≤ subgoal that
  -- triggers a fresh solver dispatch via `runTermModeOnGoal`.
  match matchIntEqGoal? goalType with
  | some _ =>
    evalTactic (← `(tactic| apply Int.le_antisymm))
    let subgoals ← getGoals
    for sg in subgoals do
      setGoals [sg]
      runTermModeOnGoal sg adapterNames? preferHigherTier
    setGoals []
  | none =>
  -- R3-M1: ℕ equality goals split via Nat.le_antisymm — each ≤
  -- direction re-dispatches and lifts like any ℕ comparison.
  match goalType.getAppFnArgs with
  | (``Eq, #[α, _, _]) =>
    if α.isConstOf ``Nat then
      evalTactic (← `(tactic| apply Nat.le_antisymm))
      let subgoals ← getGoals
      for sg in subgoals do
        setGoals [sg]
        runTermModeOnGoal sg adapterNames? preferHigherTier
      setGoals []
    else
      evalProofBrokerTermRest goalType goal adapterNames? preferHigherTier
  | _ =>
    evalProofBrokerTermRest goalType goal adapterNames? preferHigherTier
where
  /-- The pre-R3 tail: extension-claimed equality split, else the
      plain single-goal pipeline. -/
  evalProofBrokerTermRest (goalType : Expr) (goal : MVarId)
      (adapterNames? : Option (List String)) (preferHigherTier : Bool)
      : TacticM Unit := do
    match ← matchExtensionEqGoal? goalType with
    | some _ =>
      -- Delegate the antisym apply to the extension (Mathlib-side
      -- `le_antisymm` isn't visible from core's Mathlib-free scope).
      match ← reifierExt.get with
      | some ext =>
        ext.tier1EqSplit
        let subgoals ← getGoals
        for sg in subgoals do
          setGoals [sg]
          runTermModeOnGoal sg adapterNames? preferHigherTier
        setGoals []
      | none =>
        runTermModeOnGoal goal adapterNames? preferHigherTier
    | none =>
      runTermModeOnGoal goal adapterNames? preferHigherTier

/- ============================================================
   Test-only entry point for the LLM-replay closer
   ============================================================ -/

/-- TEST-ONLY tactic. Drives the exact `replayLlmScriptOrFail`
    path `proof_broker` takes for an LLM `lean-tactic-script`
    cert, but feeds the string literal directly as the cert's
    `payload.trace_data` instead of dispatching to a live LLM
    endpoint (which `Adapter_llm` fail-closes without
    `PROOF_BROKER_LLM_ENDPOINT`). This lets CI assert the
    audit-H1 contract — a valid script closes the goal, while a
    `sorry`/`admit`/`native_decide`/bespoke-axiom script is
    REJECTED as a tactic failure — with no network and no live
    model. Not used by the real broker pipeline. -/
syntax (name := llmReplayTest) "llm_replay_test" str : tactic

@[tactic llmReplayTest]
def evalLlmReplayTest : Tactic := fun stx => do
  match stx with
  | `(tactic| llm_replay_test $s:str) =>
    let cert : Json := Json.mkObj [
      ("payload", Json.mkObj [
        ("trace_format", Json.str "lean-tactic-script"),
        ("trace_data", Json.str s.getString)])]
    replayLlmScriptOrFail (← getMainGoal) cert
  | _ => throwError "llm_replay_test: malformed invocation"

/-- TEST-ONLY tactic for the LLM-assisted Tier-3 reconstruction
    fallback (roadmap §Phase 3 #4). The live SDK FFI
    (`llm_translate_trace`) only runs when an endpoint is
    configured — for CI we skip the translation call and feed the
    candidate script directly into the {e same} closer the
    production path invokes after a successful FFI translation
    (`replayReconstructedScript`). This pins the integration:
    a translated script flows through `replayLlmScriptOrFail`
    (kernel replay + axiom-footprint gate), the same audit-H1
    contract `llm_replay_test` exercises for primary LLM certs.
    First argument is the trace format of the (notionally
    un-replayable) source cert — surfaced in the `logInfo` audit
    line so the user can see which non-replayable format was
    rescued. -/
syntax (name := llmReconstructTest)
  "llm_reconstruct_test" str str : tactic

@[tactic llmReconstructTest]
def evalLlmReconstructTest : Tactic := fun stx => do
  match stx with
  | `(tactic| llm_reconstruct_test $fmt:str $script:str) =>
    let ok ← replayReconstructedScript (← getMainGoal)
              fmt.getString script.getString
    unless ok do
      throwError "llm_reconstruct_test: the candidate script did not \
        close the goal under the audit-H1 gate (`{fmt.getString}` \
        trace → Lean tactic script). The goal is left OPEN — \
        rejected, never admitted via an LLM-introduced axiom."
  | _ => throwError "llm_reconstruct_test: malformed invocation"

/-- TEST-ONLY tactic for the Alethe walker. Parses the string
    literal as an alethe-2024 trace via the SDK FFI, walks the
    proof into a kernel proof term, and assigns the goal. Lets CI
    exercise the walker's per-rule elaboration on hand-written
    traces without dispatching to a live cvc5 — the same
    CI-stable pattern as `llm_replay_test`.

    Routes through `walkProofIntoGoal`, identical to the
    production `tryAletheWalker` path: refutation traces use
    `falseOrByContra` to expose `¬goal` for non-`False` user
    goals; direct (single-literal) traces assign by defeq. -/
syntax (name := aletheWalkerTest) "alethe_walker_test" str : tactic

@[tactic aletheWalkerTest]
def evalAletheWalkerTest : Tactic := fun stx => do
  match stx with
  | `(tactic| alethe_walker_test $s:str) =>
    let proof ← match Alethe.runParseAletheProof s.getString with
      | .ok p => pure p
      | .error e =>
        throwError "alethe_walker_test: failed to parse trace ({repr e})"
    walkProofIntoGoal (← getMainGoal) proof
  | _ => throwError "alethe_walker_test: malformed invocation"

end ProofBroker.Tactic

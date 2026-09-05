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

/-- R3-M2: what the extension reports for a QUALIFIED polymorphic
    type variable — a local `α : Type u` whose context carries the
    ordered-ring instances the α lift family needs. The reifier
    names the variable canonically `"alpha"` in the IR (spec
    Example 1's name; also keeps non-ASCII binder names out of the
    wire format) and documents the specialization in
    `type_metadata` + `library_provenance`, exactly the M1
    discipline: the `embedding_witness:` tags name the lemmas the
    lift actually applies, each backed by a provenance entry with a
    real content hash. -/
structure TypeVarInfo where
  /-- The `type_variable`-kind `type_metadata` entry (keyed by the
      canonical name `"alpha"` by `buildIR`). -/
  metadata : Json
  /-- Provenance entries backing the entry's witness tags. -/
  provenance : List (String × Provenance)

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
  /-- R3-M2: recognize a local fvar (`α : Type u`) as a qualified
      polymorphic type variable — the extension checks that the
      instances its α lift family needs are synthesizable — and
      return the metadata + provenance the IR documents the
      specialization with. `none` = not qualified; the local is
      ignored exactly as before M2. -/
  typeVarInfo? : Expr → MetaM (Option TypeVarInfo)
  /-- R3-M2: term-mode closer for a Tier-1 Farkas cert over a
      polymorphic-α extraction. The cert's coefficients are replayed
      AT α through the extension's class-polymorphic Farkas family —
      the α→Int specialization was only for the solver, and this
      replay is what inverts it. Handles False and comparison goal
      shapes; equality goals are pre-split via `tier1EqSplit`. -/
  polyFarkasCloser : Lean.Json → IR → TacticM Unit
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

/-- Per-reification accumulator state (C4 ROUND 3 finding 1). One
    FRESH instance is created by each `buildIR` call and passed down
    the reify family explicitly, so concurrent declaration
    elaborations (Lean v4.32 elaborates a module's declarations in
    parallel by default) cannot interleave their tables. This
    replaces four module-level `IO.Ref`s whose stated invariant —
    "buildIR clears it on entry, single-goal reification is
    sequential" — parallel elaboration falsified: the demo's
    headline file failed 10/33 runs with `unsupported_symbol` when
    two declarations' reifications raced the shared tables. A
    module-level ref remains correct ONLY for set-once registration
    (`reifierExt` above: written at module initialization, read-only
    during elaboration).

    Fields:
    * `consts` — applied global constants that are not
      connectives/quantifiers (e.g. `Function.comp`); the HO/FOL
      path declares them as IR `freeVars` so the TPTP serializer
      has a monomorphic type.
    * `natAtoms` — R3-M1 nonlinear-ℕ atomization table,
      `payload_id ↦ ℕ subterm` (e.g. `Zmax * zhigh`); consumed for
      payloads + nonneg hypotheses and by the ℕ→ℤ lift's walker
      context.
    * `intAtoms` — R4.2 Int-side atomization table; like `natAtoms`
      but no nonneg hypothesis (an Int atom is just an
      uninterpreted Int constant).
    * `natDefs` — R3-M3 numeral-definition table,
      `constant name ↦ (const Expr, ℕ value)`; drives the
      definition-unfolding pass and its `Eq.mpr` inversion. -/
structure ReifyAcc where
  consts : IO.Ref (Array (String × TypeRef))
  natAtoms : IO.Ref (Array (String × Expr))
  intAtoms : IO.Ref (Array (String × Expr))
  natDefs : IO.Ref (Array (String × Expr × Nat))

/-- A fresh, empty accumulator — one per `buildIR` call. -/
def ReifyAcc.fresh : BaseIO ReifyAcc := do
  return { consts := ← IO.mkRef #[], natAtoms := ← IO.mkRef #[],
           intAtoms := ← IO.mkRef #[], natDefs := ← IO.mkRef #[] }

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
partial def reifyType? (ty : Expr) : MetaM (Option TypeRef) := do
  if ty.isConstOf ``Int then return some "Int"
  if ty.isProp then return some "Prop"
  if let some n := matchBitVecType? ty then
    return some s!"BitVec({n})"
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
      let some d ← reifyType? dom | return none
      parts := parts.push (if dom.isArrow then "(" ++ d ++ ")" else d)
      t := t.bindingBody!
    let some r ← reifyType? t | return none
    parts := parts.push r
    return some (String.intercalate "->" parts.toList)
  match ← reifierExt.get with
  | some ext =>
    match ← ext.reifyType ty with
    | some t => return some t
    | none =>
      -- A bare type constant the extension declined (e.g. `Nat`,
      -- `String`, a user inductive) is an uninterpreted base sort
      -- for the FOL/HOL (Vampire) path: the TPTP serializer
      -- declares it as a `$tType`. Not reachable on the LIA/LRA
      -- paths (Int/Real handled above / by the ext).
      if ty.isConst then return some (toString ty.constName!)
      return none
  | none =>
    if ty.isConst then return some (toString ty.constName!)
    return none

/-- Decode a type `Expr` as an IR `TypeRef`, or fail with the
    fragment error. `reifyType?` is the same walk without the
    throw — R4.2 added it so a caller can ASK whether a type is in
    the fragment (the UF/uninterpreted-constant arms of `reifyTerm`
    do, before committing to a shape whose arguments they may not be
    able to declare) instead of finding out by catching an
    exception. -/
def reifyType (ty : Expr) : MetaM TypeRef := do
  match ← reifyType? ty with
  | some t => return t
  | none =>
    match ← reifierExt.get with
    | some _ => throwError "proof_broker: unsupported type {ty}"
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

/-- R3-M1 (C3a ROUND 1 finding 5): the documented fail-fast scope —
    ℕ subtraction/division/modulo are named errors — must hold
    INSIDE atomized subterms too. Swallowing `(a - b) * c` as an
    opaque atom would be sound (the atom is uninterpreted and
    nonneg under truncated semantics as well), but it silently
    accepts exactly the goals most likely to be wrong about ℕ
    subtraction, against the stated contract. Structural scan, no
    reduction. -/
private partial def natAtomForbiddenOp? (e : Expr) : Option Name :=
  match e.getAppFnArgs with
  | (``HSub.hSub, args) | (``HDiv.hDiv, args) | (``HMod.hMod, args)
  | (``Nat.sub, args) | (``Nat.div, args) | (``Nat.mod, args)
  | (``Nat.pred, args) =>
    -- Inside a ℕ atom every subterm is ℕ-typed, so the head alone
    -- condemns it; report the innermost occurrence when nested.
    -- Both the notation heads (`HSub.hSub`, …) and the
    -- directly-spelled core names (`Nat.sub`, …, plus `Nat.pred` —
    -- truncated subtraction by one) are matched: the scan is a
    -- named-head check over the core ℕ arithmetic vocabulary, and
    -- ROUND 2 (C3a finding 6) showed the notation set alone lets a
    -- spelled `Nat.sub a b * c` through. An opaque FUNCTION
    -- application inside an atom stays honestly opaque — the atom
    -- is uninterpreted either way; this scan enforces the
    -- documented fail-fast contract for the core operations, not a
    -- semantic subtraction detector.
    (match args.foldl (fun acc a => acc <|> natAtomForbiddenOp? a) none with
     | some inner => some inner
     | none => e.getAppFn.constName?)
  | (_, args) => args.foldl (fun acc a => acc <|> natAtomForbiddenOp? a) none

/-- R4.2: the constant-folding bounds for closed ℕ arithmetic.
    `natFoldMaxExp` is R3-M1's exponent ceiling, kept verbatim;
    `natFoldMaxBits` additionally caps the *value* so a nest of
    closed powers (`(2^200)^200`) cannot build a megabyte-long
    numeral inside the reifier. 4096 bits is ~30× the widest
    literal any R4 obligation mentions (Goldilocks, 2^64) and ~16×
    the D2 2^128-scale corpus pins. -/
def natFoldMaxExp : Nat := 256
def natFoldMaxBits : Nat := 4096

/-- Read a **closed** ℕ term's value: literals, `+`, `*` and `^`
    over closed operands, folded structurally with no reduction and
    no side effects. `none` for anything with a variable, an
    application, a definition, ℕ subtraction/division/modulo, or a
    fold that leaves the bounds above.

    Why this rather than "is it a literal": the source spells
    bit-widths, so the interesting closed terms are `2^24`,
    `2^16 * 2^16` and `2^24 + 2 * 2^16`, none of which is an
    `OfNat` literal. Recognizing only literals made
    `2^16 * 2^16 < P` (verinf `Bracket.lean:62`) atomize into an
    uninterpreted `_pb_atom_k`, which no solver can then bound —
    and made `Zmax * 2^16` (line 78) a fake-opaque atom although it
    is linear. Folding is sound because the ℕ value and its ℤ image
    agree on `+`, `*`, `^`; there is no truncation anywhere in this
    fragment (`-`, `/`, `%` are refused, here as everywhere else).

    Purely structural: it never registers an atom or a definition,
    so a caller may probe with it and then decide to do something
    else with the same subterm. -/
partial def natClosedNumeral? (e : Expr) : Option Nat :=
  let bounded (n : Nat) : Option Nat :=
    if n < 2 ^ natFoldMaxBits then some n else none
  match matchNatLiteralAtNat? e with
  | some n => bounded n
  | none =>
    match e.getAppFnArgs with
    | (``HAdd.hAdd, #[α, _, _, _, a, b]) =>
      if α.isConstOf ``Nat then
        match natClosedNumeral? a, natClosedNumeral? b with
        | some x, some y => bounded (x + y)
        | _, _ => none
      else none
    | (``HMul.hMul, #[α, _, _, _, a, b]) =>
      if α.isConstOf ``Nat then
        match natClosedNumeral? a, natClosedNumeral? b with
        | some x, some y => bounded (x * y)
        | _, _ => none
      else none
    | (``HPow.hPow, #[_, _, _, _, a, b]) =>
      match natClosedNumeral? a, matchNatLiteralAtNat? b with
      | some base, some exp =>
        if exp > natFoldMaxExp then none else bounded (base ^ exp)
      | _, _ => none
    | _ => none

/-- Structurally closed ℕ arithmetic — literals under `+`, `*`, and
    `^` with a literal exponent — decided WITHOUT computing the
    value. Where this holds but `natClosedNumeral?` declined, the
    term is closed yet exceeds the folding bounds: that is a scope
    error to raise by name, never a silent atom (an atomized
    numeral generalizes the goal into one that mysteriously fails
    to close — the failure mode the named error exists to prevent).
    Deciding closedness must not compute: folding `2^5000` merely
    to diagnose it would re-create the resource hazard the bounds
    exist to avoid. -/
partial def natClosedShape (e : Expr) : Bool :=
  (matchNatLiteralAtNat? e).isSome ||
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, _, a, b]) =>
    α.isConstOf ``Nat && natClosedShape a && natClosedShape b
  | (``HMul.hMul, #[α, _, _, _, a, b]) =>
    α.isConstOf ``Nat && natClosedShape a && natClosedShape b
  | (``HPow.hPow, #[_, _, _, _, a, b]) =>
    natClosedShape a && (matchNatLiteralAtNat? b).isSome
  | _ => false

/-- The named bounds refusal for a closed-shaped term the fold
    declined (see `natClosedShape`). -/
def throwNatFoldBounds (e : Expr) : MetaM α :=
  throwError "proof_broker: closed ℕ arithmetic {e} exceeds the \
    constant-folding bounds (exponent ≤ {natFoldMaxExp}, value < \
    2^{natFoldMaxBits}) — a numeral the reifier declines to build \
    is a scope error, not an uninterpreted atom"

/-- Atomize a nonlinear ℕ subterm: reuse the existing payload id if
    this exact `Expr` was seen before (structural equality — the
    same product mentioned twice is one atom), else mint
    `_pb_atom_<k>` and record it. The shell is the atom under the
    cast, like any ℕ atom. Refuses atoms hiding sub/div/mod (see
    `natAtomForbiddenOp?`). -/
def atomizeNatTerm (acc : ReifyAcc) (e : Expr) : MetaM ShellTerm := do
  if let some op := natAtomForbiddenOp? e then
    throwError "proof_broker: ℕ {op} inside a nonlinear subterm \
      ({e}) — the ℕ→ℤ specialization refuses truncated/rounding ℕ \
      arithmetic even under atomization; restate without it"
  let atoms ← acc.natAtoms.get
  let id ← match atoms.find? (fun (_, e') => e' == e) with
    | some (id, _) => pure id
    | none =>
      let id := s!"_pb_atom_{atoms.size}"
      acc.natAtoms.modify (·.push (id, e))
      pure id
  return .app natCastSymbol [] [.opaque_ id]

/-- R3-M3: recognize a plain definition `c : Nat := <numeral>` — a
    `defnInfo` constant of type `Nat` whose elaborated body is a
    numeral. Theorems, opaques, axioms and non-numeral bodies all
    decline (fail closed into the ordinary unsupported-term error). -/
def matchNatNumeralDef? (e : Expr) : MetaM (Option (Name × Nat)) := do
  let .const c _ := e | return none
  let env ← Lean.getEnv
  let some (.defnInfo d) := env.find? c | return none
  unless d.type.isConstOf ``Nat do return none
  return (matchNatLiteralAtNat? d.value).map (c, ·)

/-- Reify a ℕ-typed `Expr` into the ℤ image of its value (casts
    pushed to atoms). Scope: variables, closed arithmetic (folded to
    one numeral by `natClosedNumeral?`), `+`, `*` (with a
    closed-numeral factor — otherwise atomized), `^` with a
    non-closed base (atomized), numeral-body
    constants (R3-M3 — emitted as an opaque leaf the def-unfold
    pass replaces, documented in `definitional_metadata`). ℕ
    subtraction / division / modulo fail fast — never cast
    naively. -/
partial def reifyNatTerm (acc : ReifyAcc) (e : Expr) : MetaM ShellTerm := do
  -- Closed ℕ arithmetic collapses to one Int numeral before any
  -- structural walk: `2^16 * 2^16` is the numeral 4294967296 in the
  -- image, not a product of two atoms (`natClosedNumeral?`).
  if let some n := natClosedNumeral? e then
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
    return .app "HAdd.hAdd" [] [← reifyNatTerm acc a, ← reifyNatTerm acc b]
  | (``HMul.hMul, #[α, _, _, _, a, b]) =>
    unless α.isConstOf ``Nat do
      throwError "proof_broker: ℕ reifier reached * at {α}"
    -- Linear iff a factor is a closed numeral (R4.2: `Zmax * 2^16`
    -- counts, `2^16` being closed but not an `OfNat` literal);
    -- otherwise the product is a nonlinear atom (the D1
    -- `Zmax * zhigh` shape). Both operands closed WITHIN BOUNDS is
    -- already gone, folded at the head of `reifyNatTerm` — but a
    -- closed product the fold declined for its SIZE (e.g.
    -- `2^300 * 2^300`) reaches here with both `natClosedNumeral?`
    -- calls returning none, and must be the named bounds refusal,
    -- not a silent atom (C4 ROUND 1 finding 5).
    if let some k := natClosedNumeral? a then
      return .app "HMul.hMul" [] [.numLit (toString k) "Int", ← reifyNatTerm acc b]
    else if let some k := natClosedNumeral? b then
      return .app "HMul.hMul" [] [← reifyNatTerm acc a, .numLit (toString k) "Int"]
    else if natClosedShape e then
      throwNatFoldBounds e
    else
      atomizeNatTerm acc e
  | (``HPow.hPow, #[_, _, _, _, a, b]) =>
    -- A closed power is already folded at the head of
    -- `reifyNatTerm`; reaching here with a closed base and a
    -- literal exponent means the fold left `natFoldMaxExp` /
    -- `natFoldMaxBits`. Say so instead of atomizing: a numeral the
    -- reifier declines to build is a scope error, not an
    -- uninterpreted atom the solver might be expected to reason
    -- about.
    (match natClosedNumeral? a, matchNatLiteralAtNat? b with
     | some base, some exp =>
       throwError "proof_broker: closed ℕ power {base}^{exp} exceeds the \
         constant-folding bounds (exponent ≤ {natFoldMaxExp}, value < \
         2^{natFoldMaxBits})"
     | _, _ =>
       -- The base can itself be closed-but-over-bounds (e.g.
       -- `(2^5000)^2`): the first conjunct above then fails without
       -- the term being any less closed. Same named refusal, never
       -- a silent atom (C4 ROUND 1 finding 5).
       if natClosedShape e then throwNatFoldBounds e
       else atomizeNatTerm acc e)
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
    -- R3-M3: a numeral-body constant becomes an opaque `App` leaf
    -- (no args) at the Int-numeral position. If the pipeline's
    -- def-unfold pass does NOT replace it (metadata dropped,
    -- directive lost), the SMT script references an undeclared
    -- symbol and dispatch fails — never a silent misreading.
    if let some (c, n) ← matchNatNumeralDef? e then
      let name := c.toString
      let defs ← acc.natDefs.get
      unless defs.any (·.1 == name) do
        acc.natDefs.modify (·.push (name, e, n))
      return .app name [] []
    -- R4.2: an APPLIED ℕ-valued function the fragment has no
    -- arithmetic reading for — `x.val` (`ZMod.val`), `f i`,
    -- `Finset.card s` — is an opaque atom, exactly like a nonlinear
    -- product: a fresh Int variable carrying `0 ≤ ↑atom` and
    -- nothing else. This is what makes the verinf D1 obligations
    -- reifiable at all; their whole content is linear arithmetic
    -- over `x.val`, `z.val` and `Zmax`.
    --
    -- Scope is deliberately narrower than "anything unrecognized":
    --   * an application only (`getAppNumArgs > 0`) with a constant
    --     or free-variable head. A bare ℕ CONSTANT still errors —
    --     R3-M3 reads a numeral-body definition as a `defined_function`
    --     the pipeline unfolds, and silently atomizing the ones it
    --     declines would hide that path failing.
    --   * `natAtomForbiddenOp?` (inside `atomizeNatTerm`) still
    --     refuses an atom with ℕ `-`/`/`/`%` anywhere inside it, so
    --     the truncation contract is unchanged.
    -- Atomization is sound whatever the function means: the atom is
    -- uninterpreted, and every ℕ atom is nonneg. What it costs is
    -- completeness — a goal that needs `x.val < P` to follow from
    -- `ZMod.val`'s own specification will simply not close.
    let fn := e.getAppFn
    if (fn.isConst || fn.isFVar) && e.getAppNumArgs > 0 then
      return ← atomizeNatTerm acc e
    throwError "proof_broker: unsupported ℕ term {e} (ℕ→ℤ scope: +, \
      * with a closed-numeral factor, ^ with a closed base and a \
      literal exponent, closed arithmetic, variables, numeral-body \
      constants; nonlinear products and applied functions atomize)"

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

/-- R4.2: the ℕ-truncation scan for an **Int**-typed atom. Unlike
    `natAtomForbiddenOp?` (where every subterm is ℕ-typed and the
    head alone condemns), an Int atom may legitimately contain Int
    `-` / `/`; only a ℕ-typed one is refused. Matches both the
    notation heads at carrier `Nat` and the directly-spelled core
    names, exactly as the ℕ scan does. -/
private partial def natOpInsideIntAtom? (e : Expr) : Option Name :=
  let hit : Option Name :=
    match e.getAppFnArgs with
    | (``HSub.hSub, args) | (``HDiv.hDiv, args) | (``HMod.hMod, args) =>
      match args[0]? with
      | some α => if α.isConstOf ``Nat then e.getAppFn.constName? else none
      | none => none
    | (``Nat.sub, _) | (``Nat.div, _) | (``Nat.mod, _) | (``Nat.pred, _) =>
      e.getAppFn.constName?
    | _ => none
  match e.getAppFnArgs.2.foldl (fun acc a => acc <|> natOpInsideIntAtom? a) none with
  | some inner => some inner
  | none => hit

/-- Atomize an Int-valued subterm the fragment has no reading for:
    a projection application (`R.x i`, `cert.TA z`), a nonlinear
    product, anything whose arguments live in a type the IR cannot
    declare (`Fin n`). Structural reuse like `atomizeNatTerm` — the
    same `Expr` is one atom — but the shell is a bare `Opaque` node
    (the SDK declares it `(declare-const _pb_iatom_k Int)`) with no
    nonneg hypothesis.

    Sound for any meaning of the atomized term: replacing a subterm
    by a fresh constant generalizes the goal, so a certificate for
    the abstraction certifies the original. The cost is
    completeness, and the atom is recorded in `goal.payloads` with
    its Lean pretty-print so the abstraction is visible in the IR
    rather than implied by it (`tools/check.py` requires every
    `Opaque` id to have a payload entry).

    ℕ subtraction/division/modulo anywhere inside still fails fast:
    atomizing them would be sound but would silently accept exactly
    the goals most likely to be wrong about ℕ truncation, against
    the R3-M1 contract (C3a ROUND 1 finding 5). -/
def atomizeIntTerm (acc : ReifyAcc) (e : Expr) : MetaM ShellTerm := do
  if let some op := natOpInsideIntAtom? e then
    throwError "proof_broker: ℕ {op} inside an atomized Int subterm \
      ({e}) — the specialization refuses truncated/rounding ℕ \
      arithmetic even under atomization; restate without it"
  let atoms ← acc.intAtoms.get
  let id ← match atoms.find? (fun (_, e') => e' == e) with
    | some (id, _) => pure id
    | none =>
      let id := s!"_pb_iatom_{atoms.size}"
      acc.intAtoms.modify (·.push (id, e))
      pure id
  return .opaque_ id

partial def reifyTerm (acc : ReifyAcc) (e : Expr) : MetaM ShellTerm := do
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
    return .implies (← reifyTerm acc e.bindingDomain!) (← reifyTerm acc e.bindingBody!)
  if e.isForall then
    return ← forallBoundedTelescope e (some 1) fun xs body => do
      let x := xs[0]!
      let decl := (← getLCtx).get! x.fvarId!
      let dom := decl.type
      if ← isProp dom then
        return .implies (← reifyTerm acc dom) (← reifyTerm acc body)
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
        return .forall_ decl.userName.toString tref (← reifyTerm acc body)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, _, a, b]) =>
      -- BV vs arithmetic disambiguation: SMT-LIB uses bvadd /
      -- bvsub / bvmul rather than the polymorphic + / - / *, so
      -- the IR carries them under different App symbols. Picked
      -- at reify time from the operand type.
      let sym := if (matchBitVecType? α).isSome then "BV.add" else "HAdd.hAdd"
      return .app sym [] [← reifyTerm acc a, ← reifyTerm acc b]
  | (``HSub.hSub, #[α, _, _, _, a, b]) =>
      -- R3-M1 attack surface: ℕ subtraction is truncated — never
      -- cast naively, never reify as ordinary subtraction.
      if α.isConstOf ``Nat then
        throwError "proof_broker: ℕ subtraction is truncated (`a - b` \
          is not the ℤ difference); the ℕ→ℤ specialization refuses it \
          — restate without ℕ subtraction"
      let sym := if (matchBitVecType? α).isSome then "BV.sub" else "HSub.hSub"
      return .app sym [] [← reifyTerm acc a, ← reifyTerm acc b]
  | (``HMul.hMul, #[α, _, _, _, a, b]) =>
      if (matchBitVecType? α).isSome then
        return .app "BV.mul" [] [← reifyTerm acc a, ← reifyTerm acc b]
      -- R4.2: a product with no numeral factor is NONLINEAR. Emitting
      -- it verbatim made cvc5 reject the whole script ("A non-linear
      -- fact was asserted to arithmetic in a linear logic"), so the
      -- goal never got a certificate; as an `Opaque` atom the linear
      -- content around it (`hrec`, `hz0`, the bound on the product)
      -- is still exactly what closes the verinf `cell_value_neutral`
      -- obligation. Decided AFTER reifying both operands, because
      -- "is a numeral" is carrier-dependent (an α or Real literal is
      -- recognized by the extension, not by `matchIntLiteral?`); the
      -- atom table is rewound first so the discarded sub-reification
      -- leaves no orphan payload entries.
      let before ← acc.intAtoms.get
      let ra ← reifyTerm acc a
      let rb ← reifyTerm acc b
      match ra, rb with
      | .numLit _ _, _ | _, .numLit _ _ =>
        return .app "HMul.hMul" [] [ra, rb]
      | _, _ =>
        acc.intAtoms.set before
        atomizeIntTerm acc e
  | (``Neg.neg, #[_, _, a]) =>
      return .app "Neg.neg" [] [← reifyTerm acc a]
  | (``LE.le, #[α, _, a, b]) =>
      -- R3-M1: ℕ comparisons reify as their ℤ image.
      if α.isConstOf ``Nat then
        return .app "LE.le" [] [← reifyNatTerm acc a, ← reifyNatTerm acc b]
      expectArithCarrier α
      -- Lean's [<=] over BitVec resolves to BitVec.ule (unsigned).
      -- Signed comparisons need [BitVec.sle] written explicitly.
      let sym := if (matchBitVecType? α).isSome then "BV.ule" else "LE.le"
      return .app sym [] [← reifyTerm acc a, ← reifyTerm acc b]
  | (``LT.lt, #[α, _, a, b]) =>
      if α.isConstOf ``Nat then
        return .app "LT.lt" [] [← reifyNatTerm acc a, ← reifyNatTerm acc b]
      expectArithCarrier α
      let sym := if (matchBitVecType? α).isSome then "BV.ult" else "LT.lt"
      return .app sym [] [← reifyTerm acc a, ← reifyTerm acc b]
  | (``GE.ge, #[α, _, a, b]) =>
      if α.isConstOf ``Nat then
        return .app "LE.le" [] [← reifyNatTerm acc b, ← reifyNatTerm acc a]
      expectArithCarrier α
      let sym := if (matchBitVecType? α).isSome then "BV.ule" else "LE.le"
      return .app sym [] [← reifyTerm acc b, ← reifyTerm acc a]
  | (``GT.gt, #[α, _, a, b]) =>
      if α.isConstOf ``Nat then
        return .app "LT.lt" [] [← reifyNatTerm acc b, ← reifyNatTerm acc a]
      expectArithCarrier α
      let sym := if (matchBitVecType? α).isSome then "BV.ult" else "LT.lt"
      return .app sym [] [← reifyTerm acc b, ← reifyTerm acc a]
  | (``Eq, #[α, a, b]) =>
      -- R3-M1: an equality at ℕ images to an Int equality of the
      -- cast operands.
      if α.isConstOf ``Nat then
        return .eq "Int" (← reifyNatTerm acc a) (← reifyNatTerm acc b)
      let tref ← reifyType α
      return .eq tref (← reifyTerm acc a) (← reifyTerm acc b)
  | (``Ne, #[α, a, b]) =>
      -- `a ≠ b` unfolds to `¬(a = b)`; reify it that way so the
      -- SMT serializer sees the ordinary (not (= a b)) shape
      -- instead of an uninterpreted `Ne` symbol.
      if α.isConstOf ``Nat then
        return .not_ (.eq "Int" (← reifyNatTerm acc a) (← reifyNatTerm acc b))
      let tref ← reifyType α
      return .not_ (.eq tref (← reifyTerm acc a) (← reifyTerm acc b))
  | (``Nat.cast, #[α, _, a]) | (``NatCast.natCast, #[α, _, a]) =>
      -- R3-M1: an explicit ℕ→ℤ cast in the source (a hand-zify'd
      -- goal) reifies as the operand's ℤ image — same shell the ℕ
      -- reifier produces, so mixed `↑x`-style Int goals join the
      -- specialization path.
      if α.isConstOf ``Int then reifyNatTerm acc a
      else throwError "proof_broker: ℕ cast into {α} unsupported \
             (only ↑(ℕ) : ℤ)"
  | (``Int.ofNat, #[a]) =>
      reifyNatTerm acc a
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
           return .exists_ nm.toString tref (← reifyTerm acc body)
       | _ =>
         throwError "proof_broker: unsupported ∃ shape (expected a \
           lambda body): {e}")
  | (``And, #[a, b]) =>
      return .and_ (← reifyTerm acc a) (← reifyTerm acc b)
  | (``Or, #[a, b]) =>
      return .or_ (← reifyTerm acc a) (← reifyTerm acc b)
  | (``Not, #[a]) =>
      return .not_ (← reifyTerm acc a)
  | _ =>
      -- UF fallback: the head is a free variable applied to
      -- arguments, with an arrow-typed declaration in scope.
      -- Emit `App { symbol = "UF.<fname>" }` and the SDK
      -- serializer takes care of the [declare-fun] /
      -- application emission. Anything else is genuinely
      -- unsupported.
      --
      -- R4.2: both symbol arms are now GUARDED on every argument
      -- type being declarable (`reifyType?`). Declaring `R.x` over
      -- `Fin n` is not something the IR can express, and the old
      -- code found that out by throwing from inside `reifyType`,
      -- which killed the whole reification; now the term falls
      -- through to the Int-atom arm at the bottom, which is what
      -- the R4 D3 obligations need ("`TableCert` fields as atoms").
      let fn := e.getAppFn
      let argTypesDeclarable (args : List Expr) : MetaM Bool :=
        args.allM (fun a => do return (← reifyType? (← inferType a)).isSome)
      if fn.isFVar && e.getAppNumArgs > 0 then
        let lctx ← getLCtx
        let decl := lctx.get! fn.fvarId!
        if decl.type.isArrow then
          let argList := e.getAppArgs.toList
          if ← argTypesDeclarable argList then
            let fname := decl.userName.toString
            let reifiedArgs ← argList.mapM (reifyTerm acc)
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
        let resTyOk := (← reifyType? (← inferType e)).isSome
        if resTyOk && (← argTypesDeclarable explicit.toList) then
          let parenIfArrow (ex : Expr) (s : String) : String :=
            if ex.isArrow then "(" ++ s ++ ")" else s
          let argTyParts ← explicit.toList.mapM (fun a => do
            let ta ← inferType a
            return parenIfArrow ta (← reifyType ta))
          let resTy ← inferType e
          let tref := String.intercalate "->" (argTyParts ++ [← reifyType resTy])
          acc.consts.modify (·.push (cname, tref))
          let reifiedArgs ← explicit.toList.mapM (reifyTerm acc)
          return .app cname [] reifiedArgs
      -- R4.2: last resort — an Int-VALUED term with a constant or
      -- free-variable head becomes an uninterpreted Int atom. The
      -- type restriction is the point: only Int (the fragment's own
      -- carrier) gets this treatment, so a Real/BV/α term outside
      -- the fragment still reports the fragment error rather than
      -- silently degrading.
      if (fn.isConst || fn.isFVar) && (← inferType e).isConstOf ``Int then
        return ← atomizeIntTerm acc e
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

/-- R3-M2: the canonical IR name for the (single, M2-scope)
    polymorphic type variable — spec Example 1's `"alpha"`. Chosen
    over the user's binder name so the wire format never carries a
    non-ASCII identifier; the substitution the SDK applies is on
    type TAGS, so the choice is invisible to the user. -/
def polyTypeVarName : String := "alpha"

/-- True iff any subterm carries `tag` as a type reference — on a
    `numLit`, an `eq`'s `ty`, or a binder's type. Drives the
    poly-mode decision (`buildIR` enters α mode only when the type
    variable is actually USED as a carrier, not merely in scope). -/
partial def shellMentionsTypeRef (tag : String) : ShellTerm → Bool
  | .var _ | .const _ | .opaque_ _ => false
  | .numLit _ ty => ty == tag
  | .eq ty a b =>
    ty == tag || shellMentionsTypeRef tag a || shellMentionsTypeRef tag b
  | .app _ tyArgs args =>
    tyArgs.any (· == tag) || args.any (shellMentionsTypeRef tag)
  | .and_ a b | .or_ a b | .implies a b =>
    shellMentionsTypeRef tag a || shellMentionsTypeRef tag b
  | .not_ a => shellMentionsTypeRef tag a
  | .forall_ _ ty b | .exists_ _ ty b =>
    ty == tag || shellMentionsTypeRef tag b
  | .lambda binders b =>
    binders.any (·.ty == tag) || shellMentionsTypeRef tag b

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
    statement. `library` labels the owning library (`"lean-core"`
    for the ℕ witnesses; the M2 extension passes
    `"proof-broker-bridge"` for its own lift family). -/
def witnessProvenance (library : String) (name : Name)
    : MetaM (String × Provenance) := do
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
    library,
    version := Lean.versionString,
    modulePath,
    contentHash := hash })

@[inherit_doc witnessProvenance]
def natWitnessProvenance (name : Name) : MetaM (String × Provenance) :=
  witnessProvenance "lean-core" name

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
    is ignored.

    R4.2: a **Prop hypothesis whose type does not reify is dropped**,
    not fatal. A real proof's context is full of propositions outside
    the fragment — in the verinf obligations, `hrec : c = x + z + …`
    over `ZMod P` sits in scope at every D1 goal — and aborting on
    them made the tactic unusable on anything but a hand-built
    context. Dropping only ever WEAKENS the assumption set, so a
    certificate for the reduced context certifies the original goal a
    fortiori; the goal itself is never dropped (it is reified outside
    this loop and its errors propagate, so the R3-M1 ℕ-truncation
    fail-fast still applies to everything the cert actually reads).
    Every drop is recorded with its reason and reported by
    `proof_broker?`, so "the solver ignored my hypothesis" is a
    visible fact rather than a guess. -/
def buildIRWithAcc (mvarId : MVarId)
    : MetaM ((IR × Array (String × Expr) × Array (String × Expr × Nat)
              × Array (String × String)) × ReifyAcc) :=
  mvarId.withContext do
  -- Instantiate metavariables in the goal type and drop its
  -- top-level annotation. `apply`-introduced subgoals may carry
  -- deferred unification metavars in their types, and the `have`
  -- tactic wraps its continuation goal in `noImplicitLambda`
  -- metadata; without this, `reifyTerm` sees `?_uniq.N` / `mdata`
  -- (both pretty-print as the user-facing term) and every
  -- structural match falls through to "unsupported expression".
  -- Create THIS call's accumulator (per-call, never module state:
  -- C4 ROUND 3 High — `reifyTerm` on the goal and each hypothesis
  -- below pushes applied non-connective constants, atoms and
  -- numeral defs into it, and `buildIR` folds them on exit).
  let acc ← ReifyAcc.fresh
  let goalType := (← Lean.instantiateMVars (← mvarId.getType)).consumeMData
  let goalShell ← reifyTerm acc goalType
  let mut freeVars : List FreeVar := []
  let mut hypotheses : List IR.Hypothesis := []
  -- (local name, why it was not reified) — see the docstring.
  let mut skipped : Array (String × String) := #[]
  let extOpt ← reifierExt.get
  let mut sawExtensionType : Bool := false
  let mut sawBV : Bool := false
  let mut sawUF : Bool := false
  let mut sawNat : Bool := false
  -- R3-M2: the (single) qualified polymorphic type variable of this
  -- extraction, with the metadata/provenance the extension reported.
  let mut polyVar : Option (FVarId × TypeVarInfo) := none
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    -- Symmetric with the target above (R4 continuation): a
    -- `have := e` or `by_cases` hypothesis is an assigned-but-
    -- uninstantiated metavariable, and a `have h : T := …` whose `T`
    -- needed a coercion or a default instance keeps assigned
    -- metavariables inside `T`. Read raw, `reifyTerm` fell through
    -- every structural match and `observing?` below DROPPED the
    -- hypothesis as "outside the fragment" — measured as the solver
    -- answering sat on the verinf `D3/170` / `D3/180` obligations
    -- (demo `reference/ctx/dump.log`). The tactic front-ends
    -- normalize the whole goal first (`normalizeGoalForBroker`);
    -- this keeps `buildIR` itself correct for callers that do not
    -- go through them (pinned by `reify_hyp_count_test`).
    let ty := (← Lean.instantiateMVars decl.type).consumeMData
    -- R3-M2: typeclass-instance locals (`inst : CommRing α`,
    -- `IsStrictOrderedRing α` — the latter is Prop-valued and would
    -- otherwise land in the hypothesis branch) are class METADATA,
    -- not reifiable hypotheses/data; the type-variable recognition
    -- below reads them through instance synthesis instead. Before
    -- M2 such locals either fell through untouched (Type-valued
    -- classes) or made the Prop reifier fail fast; skipping is the
    -- sound direction — dropping an assumption only weakens what
    -- the solver may use.
    if (← Lean.Meta.isClass? ty).isSome then continue
    -- R3-M2: a `Sort`-typed local is a candidate type variable.
    -- The extension decides qualification (the ordered-ring
    -- instances its lift family needs must be synthesizable);
    -- unqualified sort locals stay ignored exactly as before.
    if ty.isSort && !ty.isProp then
      if let some ext := extOpt then
        if let some info ← ext.typeVarInfo? decl.toExpr then
          if polyVar.isSome then
            throwError "proof_broker: more than one qualified \
              polymorphic type variable in scope (R3-M2 scope: a \
              single α)"
          polyVar := some (decl.fvarId, info)
      continue
    if ← isProp ty then
      match ← observing? (reifyTerm acc ty) with
      | some shell =>
        hypotheses := hypotheses ++ [{ name := decl.userName.toString, shell }]
      | none =>
        skipped := skipped.push (decl.userName.toString,
          s!"proposition outside the reifiable fragment ({← Lean.Meta.ppExpr ty})")
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
    else if ty.isFVar && polyVar.any (·.1 == ty.fvarId!) then
      -- R3-M2: a data local at the qualified type variable is an
      -- arithmetic free var declared at the CANONICAL tag "alpha";
      -- the SDK refinement pass substitutes alpha → Int (recorded
      -- with the extension's real witness) before the SMT
      -- serializer runs.
      freeVars := freeVars ++ [{ name := decl.userName.toString,
                                 ty := polyTypeVarName }]
    else if ty.isProp then
      -- A local `p : Prop` is a Boolean ATOM, not a hypothesis
      -- (`isProp ty` above matched locals whose type IS a
      -- proposition; here the type is `Prop` itself). Declare it
      -- as a free var — the SDK serializer maps the `Prop` type
      -- ref to SMT-LIB `Bool` — so pure-propositional goals
      -- (`∀ p q : Prop, …`) dispatch with their atoms declared.
      freeVars := freeVars ++ [{ name := decl.userName.toString, ty := "Prop" }]
    else if ty.isArrow then
      -- Function-typed local: a UF candidate, IF every link of the
      -- arrow chain is a type the IR can declare. `R.x : Fin n → ℤ`
      -- is not (R4.2) — it is left undeclared and its applications
      -- atomize.
      match ← reifyType? ty with
      | some tref =>
        freeVars := freeVars ++ [{ name := decl.userName.toString, ty := tref }]
        sawUF := true
      | none =>
        skipped := skipped.push (decl.userName.toString,
          s!"function type outside the IR's type language ({← Lean.Meta.ppExpr ty})")
    else
      match extOpt with
      | some ext =>
        match ← ext.freeVarType ty with
        | some tref =>
          freeVars := freeVars ++ [{ name := decl.userName.toString, ty := tref }]
          sawExtensionType := true
        | none =>
          skipped := skipped.push (decl.userName.toString,
            s!"data local at an undeclarable type ({← Lean.Meta.ppExpr ty})")
      | none =>
        skipped := skipped.push (decl.userName.toString,
          s!"data local at an undeclarable type ({← Lean.Meta.ppExpr ty})")
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
  for (cname, ctref) in (← acc.consts.get) do
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
  let natAtoms ← acc.natAtoms.get
  let natDefs ← acc.natDefs.get
  let natMode := sawNat || !natAtoms.isEmpty
  if natMode && (sawBV || bvInTerms || sawUF || ufInTerms || isHO
                 || sawExtensionType) then
    throwError "proof_broker: ℕ variables cannot mix with UF / BV / \
      higher-order / extension carriers yet (R3-M1 scope: pure ℕ \
      linear arithmetic)"
  -- R3-M2: α mode = a qualified type variable in scope AND used as a
  -- carrier (a free var declared at "alpha", or an "alpha"-tagged
  -- literal/equality in some shell). A type variable merely in scope
  -- over an Int/ℕ goal does not switch modes.
  let polyMode := polyVar.isSome && (
    freeVars.any (·.ty == polyTypeVarName)
    || shellMentionsTypeRef polyTypeVarName goalShell
    || hypotheses.any (fun h => shellMentionsTypeRef polyTypeVarName h.shell))
  if polyMode && (natMode || sawBV || bvInTerms || sawUF || ufInTerms
                  || isHO || sawExtensionType) then
    throwError "proof_broker: a polymorphic type variable cannot mix \
      with ℕ / UF / BV / higher-order / Real carriers yet (R3-M2 \
      scope: pure α linear arithmetic)"
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
    -- R3-M2: a type-variable IR classifies "none" pending refinement
    -- (the fixture/spec convention; `Farkas.effective_fragment`
    -- defaults it to LIA and refinement picks the host type from the
    -- embedding tags — the actual classifier for these IRs).
    else if polyMode then "none"
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
  let typeMetadata :=
    (if natMode then [("Nat", natTypeMetadata)] else [])
    -- R3-M2: the type-variable entry the extension reported — the
    -- `embedding_witness:` tags inside it name the α lift family,
    -- and refinement copies them into the cert's soundness_witness.
    ++ (match polyVar with
        | some (_, info) =>
          if polyMode then [(polyTypeVarName, info.metadata)] else []
        | none => [])
  let libraryProvenance ←
    if natMode then natEmbeddingWitnessLemmas.mapM natWitnessProvenance
    else pure []
  let libraryProvenance := libraryProvenance
    ++ (match polyVar with
        | some (_, info) => if polyMode then info.provenance else []
        | none => [])
  -- R3-M3: one `defined_function` entry + provenance (content hash
  -- of the pretty-printed definition body) per numeral-body
  -- constant, plus the user directive naming the concept tag — the
  -- registry's always-unfold list carries it too, so the pipeline
  -- unfolds these on every dispatch and the trace records the
  -- inversion data the lift consumes.
  let definitionalMetadata := natDefs.toList.map (fun (name, _e, n) =>
    (name, Json.mkObj [
      ("kind", "defined_function"),
      ("abstract_signature", "Int"),
      ("definitional_equation",
        (ShellTerm.eq "Int" (.app name [] [])
          (.numLit (toString n) "Int")).toJson),
      ("concept_tag", "numeral_definition")]))
  let defProvenance ← natDefs.toList.mapM (fun (name, e, _n) => do
    let .const c _ := e
      | throwError "proof_broker: numeral-def table holds a non-const"
    let env ← Lean.getEnv
    let some (.defnInfo d) := env.find? c
      | throwError "proof_broker: numeral def {c} vanished"
    let stmt ← Lean.Meta.ppExpr d.value
    let hash ← match runContentHash (toString stmt) with
      | .ok h => pure h
      | .error err =>
        throwError "proof_broker: content_hash FFI failed: {repr err}"
    let modulePath := env.getModuleIdxFor? c |>.map fun idx =>
      toString env.allImportedModuleNames[idx.toNat]!
    pure (name, ({
      library := "user",
      version := Lean.versionString,
      modulePath,
      contentHash := hash } : Provenance)))
  let libraryProvenance := libraryProvenance ++ defProvenance
  let userDirectives : Option UserDirectives :=
    if natDefs.isEmpty then none
    else some {
      preferredBackend := none, tierPreference := none,
      rewriterPreferences := some {
        enableQuotientElimination := none,
        enableDefinitionUnfolding := some ["numeral_definition"],
        disablePasses := none },
      budget := none }
  let intAtoms ← acc.intAtoms.get
  let payloads ←
    if natAtoms.isEmpty && intAtoms.isEmpty then pure none
    else do
      let mk (kind : String) (id : String) (e : Expr) : MetaM (String × Json) := do
        let pp ← Lean.Meta.ppExpr e
        return (id, Json.mkObj [
          ("kind", Json.str kind),
          ("lean", Json.str (toString pp))])
      let natEntries ← natAtoms.toList.mapM (fun (id, e) => mk "nat_nonlinear_atom" id e)
      let intEntries ← intAtoms.toList.mapM (fun (id, e) => mk "int_opaque_atom" id e)
      pure (some (Json.mkObj (natEntries ++ intEntries)))
  -- The atom table rides on the RETURN VALUE, not the module ref:
  -- Lean elaborates theorems in parallel, so a ref read at
  -- closer time can race another invocation's `buildIR` reset
  -- (observed as an unknown-free-variable failure). The ref is
  -- only the accumulator WITHIN this reify.
  return (({
    irVersion := "1.0",
    sourceSystem := { name := "lean", version := "0.0" },
    tier,
    logicClassification := {
      order, featuresUsed,
      firstOrderFragment := fragment, decidableTheory := none
    },
    goal := { shell := goalShell, payloads },
    context := {
      typeVars := if polyMode then [polyTypeVarName] else [],
      freeVars, hypotheses, librarySlice := none },
    typeMetadata,
    definitionalMetadata,
    libraryProvenance,
    userDirectives
  }, natAtoms, natDefs, skipped), acc)

/-- The public reification entry point. `buildIRWithAcc` additionally
    returns the `ReifyAcc` the reification ACTUALLY accumulated into
    — consumed only by the call-site isolation pin
    (`reify_callsite_isolation_test`), which is what makes the
    per-call discipline testable independent of how a regression is
    SPELLED (C4 ROUND 8 Med 1: the textual source gate lost an
    arms race per round — `@[init]`, indentation, hardcoded file
    lists — because it pinned spellings; the returned accumulator
    pins the behavior). -/
def buildIR (mvarId : MVarId)
    : MetaM (IR × Array (String × Expr) × Array (String × Expr × Nat)
             × Array (String × String)) := do
  let (r, _) ← buildIRWithAcc mvarId
  return r

end Reify

/- ============================================================
   Manifest loading

   Manifests sit alongside the test fixtures in `examples/`. The
   tactic finds them by:
     1. honoring `PROOF_BROKER_EXAMPLES_DIR` if set (verbatim, no
        probe — an explicit override that is wrong must fail loudly,
        not fall through to some other directory),
     2. otherwise `<cwd>/../examples`, the in-repo convention
        Main.lean also uses,
     3. otherwise a *package-anchored* directory derived from where
        this module's own `.olean` was loaded from (R4.1).

   Step 3 is what makes the tactic usable from a downstream Lake
   project. Steps 1–2 are cwd-relative, and a consumer's cwd is its
   own project root, not the bridge's — so before R4.1 every
   downstream call died with "no manifests found in
   <consumer>/../examples" unless the user exported the env var by
   hand. `findBridgeExamplesDir?` resolves `ProofBroker.Tactic`
   against LEAN_PATH, which Lake populates with the bridge's build
   directory in both dependency flavors (a `from git` require
   materialized under `.lake/packages/`, and a `from "…"` path
   require built in place).
   ============================================================ -/

/-- The four manifest file names the tactic ever loads. Shared by
    the directory probe and `loadDefaultManifests` so "this directory
    is the manifest directory" and "these are the manifests" can
    never drift apart. Vampire last: `capability_match` skips it for
    first-order LIA/LRA/BV goals, so the order is for determinism,
    not precedence. -/
private def manifestFileNames : List String :=
  ["manifest-cvc4.json", "manifest-cvc5.json",
   "manifest-z3.json", "manifest-vampire.json"]

/-- True iff `dir` holds at least one of `manifestFileNames` — the
    same predicate as "`loadDefaultManifests` would find something
    here", so probing a candidate never rejects a directory the
    loader would have accepted. -/
private def dirHasManifest (dir : System.FilePath) : IO Bool :=
  manifestFileNames.anyM (fun n => (dir / System.FilePath.mk n).pathExists)

/-- The `examples/` directory that ships next to the loaded bridge,
    or `none` if the layout does not match (an installed/relocated
    olean, a vendored build). Never throws: a failed lookup just
    means the caller falls back to the cwd-relative candidate and
    reports both in its error.

    `Lean.findOLean` returns
    `<bridge>/.lake/build/lib/lean/ProofBroker/Tactic.olean`; six
    `parent` steps reach `<bridge>` (the `lean-bridge` package
    directory) and the manifests live one level above it, in the
    proof-broker repo root. -/
private def findBridgeExamplesDir? : IO (Option System.FilePath) := do
  -- Module name, not a declaration name, so a single backtick: it is
  -- resolved against LEAN_PATH at run time, and a miss (renamed
  -- module, no olean on the path when running from source) returns
  -- `none` rather than throwing.
  let .ok olean ← (Lean.findOLean `ProofBroker.Tactic).toBaseIO
    | return none
  unless ← olean.pathExists do return none
  -- Tactic.olean → ProofBroker → lean → lib → build → .lake → <bridge>
  let mut dir := olean
  for _ in [0:6] do
    let some p := dir.parent | return none
    dir := p
  let cand := dir / ".." / "examples"
  if ← dirHasManifest cand then return some cand else return none

private def defaultManifestDir : IO System.FilePath := do
  match (← IO.getEnv "PROOF_BROKER_EXAMPLES_DIR") with
  | some s => return s
  | none =>
    -- The cwd candidate keeps priority and is only stepped over when
    -- it holds no manifest at all — i.e. exactly in the cases where
    -- the pre-R4.1 behavior was to raise "no manifests found".
    let cwdCand := (← IO.currentDir) / ".." / "examples"
    if ← dirHasManifest cwdCand then return cwdCand
    match ← findBridgeExamplesDir? with
    | some d => return d
    | none => return cwdCand

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
  let mut result : List Json := []
  for n in manifestFileNames do
    if let some j ← loadManifestIfPresent (dir / n) then
      result := result ++ [j]
  if result.isEmpty then
    throwError "proof_broker: no manifests found in {dir}; \
                set PROOF_BROKER_EXAMPLES_DIR, run from a directory \
                whose parent has examples/manifest-*.json, or build \
                against a bridge whose package directory has \
                ../examples (the downstream-consumer layout)"
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
      ℕ product of this extraction — the snapshot of this call's
      per-call accumulator (`Reify.ReifyAcc.natAtoms`; the module
      ref this once cited was deleted at C4 ROUND 3 — accumulation
      itself is per-call now, so nothing can reset it between the
      reify and the closer). -/
  natAtoms : Array (String × Expr) := #[]
  /-- R3-M3: `constant name ↦ (const Expr, ℕ value)` for every
      numeral-body definition this extraction documented in
      `definitional_metadata` — the set of unfolds the term-mode
      lift can invert. Carried on the path for the same
      parallel-elaboration reason as `natAtoms`. -/
  natDefs : Array (String × Expr × Nat) := #[]
  /-- R4.2: locals `buildIR` did not put in the IR, with the reason
      — a proposition outside the fragment, a function type the IR
      cannot declare, a data local at an undeclarable type. Dropping
      only weakens the assumption set, but a reader has to be able
      to SEE what was dropped; `proof_broker?` prints this. -/
  skippedLocals : Array (String × String) := #[]
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
  let skipLines :=
    if path.skippedLocals.isEmpty then []
    else "  skipped:  locals not in the IR (assumptions dropped, goal unaffected)"
      :: path.skippedLocals.toList.map (fun (n, why) => s!"              {n} — {why}")
  let lines := ["proof_broker?:", irLine] ++ skipLines ++ [dispatchLine] ++ attemptLines
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
  let (ir, natAtoms, natDefs, skippedLocals) ← Reify.buildIR goal
  -- Walker-strict callers pass `tierPreference := some ["3"]`:
  -- the IR's `user_directives.tier_preference` (spec §5.4) tells
  -- the cvc5 adapter to mint the verified Tier-3 alethe trace
  -- ahead of the term-mode-friendly Tier-2/1 witnesses. The
  -- default dispatch is unchanged. R3-M3: MERGED into any
  -- reifier-set directives (the numeral-def unfolding preference
  -- must survive the override).
  let ir := match tierPreference with
    | none => ir
    | some tp =>
      let ud := ir.userDirectives.getD {
        preferredBackend := none, tierPreference := none,
        rewriterPreferences := none, budget := none }
      { ir with userDirectives := some { ud with tierPreference := some tp } }
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
    natAtoms, natDefs, skippedLocals
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
   R3-M3: definition-unfold inversion — the guard lifted for the
   definition_unfolding pass on the term-mode path.

   The dispatch pipeline may now genuinely rewrite a ℕ goal: a
   numeral-body constant the reifier documented in
   `definitional_metadata` is replaced by its numeral (trace entry
   with `inversion_data.unfolded_symbols`). The term-mode closer
   admits such traces — and ONLY such traces — by first rewriting
   the goal (and any hypothesis mentioning the constant) with the
   unfolding equation `c = <numeral>` via `Eq.mpr` (`rfl` up to
   kernel delta reduction), so the cert's witness addresses exactly
   what remains. Every other applied/failed pass keeps the R2
   identity requirement; the walker paths are unchanged (identity
   only).
   ============================================================ -/

/-- Symbols named by a definition_unfolding entry's
    `inversion_data.unfolded_symbols`. -/
private def entryUnfoldedSymbols (e : Trace.Entry) : List String :=
  match e.inversionData with
  | none => []
  | some j =>
    (((j.getObjVal? "unfolded_symbols").toOption.bind
      (·.getArr?.toOption)).getD #[]).toList.filterMap
      (fun s => (s.getObjValAs? String "symbol").toOption)

/-- All unfolded symbols across the trace's def-unfold entries. -/
private def traceUnfoldedSymbols (d : Trace.Document) : List String :=
  d.entries.foldl (fun acc e =>
    if e.pass == "definition_unfolding" then acc ++ entryUnfoldedSymbols e
    else acc) []

/-- Trace admissibility for the TERM-MODE path (R3-M3): `none` when
    the trace is identity, or when every non-identity entry is an
    APPLIED definition unfold whose symbols are all ones this
    extraction emitted the unfolding equation for (`path.natDefs`).
    Anything else — a missing trace, a failed pass, an applied pass
    with no inversion here (prop-simp), a foreign unfolded symbol —
    is a named error, fail closed. -/
private def termTraceError? (path : ExtractionPath) : Option String :=
  match path.trace with
  | none => some "proof_broker_term: the dispatch returned no rewrite \
      trace, so the cert cannot be tied to this goal (fail closed)"
  | some d =>
    if d.isIdentity then none
    else Id.run do
      let defNames := path.natDefs.map (·.1)
      let mut admitted := false
      for e in d.entries do
        let identityShaped :=
          (match e.outcome with
           | some .skippedPreconditions | some .noOp => true
           | _ => false)
          && e.beforeHash == e.afterHash
        if identityShaped then continue
        unless e.pass == "definition_unfolding"
            && e.outcome == some .applied do
          return some s!"proof_broker_term: the dispatch pipeline's \
            '{e.pass}' pass rewrote the goal and this bridge has no \
            inversion for it; the cert addresses the rewritten IR, \
            so the goal is left OPEN (fail closed)"
        -- An APPLIED unfold must name what it unfolded: admission
        -- means "every rewrite is one we invert", so an entry whose
        -- inversion_data is absent, malformed or empty is a refusal,
        -- not a vacuous pass over zero symbols. (The SDK cannot emit
        -- this shape — Applied implies non-empty inversion data —
        -- so this branch only fires on a hand-built or drifted
        -- trace.)
        if (entryUnfoldedSymbols e).isEmpty then
          return some s!"proof_broker_term: the trace's applied \
            'definition_unfolding' entry names no parseable \
            unfolded symbols, so its rewrite cannot be inverted — \
            refusing to consume the cert (fail closed)"
        for sym in entryUnfoldedSymbols e do
          unless defNames.contains sym do
            return some s!"proof_broker_term: the trace unfolds \
              '{sym}', which this extraction did not emit an \
              unfolding equation for — refusing to consume the cert \
              (fail closed)"
        admitted := true
      -- The document is not identity, so SOME entry must own the
      -- rewrite. A trace whose endpoint hashes disagree while every
      -- entry is identity-shaped (or the entry list is empty) is
      -- refused: admission must always mean "an inversion ran",
      -- never a vacuous walk over nothing.
      unless admitted do
        return some "proof_broker_term: the trace's endpoint hashes \
          disagree but no entry admits a rewrite, so the rewritten \
          IR cannot be tied to this goal — refusing to consume the \
          cert (fail closed)"
      return none

/-- Does `c` occur in `e` only at VALUE positions — never inside a
    subterm that is itself a type?

    R4.2, and the reason this check exists at all: unfolding a
    numeral definition is a `kabstract` over *every* occurrence, and
    an occurrence sitting inside a TYPE turns a cheap swap into a
    kernel bomb. verinf's `lift_cell` reifies
    `hmul : ((Zmax : ZMod P) * zhigh).val = Zmax * zhigh.val`, where
    `P` appears in the `ZMod P` type arguments of `HMul.hMul`.
    Rewriting those gives a term at `ZMod 18446744069414584321`
    while its neighbours are still at `ZMod P`, and the next defeq
    check has to whnf `ZMod <literal>` — `ZMod` recurses on ℕ, so
    that is `Nat.rec` at 2^64 scale, unary and astronomically beyond
    any machine. The mechanism is ARGUED from `ZMod`'s definition,
    not measured: no reproducible artifact of this bomb exists (the
    ~57 GB event once cited here belongs to `Farkas_search.cartesian`
    — C4 ROUND 1/2, delta.md §5.7). The refusing branch is pinned
    DETERMINISTICALLY by `type_pos_gate_test` (a direct verdict
    check in both directions — the end-to-end `PBModP` negative in
    `Test/TacticMathlib.lean` documents the user-facing refusal but
    fails under any closer outcome, so it cannot pin the gate).

    `hbound : Zmax * zhigh.val < P` passes: its `P`s are ℕ values,
    including the `@ZMod.val P zhigh` index, which unifies with the
    numeral by delta in one step. `hmul` and `hZval` are rejected —
    and nothing is lost, since the arithmetic the certificate reads
    from them never mentions `P`. -/
private partial def constOnlyInValuePositions (c : Name) (e : Expr) : MetaM Bool := do
  let mentions (x : Expr) : Bool := (x.find? (·.isConstOf c)).isSome
  if !mentions e then return true
  match e with
  | .app .. =>
    let fn := e.getAppFn
    if mentions fn && !fn.isConstOf c then return false
    for a in e.getAppArgs do
      if mentions a then
        -- An argument that IS a type (its own type is a sort) must
        -- not mention the constant at all; anything else recurses.
        if (← Lean.Meta.inferType a).isSort then return false
        unless ← constOnlyInValuePositions c a do return false
    return true
  | .lam _ d b _ | .forallE _ d b _ =>
    if mentions d then
      if (← Lean.Meta.inferType d).isSort then return false
      unless ← constOnlyInValuePositions c d do return false
    -- The body may have loose bvars; only the constant matters here,
    -- and `find?` does not care about binder depth.
    constOnlyInValuePositions c b
  | .mdata _ b => constOnlyInValuePositions c b
  | .proj _ _ b => constOnlyInValuePositions c b
  | .letE _ t v b _ =>
    if mentions t then return false
    unless ← constOnlyInValuePositions c v do return false
    constOnlyInValuePositions c b
  | .const n _ => return n == c
  | _ => return true

/-- Apply the def-unfold inversions to `goal`: for every symbol the
    trace unfolded, rewrite the goal with `c = <numeral>` (proved by
    `rfl` — the constant's body IS the numeral, so the kernel checks
    it by delta reduction; the lifted term carries the resulting
    `Eq.mpr`), and defeq-swap the type of every Prop hypothesis
    mentioning the constant. No-op on an identity trace. -/
private def invertDefUnfolds (goal : MVarId) (path : ExtractionPath)
    : TacticM MVarId := do
  let some d := path.trace | return goal
  if d.isIdentity then return goal
  let mut g := goal
  for sym in (traceUnfoldedSymbols d).eraseDups do
    let some (_, constE, val) := path.natDefs.find? (·.1 == sym)
      | throwError "proof_broker_term: trace unfolds '{sym}' but the \
          extraction has no such definition (fail closed)"
    let cName := constE.constName!
    g ← g.withContext do
      let litE := Lean.mkNatLit val
      -- Fail closed on a recorded value that is not the definition's
      -- body: everything below is a defeq swap of `c` for `litE`, so
      -- check that defeq ONCE, here, with a named error — rather than
      -- letting a bad extraction surface as a kernel type error at
      -- `Theorem`-add time (it would still be caught, but not
      -- attributably).
      unless ← Lean.Meta.isDefEq constE litE do
        throwError "proof_broker_term: the extraction records \
          '{cName} = {val}' but {cName} is not definitionally that \
          numeral (fail closed)"
      -- Goal: swap the constant for its numeral, justified by the
      -- same kernel defeq the unfolding equation records.
      --
      -- NOT `rewrite`/`Eq.mpr` (R4.2): `rewrite` has to build a
      -- motive `fun _a => …`, and the constant being unfolded may
      -- occur in a TYPE inside the goal as well as at an arithmetic
      -- position. The verinf D1 obligation `x.val + z.val < P` with
      -- `x z : ZMod P` is exactly that shape, and the motive
      -- `fun _a => (@ZMod.val _a x) + _ < _a` does not typecheck
      -- ("motive is not type correct"). `change` needs no motive:
      -- it checks the two targets defeq — which they are, by delta
      -- on `P` — and the cast it inserts is re-checked by the
      -- kernel when the theorem is added, so a bad swap is a build
      -- error, never a silent one.
      let mut g' := g
      let tgt ← g'.getType
      if tgt.getUsedConstantsAsSet.contains cName then
        unless ← g'.withContext (constOnlyInValuePositions cName tgt) do
          throwError "proof_broker_term: the extraction unfolds \
            '{cName}', but the goal mentions it inside a TYPE \
            ({tgt}); inverting the unfold there would force the \
            kernel to reduce that type at the definition's value. \
            Fail closed rather than build a term the kernel cannot \
            check cheaply."
        let tgtNew ← g'.withContext do
          let abst ← Lean.Meta.kabstract tgt constE
          pure (abst.instantiate1 litE)
        g' ← g'.change tgtNew
      -- Hypotheses: the rewritten type is defeq, so swap in place —
      -- but ONLY in hypotheses this extraction actually reified.
      --
      -- R4.2: rewriting every local that merely MENTIONS the constant
      -- is a memory bomb. In verinf's `lift_cell` the context holds
      -- `hrec : c = x + z + ↑Zmax * zhigh` at type `ZMod P`, which the
      -- reifier drops (it is outside the fragment) — but `kabstract`
      -- happily turned `ZMod P` into `ZMod 18446744069414584321`, and
      -- `ZMod` is defined by recursion on ℕ, so the next defeq check
      -- on that type would reduce `Nat.rec` at a 2^64-scale literal —
      -- unary, beyond any machine. Argued from the definitions, not
      -- measured (the ~57 GB figure once cited here was the
      -- Farkas-search materialization — delta.md §5.7).
      --
      -- The extraction's own hypothesis list is the right scope: it is
      -- exactly the set the certificate reads, every member reified
      -- inside the arithmetic fragment (so the constant occurs at an
      -- arithmetic position, never as a type index), and it is what
      -- the fallback decision procedure needs unfolded. Anything the
      -- reifier declined is left alone.
      let irHypNames := path.ir.context.hypotheses.map (·.name)
      let mut swaps : Array (FVarId × Expr) := #[]
      for decl in (← g'.withContext getLCtx) do
        if decl.isImplementationDetail then continue
        unless irHypNames.contains decl.userName.toString do continue
        -- Skip, don't fail: a hypothesis is optional context for the
        -- fallback, so leaving one un-unfolded costs completeness at
        -- worst. The goal above is not optional, hence the error.
        unless ← g'.withContext (constOnlyInValuePositions cName decl.type) do
          continue
        if decl.type.getUsedConstantsAsSet.contains cName then
          if ← g'.withContext (Lean.Meta.isProp decl.type) then
            let newTy ← g'.withContext do
              let abst ← Lean.Meta.kabstract decl.type constE
              pure (abst.instantiate1 litE)
            swaps := swaps.push (decl.fvarId, newTy)
      for (fvarId, newTy) in swaps do
        g' ← g'.replaceLocalDeclDefEq fvarId newTy
      pure g'
  return g

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

/-- R4.2: does `goal.payloads` carry a ℕ atomization entry? Since
    Int atomization writes into the same object (`kind` =
    `int_opaque_atom`), "payloads present" is no longer the same
    question as "ℕ mode" — reading the kind is. Getting this wrong
    fails CLOSED (an Int goal misread as ℕ mode demands a `Nat`
    specialization record the cert does not have, and `specGate`
    refuses), but it would refuse every atomized ℤ goal. -/
private def hasNatAtomPayload (ir : IR) : Bool :=
  match ir.goal.payloads with
  | none => false
  | some (.obj kvs) =>
    kvs.any (fun _ v =>
      match v.getObjValAs? String "kind" with
      | .ok k => k == "nat_nonlinear_atom"
      | .error _ => false)
  | some _ => false

/-- ℕ mode of an extraction: the reified IR declared a ℕ free var
    or atomized a ℕ subterm (`nat_nonlinear_atom` payloads). -/
private def natModeOf (ir : IR) : Bool :=
  ir.context.freeVars.any (·.ty == "Nat") || hasNatAtomPayload ir

/-- R3-M2: α mode of an extraction — the reified IR declares the
    canonical type variable. -/
private def polyModeOf (ir : IR) : Bool :=
  !ir.context.typeVars.isEmpty

/-- Which specialization set a closer path can invert (R3). The
    walker paths invert only the ℕ→ℤ cast layer (`.nat` on a ℕ
    extraction, `.int` otherwise — an α cert is refused there); the
    term-mode path additionally inverts the α→Int specialization by
    replaying the Farkas coefficients at α (`.poly`). -/
private inductive SpecMode
  | int  -- no specialization consumable
  | nat  -- exactly the Nat → Int record, required present
  | poly -- exactly the alpha → Int record, required present
deriving BEq, Repr

/-- Fail-closed specialization gate — the R3 analog of R2's
    identity-trace guard, lifted pass-by-pass as inversions land: a
    cert-consuming closer runs only when every specialization the
    cert records is one the CALLING PATH inverts (`SpecMode`). In ℕ
    and α modes the respective record must be PRESENT — a cert
    minted over a specialized IR with no recorded specialization
    means refinement did not happen honestly. -/
private def certSpecializationsError? (cert : Json) (mode : SpecMode)
    : Option String := Id.run do
  let specs := ((cert.getObjVal? "refinement_record").bind
    (·.getObjVal? "specializations")).toOption.bind
    (·.getArr?.toOption) |>.getD #[]
  let mut sawRequired := false
  for s in specs do
    let kind := (s.getObjValAs? String "kind").toOption.getD ""
    let source := (s.getObjValAs? String "source").toOption.getD ""
    let target := (s.getObjValAs? String "target").toOption.getD ""
    if mode == .nat && kind == "type_specialization" && source == "Nat"
        && target == "Int" then
      sawRequired := true
    else if mode == .poly && kind == "type_specialization"
        && source == Reify.polyTypeVarName && target == "Int" then
      sawRequired := true
    else
      return some s!"proof_broker: the cert records a specialization \
        this closer path cannot invert (kind={kind}, {source} → \
        {target}); the goal is left OPEN rather than closed from a \
        cert whose translation has no lift here (fail closed)"
  if mode == .nat && !sawRequired then
    return some "proof_broker: ℕ goal, but the cert records no \
      Nat → Int type specialization — refusing to consume it \
      (fail closed)"
  if mode == .poly && !sawRequired then
    return some s!"proof_broker: polymorphic-α goal, but the cert \
      records no {Reify.polyTypeVarName} → Int type specialization — \
      refusing to consume it (fail closed)"
  return none

private def checkCertSpecializations (cert : Json) (mode : SpecMode)
    : TacticM Unit := do
  match certSpecializationsError? cert mode with
  | some msg => throwError msg
  | none => pure ()

/-- The `SpecMode` for the WALKER paths: they invert the ℕ cast
    layer only — an α-specialized cert is refused (strict) or
    skipped (plain-path semantics). -/
private def walkerSpecMode (ir : IR) : SpecMode :=
  if natModeOf ir then .nat else .int

/-- The `SpecMode` for the TERM-MODE path, which additionally
    replays α certs at α. -/
private def termSpecMode (ir : IR) : SpecMode :=
  if natModeOf ir then .nat
  else if polyModeOf ir then .poly
  else .int

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
        -- the lift rebuilds the ℕ proof from it. The specialization
        -- gate applies with the guard's plain-path semantics: a
        -- non-invertible record SKIPS the walker attempt (the
        -- fallback re-proves the original goal itself), where the
        -- strict entry points fail closed with the named error.
        if certTraceFormat cert == "alethe-2024" && identityTraceOk path
            && (certSpecializationsError? cert (walkerSpecMode path.ir)).isNone then
          -- R4.2: checkpoint the TACTIC state around the attempt.
          -- Both walkers reach `falseOrByContra`, which ASSIGNS the
          -- main goal, before they can know whether the walk will
          -- succeed; a later failure returned `false` with the goal
          -- already assigned, and the omega fallback below then died
          -- with "No goals to be solved" instead of closing the
          -- goal. The `false` contract ("leaves the goal untouched")
          -- is what the fallback rests on, so restore it here rather
          -- than trust each walker to unwind itself.
          let st ← saveState
          let ok ←
            if natModeOf path.ir then
              tryAletheWalkerNat cert path.ir path.natAtoms
            else tryAletheWalker cert
          unless ok do st.restore
          pure ok
        else
          pure false
      unless walkerHandled do
        -- R3-M2: an α extraction has no decision-procedure closer
        -- (omega is Int/ℕ-only). If the cert is a Tier-1 Farkas
        -- witness whose specializations the term-mode path inverts,
        -- replay it at α through the extension's polymorphic family;
        -- anything else is an honest tactic failure. The replay
        -- CONSUMES the cert, so the R2 trace requirement applies
        -- here exactly as on the term-mode entry — and an α
        -- extraction CAN emit unfolding equations (a ℕ-typed
        -- hypothesis over numeral-body constants fills `natDefs`
        -- without tripping ℕ mode), so what `termTraceError?`
        -- admits is identity OR extraction-emitted definition
        -- unfolds, which are inverted here exactly as on the
        -- term-mode entry and the ℕ/Int arm below. With no
        -- decision-procedure fallback at α, any other trace is a
        -- named failure, never a silent consume.
        if polyModeOf path.ir then
          if let some msg := termTraceError? path then
            throwError msg
          if !identityTraceOk path then
            let g ← invertDefUnfolds (← getMainGoal) path
            replaceMainGoal [g]
          checkCertSpecializations cert (termSpecMode path.ir)
          match ← reifierExt.get with
          | some ext => ext.polyFarkasCloser cert path.ir
          | none =>
            throwError "proof_broker: the broker certified this \
              polymorphic-α goal but no α closer is registered. \
              `import ProofBrokerMathlib` to enable the \
              class-polymorphic Farkas term builder. The goal is left \
              OPEN rather than closed by an unjustified axiom."
        else
          -- R3-M3: omega re-proves the ORIGINAL goal and cannot see
          -- through a non-reducible numeral definition; when the
          -- pipeline's only rewrites are invertible definition
          -- unfolds, apply the same inversion first. A trace this
          -- bridge cannot invert keeps today's behavior (omega on
          -- the original goal — sound, possibly incomplete).
          if !identityTraceOk path && (termTraceError? path).isNone then
            let g ← invertDefUnfolds (← getMainGoal) path
            replaceMainGoal [g]
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
        -- R3-M1: same plain-path specialization-gate skip as the
        -- LIA arm (ℕ never reaches UF/UFLIA — carrier mixing is a
        -- reifier error — so natMode is false here by construction).
        if certTraceFormat cert == "alethe-2024" && identityTraceOk path
            && (certSpecializationsError? cert (walkerSpecMode path.ir)).isNone then
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
        -- R3-M1: same plain-path specialization-gate skip as the
        -- LIA arm (ℕ never reaches UF/UFLIA — carrier mixing is a
        -- reifier error — so natMode is false here by construction).
        if certTraceFormat cert == "alethe-2024" && identityTraceOk path
            && (certSpecializationsError? cert (walkerSpecMode path.ir)).isNone then
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

/-- R4 continuation: bring the goal into the form a declaration
    header gives an `example` — every assigned metavariable in the
    target and the local context instantiated, and the target's
    top-level `Expr.mdata` annotation removed.

    Measured on the verinf spike (demo `reference/ctx/dump.log`,
    2026-09-05): a tactic-internal goal is NOT in that form. The
    `have` tactic leaves its continuation goal wrapped in the
    `noImplicitLambda` annotation; `have := e`, `by_cases`, and any
    `have h : T := …` whose `T` needed a coercion or a default
    instance leave hypothesis (and target) types as assigned-but-
    uninstantiated metavariables. Every structural match downstream
    — `getAppFnArgs`, `isConstOf`, `matchNatGoal?`, `matchLiaGoal?`,
    `fvarOfName` + `normalizeHypothesis` — then sees `?m` or `mdata`
    and falls through: the reifier threw "unsupported expression:
    <goal>" (obligations `D1/71`, `D3/98`, `D3/101`, `D3/175`,
    `D3/178`), or silently DROPPED the un-reifiable hypothesis so the
    solver answered sat (`D3/170`, `D3/180`), or the ℕ term-mode
    closer refused a goal the reifier had just read (`D1/69`). None
    of it is reachable from a probe whose goal is a declaration
    signature — which is exactly the "closes in isolation, fails in
    the file" context sensitivity the C4 handoff recorded as not
    understood.

    Mechanism, not workaround: `instantiateMVarDeclMVars` is Lean's
    own operation for exactly this (target + local context, in
    place, no proof-term change), and `consumeMData` removes only
    `Expr.mdata`, which carries no logical content — the goal is
    the SAME goal and `MVarId.setType` keeps the same metavariable,
    so an already-clean goal (every pre-existing test) is untouched
    byte for byte. SCOPE: metavariables anywhere in the target and
    context; the annotation at the TOP of the target only. A nested
    `mdata` inside a term, or one on a hypothesis type, is not
    stripped (none observed on the spike; the reifier's named error
    still reports the term). Pinned by the `pb_r4_ctx_*` tests in
    `Test/Tactic.lean`, each of which first asserts the raw shape is
    present (`raw_shape_test`) so the pin cannot pass vacuously. -/
private def normalizeGoalForBroker (goal : MVarId) : TacticM MVarId := do
  Lean.instantiateMVarDeclMVars goal
  let ty ← goal.getType
  let ty' := ty.consumeMData
  unless ty' == ty do goal.setType ty'
  return goal

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

/-- SMT-LIB §3.1 simple-symbol alphabet, mirrored from the SDK's
    `Smtlib.is_simple_symbol_tail_char`. ASCII only — Lean's
    `Char.isAlphanum` is ASCII, which is what we want here. -/
private def smtSymbolTailChar (c : Char) : Bool :=
  c.isAlphanum || "~!@$%^&*_-+=<>.?/".any (· == c)

/-- Reserved words the SDK refuses in identifier position
    (`Smtlib.smtlib_reserved`). -/
private def smtReservedWords : List String :=
  ["let", "forall", "exists", "match", "as", "par", "_",
   "Bool", "Int", "Real"]

/-- Does this name serialize as an SMT-LIB simple symbol? The SDK
    raises `bad_identifier` for anything else — quoted symbols are
    refused because they do not survive the proof-trace round trip. -/
private def smtSafeIdent (s : String) : Bool :=
  !s.isEmpty
  && smtSymbolTailChar s.front && !s.front.isDigit
  && s.all smtSymbolTailChar
  && !(smtReservedWords.contains s)

/-- Best-effort SMT-safe rewriting of a Lean name: every character
    outside the simple-symbol alphabet becomes `_`, a leading digit
    gets an `x` in front, and an empty/reserved result becomes
    `_pb_v`. Not required to be injective — the caller resolves
    collisions through the local context. -/
private def smtSanitizeIdent (s : String) : String :=
  let mapped := String.ofList (s.toList.map (fun c => if smtSymbolTailChar c then c else '_'))
  let mapped := if mapped.isEmpty then "_pb_v"
                else if mapped.front.isDigit then "x" ++ mapped
                else mapped
  if smtReservedWords.contains mapped then mapped ++ "_" else mapped

/-- R4.2: alpha-rename local hypotheses and variables whose names
    are not SMT-LIB simple symbols, BEFORE reification.

    Primed names are idiomatic Lean and pervasive in the verinf
    obligations (`threshold_unique`'s `c'`, `h1'`, `h2'`); the SDK
    serializer refuses them with
    `bad_identifier: c' … is not a SMT-LIB simple symbol; rename or
    alpha-convert before serialization`, so every such goal failed
    dispatch outright. Renaming on the GOAL rather than mapping
    names inside the IR is what keeps the rest of the pipeline
    honest: the reifier, the certificate, `fvarOfName` and the
    walker context all keep using one name for one thing, and no
    inverse map has to be trusted at lift time.

    Only the user-facing name changes — same fvar, same type, same
    proof term. Names already SMT-safe (which is nearly all of
    them) are untouched, so an unaffected goal reifies byte-for-byte
    as before. -/
private def renameLocalsForSmt (goal : MVarId) : TacticM MVarId := do
  let renames ← goal.withContext do
    let mut acc : Array (FVarId × String) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      unless smtSafeIdent decl.userName.toString do
        acc := acc.push (decl.fvarId, smtSanitizeIdent decl.userName.toString)
    pure acc
  if renames.isEmpty then return goal
  let mut g := goal
  for (fvarId, base) in renames do
    let fresh ← g.withContext do
      let cand := (← getLCtx).getUnusedName (Name.mkSimple base)
      -- `getUnusedName` disambiguates by appending an index; guard
      -- the result anyway rather than assume the shape of the
      -- suffix, and fall back to a synthetic name that cannot
      -- collide with a source identifier.
      if smtSafeIdent cand.toString then
        pure cand
      else
        pure ((← getLCtx).getUnusedName (Name.mkSimple "_pb_v"))
    g ← g.rename fvarId fresh
  replaceMainGoal [g]
  return g

@[tactic proofBroker]
def evalProofBroker : Tactic := fun stx => do
  let goal ← getMainGoal
  let goal ← normalizeGoalForBroker goal
  let goal ← introLeadingNatForalls goal
  let goal ← renameLocalsForSmt goal
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
  let goal ← normalizeGoalForBroker goal
  let goal ← introLeadingNatForalls goal
  let goal ← renameLocalsForSmt goal
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
  -- one the WALKER inverts (ℕ→ℤ via the cast layer; an α cert is
  -- refused here — the α replay is term-mode-only); otherwise the
  -- cert is refused, fail closed.
  let natMode := natModeOf path.ir
  checkCertSpecializations cert (walkerSpecMode path.ir)
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
  let goal ← normalizeGoalForBroker goal
  let goal ← introLeadingNatForalls goal
  let goal ← renameLocalsForSmt goal
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
  -- R4 continuation: term mode consumes a Tier 1 Farkas or Tier 2
  -- case-split witness and nothing else, so it SAYS so
  -- (`user_directives.tier_preference`, the walker's `["3"]` in the
  -- other direction). The SDK's parallel driver ranks those tiers
  -- first when picking the winner, and cvc5's ladder runs the
  -- internal Farkas closer before minting a Tier 3 trace. Without
  -- it, the verinf `D1/69` obligation under its full context got
  -- cvc5's verified Tier 3 trace as "the highest tier" while z3's
  -- Tier 1 witness — the one this closer needs — lost the race.
  let path ← buildExtractionPath goal adapterNames? preferHigherTier
    (tierPreference := some ["1", "2"])
  let cert ← match path.cert with
    | some c => pure c
    | none => throwError "proof_broker_term: no adapter minted a cert"
  -- Trace guard (R2, lifted for definition unfolding in R3-M3): the
  -- term-mode closers rebuild the proof from the cert's witness, so
  -- the trace must be identity OR consist solely of definition
  -- unfolds this extraction emitted the equations for — those are
  -- inverted below (`invertDefUnfolds`, Eq.mpr over `c = <numeral>`)
  -- so the witness addresses exactly what remains. Anything else is
  -- a named failure — term mode has no decision-procedure fallback
  -- by design.
  if let some msg := termTraceError? path then
    throwError msg
  let goal ← invertDefUnfolds goal path
  replaceMainGoal [goal]
  let goalType ← goal.getType
  unless path.verifyOk == some true do
    let r := path.verifyReason.map reprStr |>.getD "<unknown>"
    throwError "proof_broker_term: cert was minted but verifier did not \
                 accept it (reason: {r}); term-mode requires a verified \
                 Tier 1 Farkas or Tier 2 case-split cert"
  -- R3 specialization gate (fail closed; see
  -- `checkCertSpecializations`) + the lifts: a ℕ extraction's
  -- Tier-1 Farkas witness is consumed by `closeNatViaTermMode`,
  -- which casts the witness-named facts to ℤ by term construction
  -- and runs the Int fold over the images; an α extraction's is
  -- replayed AT α through the extension's class-polymorphic Farkas
  -- family (`polyFarkasCloser`) — the α→Int specialization was only
  -- for the solver (R3-M2).
  let natMode := natModeOf path.ir
  checkCertSpecializations cert (termSpecMode path.ir)
  if natMode then
    if certStrategyHint cert == "case_split_farkas" then
      throwError "proof_broker_term: Tier 2 case-split over a ℕ \
        extraction is not lifted yet"
    closeNatViaTermMode goal goalType cert path.ir path.natAtoms
    return
  if polyModeOf path.ir then
    if certStrategyHint cert == "case_split_farkas" then
      throwError "proof_broker_term: Tier 2 case-split over a \
        polymorphic-α extraction is not lifted yet"
    match ← reifierExt.get with
    | some ext => ext.polyFarkasCloser cert path.ir
    | none =>
      throwError "proof_broker_term: polymorphic-α cert minted but no \
        extension closer is registered (import `ProofBrokerMathlib` \
        for the class-polymorphic Farkas term builder)"
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
  let goal ← normalizeGoalForBroker goal
  let goal ← introLeadingNatForalls goal
  let goal ← renameLocalsForSmt goal
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

/-- TEST-ONLY tactic pinning the R3-M1 specialization gate
    (`checkCertSpecializations`) fail-closed, independent of any live
    dispatch — no live path today mints a foreign specialization or a
    spec-less ℕ cert, so without this the gate's throw branches would
    be exercised by nothing (C3a ROUND 1 finding 2, the C2 envelope-arm
    vacuity pattern). The tactic builds a synthetic cert carrying only
    the field the gate reads and runs the REAL gate:

    * `spec_gate_test nat nat_spec` — ℕ mode, exactly the Nat → Int
      record → gate passes, `trivial` closes the `True` goal.
    * `spec_gate_test int none` — non-ℕ, no records → passes.
    * `spec_gate_test nat none` — ℕ mode, record MISSING → the
      "records no Nat → Int type specialization" branch throws.
    * `spec_gate_test int foreign_spec` / `spec_gate_test nat
      foreign_spec` / `spec_gate_test nat mixed_spec` — a
      specialization this bridge cannot invert (alone, or riding next
      to a valid Nat → Int record) → the "cannot invert" branch
      throws. Deleting either throw branch flips the matching
      `fail_if_success` tests in `Test/Tactic.lean`.

    R3-M2 adds the `poly` mode (the term-mode path's α gate):
    * `spec_gate_test poly foreign_spec` — the alpha → Int record IS
      the invertible set in poly mode → passes.
    * `spec_gate_test poly none` — record missing → throws.
    * `spec_gate_test poly nat_spec` / `spec_gate_test poly beta_spec`
      — a record the α replay cannot invert → throws (`beta_spec` is
      foreign in every mode). -/
syntax (name := specGateTest) "spec_gate_test" ident ident : tactic

@[tactic specGateTest]
def evalSpecGateTest : Tactic := fun stx => do
  match stx with
  | `(tactic| spec_gate_test $mode $kind) =>
    let specMode ← match mode.getId.toString with
      | "nat" => pure SpecMode.nat
      | "int" => pure SpecMode.int
      | "poly" => pure SpecMode.poly
      | m => throwError "spec_gate_test: unknown mode '{m}' (nat | int | poly)"
    let natSpec := Json.mkObj [
      ("kind", "type_specialization"),
      ("source", "Nat"), ("target", "Int"),
      ("justification", "embeds_into:Int_for_universal_LIA"),
      ("soundness_witness", "Int.ofNat_le")]
    let foreignSpec := Json.mkObj [
      ("kind", "type_specialization"),
      ("source", "alpha"), ("target", "Int"),
      ("justification", "embeds_into:Int_for_universal_LIA"),
      ("soundness_witness", "linear_ordered_comm_ring_lia_embedding")]
    let betaSpec := Json.mkObj [
      ("kind", "type_specialization"),
      ("source", "beta"), ("target", "Real"),
      ("justification", "embeds_into:Real_for_universal_LRA"),
      ("soundness_witness", "linear_ordered_field_lra_embedding")]
    let specs : Json ← match kind.getId.toString with
      | "none" => pure (Json.arr #[])
      | "nat_spec" => pure (Json.arr #[natSpec])
      | "foreign_spec" => pure (Json.arr #[foreignSpec])
      | "mixed_spec" => pure (Json.arr #[natSpec, foreignSpec])
      | "beta_spec" => pure (Json.arr #[betaSpec])
      | k => throwError "spec_gate_test: unknown kind '{k}' \
          (none | nat_spec | foreign_spec | mixed_spec | beta_spec)"
    let cert := Json.mkObj [
      ("refinement_record", Json.mkObj [("specializations", specs)])]
    checkCertSpecializations cert specMode
    evalTactic (← `(tactic| trivial))
  | _ => throwError "spec_gate_test: malformed invocation"

/-- TEST-ONLY tactic: the CALL-SITE isolation pin (C4 ROUND 8
    Med 1; widened to all four fields at ROUND 9 Med 1 — the
    one-field version repeated the constructor pin's ROUND 5
    mistake, three lines below the comment warning about it). Runs
    the REAL `Reify.buildIRWithAcc` twice on the goal (which must
    reify at least one ℕ atom) and checks the two returned
    accumulators behave as distinct state:
    * run 1's atom table is non-empty and SURVIVES run 2 (the race
      bug's mechanism was a later reification's reset wiping an
      earlier one's table through shared state);
    * a marker pushed into EACH of run 2's four fields does not
      appear in run 1's corresponding field.
    HONEST SCOPE (ROUND 9): red under any spelling that leaves
    `buildIRWithAcc` returning the accumulator it accumulated into
    — which every single-accumulator mutation does. A DECOY mutant
    (accumulate in shared state, return a copied accumulator) evades
    any return-value pin by construction; that residual is covered
    only by the source gate and review, and is stated in delta §5.7
    rather than papered over. -/
syntax (name := reifyCallsiteIsolationTest)
  "reify_callsite_isolation_test" : tactic

@[tactic reifyCallsiteIsolationTest]
def evalReifyCallsiteIsolationTest : Tactic := fun stx => do
  match stx with
  | `(tactic| reify_callsite_isolation_test) =>
    let g ← getMainGoal
    let (_, acc1) ← Reify.buildIRWithAcc g
    let n1 := (← acc1.natAtoms.get).size
    unless n1 > 0 do
      throwError "reify_callsite_isolation_test: the goal reified no \
        ℕ atom — use a goal with a nonlinear ℕ product so aliasing \
        is observable"
    let (_, acc2) ← Reify.buildIRWithAcc g
    unless (← acc1.natAtoms.get).size == n1 do
      throwError "reify_callsite_isolation_test: run 2 WIPED run 1's \
        atom table (size {(← acc1.natAtoms.get).size}, was {n1}) — \
        buildIR is accumulating in shared state (the C4 ROUND 3 race \
        mechanism)"
    -- per-field aliasing markers (ROUND 9 Med 1: natDefs-only
    -- re-sharing was green under a natAtoms-only marker)
    acc2.consts.modify (·.push ("_pb_cs_marker", "Int"))
    acc2.natAtoms.modify (·.push ("_pb_cs_marker", Lean.mkConst ``Nat))
    acc2.intAtoms.modify (·.push ("_pb_cs_marker", Lean.mkConst ``Int))
    acc2.natDefs.modify (·.push ("_pb_cs_marker", Lean.mkConst ``Nat, 0))
    if (← acc1.consts.get).any (·.1 == "_pb_cs_marker") then
      throwError "reify_callsite_isolation_test: consts ALIASED \
        across the two reifications"
    if (← acc1.natAtoms.get).any (·.1 == "_pb_cs_marker") then
      throwError "reify_callsite_isolation_test: natAtoms ALIASED \
        across the two reifications"
    if (← acc1.intAtoms.get).any (·.1 == "_pb_cs_marker") then
      throwError "reify_callsite_isolation_test: intAtoms ALIASED \
        across the two reifications"
    if (← acc1.natDefs.get).any (·.1 == "_pb_cs_marker") then
      throwError "reify_callsite_isolation_test: natDefs ALIASED \
        across the two reifications"
    evalTactic (← `(tactic| omega))
  | _ => throwError "reify_callsite_isolation_test: malformed invocation"

/-- TEST-ONLY tactic: the runtime half of the per-call accumulator
    fix's pin (C4 ROUND 4 finding 1; field coverage widened at
    ROUND 5 Med 1; SCOPE stated honestly at ROUND 6 Med 1). Calls
    `ReifyAcc.fresh` twice, pushes a marker into EACH of the first
    accumulator's four fields, and asserts per field that the second
    is empty and the first kept its entry. This pins the
    CONSTRUCTOR: any re-sharing inside `ReifyAcc.fresh` is red on
    every run, no parallelism required. It does NOT see a mutation
    that leaves `fresh` intact and moves accumulation back to
    module refs cleared at the `buildIR` call site — that direction
    is pinned by `reify_callsite_isolation_test` (aliasing-based;
    red whenever the reification returns the accumulator it
    accumulated into — the load-bearing pin since ROUND 8) with
    `tools/check.py`'s `check_lean_reify_isolation` source gate as
    defense in depth.
    The stress herd exercises concurrency but is not a catcher —
    measured pre-fix rates 0/30 (anonymous form, ROUND 4), 0/20
    (all-four-shared mutation) and 0/10 (natDefs-only mutation),
    both on the named-theorem form at ROUND 5. -/
syntax (name := reifyAccIsolationTest) "reify_acc_isolation_test" : tactic

@[tactic reifyAccIsolationTest]
def evalReifyAccIsolationTest : Tactic := fun stx => do
  match stx with
  | `(tactic| reify_acc_isolation_test) =>
    -- ALL FOUR fields, independently (C4 ROUND 5 Med 1: asserting
    -- only natAtoms let a natDefs-only re-sharing — the exact table
    -- whose loss produced the demo's `unsupported_symbol` — escape
    -- every pin in the tree).
    let a ← ReifyAcc.fresh
    a.consts.modify (·.push ("_pb_iso_c", "Int"))
    a.natAtoms.modify (·.push ("_pb_iso_na", Lean.mkConst ``Nat))
    a.intAtoms.modify (·.push ("_pb_iso_ia", Lean.mkConst ``Int))
    a.natDefs.modify (·.push ("_pb_iso_nd", Lean.mkConst ``Nat, 0))
    let b ← ReifyAcc.fresh
    let checkEmpty (name : String) (n : Nat) : TacticM Unit := do
      unless n == 0 do
        throwError "reify_acc_isolation_test: a fresh accumulator's \
          {name} is NOT empty ({n} entries) — ReifyAcc.fresh is \
          sharing state"
    checkEmpty "consts" (← b.consts.get).size
    checkEmpty "natAtoms" (← b.natAtoms.get).size
    checkEmpty "intAtoms" (← b.intAtoms.get).size
    checkEmpty "natDefs" (← b.natDefs.get).size
    let checkKept (name : String) (n : Nat) : TacticM Unit := do
      unless n == 1 do
        throwError "reify_acc_isolation_test: the first accumulator's \
          {name} lost its entry (size {n}) — a later fresh cleared \
          shared refs"
    checkKept "consts" (← a.consts.get).size
    checkKept "natAtoms" (← a.natAtoms.get).size
    checkKept "intAtoms" (← a.intAtoms.get).size
    checkKept "natDefs" (← a.natDefs.get).size
    evalTactic (← `(tactic| trivial))
  | _ => throwError "reify_acc_isolation_test: malformed invocation"

/-- TEST-ONLY tactic pinning `constOnlyInValuePositions` in BOTH
    directions, deterministically (C4 ROUND 3 Med 1: the end-to-end
    `PBModP` negative proved vacuous — it fails under any closer
    outcome, so `gate ≡ true` left every build green). For the named
    constant `c`, builds the two canonical shapes and asserts the
    gate's verdicts directly:
    * value position, `c + 1` — must be ALLOWED (true);
    * type position, `@id (Fin c)` — the constant inside an argument
      whose own type is a Sort — must be REFUSED (false).
    Mutating the gate in either direction turns exactly this red. -/
syntax (name := typePosGateTest) "type_pos_gate_test" ident : tactic

@[tactic typePosGateTest]
def evalTypePosGateTest : Tactic := fun stx => do
  match stx with
  | `(tactic| type_pos_gate_test $c) =>
    let cName ← Lean.resolveGlobalConstNoOverload c
    let cE := Lean.mkConst cName
    let valuePos ← Lean.Meta.mkAppM ``HAdd.hAdd #[cE, Lean.mkNatLit 1]
    let typePos :=
      Lean.mkApp (Lean.mkConst ``id [Lean.levelOne])
        (Lean.mkApp (Lean.mkConst ``Fin) cE)
    unless ← constOnlyInValuePositions cName valuePos do
      throwError "type_pos_gate_test: the gate REFUSED a pure value \
        position ({valuePos}) — the permissive branch broke"
    if ← constOnlyInValuePositions cName typePos then
      throwError "type_pos_gate_test: the gate ALLOWED a type \
        position ({typePos}) — the refusing branch broke"
    evalTactic (← `(tactic| trivial))
  | _ => throwError "type_pos_gate_test: malformed invocation"

/-- TEST-ONLY tactic: assert the RAW shape of the main goal or of a
    named hypothesis — the shape `normalizeGoalForBroker` exists to
    remove — so the `pb_r4_ctx_*` tests are not vacuous: a test that
    merely closes a goal would also pass on a toolchain that no
    longer produces the shape, and would then pin nothing.
    * `raw_shape_test goal_mdata` — the target, read WITHOUT
      instantiation, is an `Expr.mdata` node (the `have` tactic's
      `noImplicitLambda` annotation on its continuation goal).
    * `raw_shape_test goal_mvar` — the raw target contains an
      assigned expression metavariable.
    * `raw_shape_test hyp_mvar h` — the raw type of local `h`
      contains an assigned expression metavariable (`have := e`,
      `by_cases`, a coercion-bearing `have` type).
    Fails with a named message when the shape is ABSENT, which is
    the signal that a toolchain change made the pin moot. Leaves the
    goal untouched. -/
syntax (name := rawShapeTest) "raw_shape_test" ident (colGt ident)? : tactic

@[tactic rawShapeTest]
def evalRawShapeTest : Tactic := fun stx => do
  match stx with
  | `(tactic| raw_shape_test $kind $[$hyp?]?) =>
    let goal ← getMainGoal
    goal.withContext do
      let raw ← goal.getType
      match kind.getId.toString, hyp? with
      | "goal_mdata", none =>
        unless raw.isMData do
          throwError "raw_shape_test: the raw target is not an mdata \
            node (ctor {raw.ctorName}) — the shape this test pins is \
            absent; re-derive the pin against this toolchain"
      | "goal_mvar", none =>
        unless raw.hasExprMVar do
          throwError "raw_shape_test: the raw target has no expression \
            metavariable — the shape this test pins is absent; \
            re-derive the pin against this toolchain"
      | "hyp_mvar", some h =>
        let some decl := (← getLCtx).findFromUserName? h.getId
          | throwError "raw_shape_test: no local named {h.getId}"
        unless decl.type.hasExprMVar do
          throwError "raw_shape_test: the raw type of {h.getId} has no \
            expression metavariable (ctor {decl.type.ctorName}) — the \
            shape this test pins is absent; re-derive the pin against \
            this toolchain"
      | k, _ =>
        throwError "raw_shape_test: unknown shape '{k}' (goal_mdata | \
          goal_mvar | hyp_mvar <h>)"
  | _ => throwError "raw_shape_test: malformed invocation"

/-- TEST-ONLY tactic: run the REAL `Reify.buildIR` on the main goal
    — NOT through a tactic front-end, so `normalizeGoalForBroker`
    has not run — and assert that exactly `n` hypotheses were
    reified and NONE was skipped. This pins the reifier's own
    per-hypothesis instantiation (`buildIRWithAcc`) independently of
    the front-end normalization: with it reverted, a `have := e` or
    `by_cases` hypothesis reifies as `?m`, is dropped into
    `skippedLocals`, and the count is one short. Leaves the goal
    untouched. -/
syntax (name := reifyHypCountTest) "reify_hyp_count_test" num : tactic

@[tactic reifyHypCountTest]
def evalReifyHypCountTest : Tactic := fun stx => do
  match stx with
  | `(tactic| reify_hyp_count_test $n) =>
    let (ir, _atoms, _defs, skipped) ← Reify.buildIR (← getMainGoal)
    unless skipped.isEmpty do
      throwError "reify_hyp_count_test: buildIR SKIPPED {skipped.size} \
        local(s): {skipped.map (fun (nm, why) => s!"{nm}: {why}")} — a \
        hypothesis that closes this goal was dropped as outside the \
        fragment"
    let got := ir.context.hypotheses.length
    unless got == n.getNat do
      throwError "reify_hyp_count_test: expected {n.getNat} reified \
        hypothesis(es), got {got} ({ir.context.hypotheses.map (·.name)})"
  | _ => throwError "reify_hyp_count_test: malformed invocation"

/-- TEST-ONLY tactic used by the `Test/TacticStress.lean` herd:
    runs the REAL `Reify.buildIR` on the goal — no dispatch, no
    solver — and asserts the returned atom and numeral-def tables
    have exactly the expected sizes. HONEST ROLE (C4 ROUND 4
    finding 1): the herd EXERCISES concurrent per-call accumulators
    under v4.32's async elaboration of named theorems; it is NOT a
    reliable regression catcher — measured pre-fix catch rates: 0/30
    builds on the ROUND 4 anonymous-example form; on THIS
    named-theorem form (ROUND 5) 0/20 under the all-four-shared
    mutation and 0/10 under the natDefs-only one;
    a dispatch-free `buildIR` window is ~1.5 ms (the demo file
    raced because its windows span live solver round trips). The
    fix's pin is three-part: `reify_callsite_isolation_test`
    (load-bearing, aliasing-based; scope and residual in delta §5.7),
    `reify_acc_isolation_test` (the constructor), and
    `check_lean_reify_isolation` in `tools/check.py` (source-level
    defense in depth). -/
syntax (name := reifyStressTest) "reify_stress_test" num num : tactic

@[tactic reifyStressTest]
def evalReifyStressTest : Tactic := fun stx => do
  match stx with
  | `(tactic| reify_stress_test $nAtoms $nDefs) =>
    let (_ir, atoms, defs, _skippedLocals) ← Reify.buildIR (← getMainGoal)
    unless atoms.size == nAtoms.getNat do
      throwError "reify_stress_test: expected {nAtoms.getNat} ℕ \
        atom(s), got {atoms.size} ({atoms.map (·.1)}) — cross-goal \
        table contamination"
    unless defs.size == nDefs.getNat do
      throwError "reify_stress_test: expected {nDefs.getNat} numeral \
        def(s), got {defs.size} ({defs.map (·.1)}) — cross-goal \
        table contamination"
  | _ => throwError "reify_stress_test: malformed invocation"

/-- TEST-ONLY tactic pinning the R3-M3 term-mode trace guard
    (`termTraceError?`) branch by branch, independent of live
    dispatch — the live paths only ever produce identity traces or
    our own numeral-def unfolds, so without this the guard's refusal
    branches would be exercised by nothing (the C3a finding-2
    pattern). Builds a synthetic `ExtractionPath` whose `natDefs`
    table knows exactly one definition (`ProofBroker.Test.P`) and a
    synthetic trace per kind:

    * `identity` — identity trace → guard passes.
    * `def_unfold_ours` — applied definition_unfolding of the known
      symbol → guard passes (the inversion path's admission).
    * `def_unfold_foreign` — applied unfold of a symbol the
      extraction did not emit → named error.
    * `def_unfold_empty` — applied unfold naming NO symbols (absent/
      malformed/empty `inversion_data`) → named error, not a vacuous
      pass.
    * `prop_simp_applied` — an applied pass with no inversion →
      named error.
    * `failed_pass` — a Failed definition_unfolding entry → named
      error (only APPLIED unfolds are admitted).
    * `endpoints_no_entries` — endpoint hashes disagree, EMPTY entry
      list → named error (no entry admits the rewrite).
    * `endpoints_all_noop` — endpoint hashes disagree, every entry
      identity-shaped → named error (same: admission must mean an
      inversion ran).
    * `no_trace` — no trace on the path → named error. -/
syntax (name := traceGuardTest) "trace_guard_test" ident : tactic

@[tactic traceGuardTest]
def evalTraceGuardTest : Tactic := fun stx => do
  match stx with
  | `(tactic| trace_guard_test $kind) =>
    let mkEntry (pass : String) (outcome : Trace.Outcome)
        (syms : List String) : Trace.Entry := {
      pass, version := "1.0",
      beforeHash := "sha256:aa", afterHash := "sha256:bb",
      configuration := none, outcome := some outcome,
      inversionData := some (Json.mkObj [
        ("unfolded_symbols", Json.arr (syms.toArray.map (fun s =>
          Json.mkObj [("symbol", Json.str s)])))]),
      diagnostics := none }
    let identityDoc : Trace.Document := {
      traceVersion := "1.0", initialIrHash := "sha256:aa",
      finalIrHash := "sha256:aa", entries := [], configuration := none }
    let nonIdentityDoc (e : Trace.Entry) : Trace.Document := {
      traceVersion := "1.0", initialIrHash := "sha256:aa",
      finalIrHash := "sha256:bb", entries := [e], configuration := none }
    let endpointsNoEntriesDoc : Trace.Document := {
      traceVersion := "1.0", initialIrHash := "sha256:aa",
      finalIrHash := "sha256:bb", entries := [], configuration := none }
    let noopEntry : Trace.Entry := {
      pass := "propositional_simplification", version := "1.0",
      beforeHash := "sha256:aa", afterHash := "sha256:aa",
      configuration := none, outcome := some .noOp,
      inversionData := none, diagnostics := none }
    let endpointsAllNoopDoc : Trace.Document := {
      traceVersion := "1.0", initialIrHash := "sha256:aa",
      finalIrHash := "sha256:bb", entries := [noopEntry],
      configuration := none }
    let ourDef := "ProofBroker.Test.P"
    let trace? : Option Trace.Document ← match kind.getId.toString with
      | "identity" => pure (some identityDoc)
      | "def_unfold_ours" =>
        pure (some (nonIdentityDoc
          (mkEntry "definition_unfolding" .applied [ourDef])))
      | "def_unfold_foreign" =>
        pure (some (nonIdentityDoc
          (mkEntry "definition_unfolding" .applied ["Foreign.Q"])))
      | "def_unfold_empty" =>
        pure (some (nonIdentityDoc
          (mkEntry "definition_unfolding" .applied [])))
      | "prop_simp_applied" =>
        pure (some (nonIdentityDoc
          (mkEntry "propositional_simplification" .applied [])))
      | "failed_pass" =>
        pure (some (nonIdentityDoc
          (mkEntry "definition_unfolding" .failed [ourDef])))
      | "endpoints_no_entries" => pure (some endpointsNoEntriesDoc)
      | "endpoints_all_noop" => pure (some endpointsAllNoopDoc)
      | "no_trace" => pure none
      | k => throwError "trace_guard_test: unknown kind '{k}'"
    let dummyIr : IR := {
      irVersion := "1.0",
      sourceSystem := { name := "lean", version := "0.0" },
      tier := "structural",
      logicClassification := {
        order := "first_order", featuresUsed := [],
        firstOrderFragment := "LIA", decidableTheory := none },
      goal := { shell := .const "False", payloads := none },
      context := { typeVars := [], freeVars := [],
                   hypotheses := [], librarySlice := none },
      typeMetadata := [], definitionalMetadata := [],
      libraryProvenance := [], userDirectives := none }
    let path : ExtractionPath := {
      ir := dummyIr, attempts := [], cert := none, trace := trace?,
      finalIr := none,
      natDefs := #[(ourDef, mkConst `x, 42)],
      verifyOk := none, verifyEnvelopeOk := none, verifyReason := none,
      dispatchMs := 0, verifyMs := 0 }
    match termTraceError? path with
    | some msg => throwError msg
    | none => evalTactic (← `(tactic| trivial))
  | _ => throwError "trace_guard_test: malformed invocation"

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

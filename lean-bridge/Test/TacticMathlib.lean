/-
End-to-end tactic-elaboration tests for `proof_broker` over LRA.

Importing `ProofBrokerMathlib` registers the Real reifier +
linarith closer. With that registration, `proof_broker` accepts
LRA goals (Real-typed inequalities), reifies them, dispatches to
the broker (cvc5/z3 with their LRA-capable adapters), re-verifies
the cert, and closes with `linarith` — axiom-free under
cert-gating, same contract as `omega` for LIA.

Build success of this lib is the test.

Pre-condition: cwd = `lean-bridge/` (manifest loader points at
`../examples/`); `opam exec -- dune build` (run from repo root)
populated the FFI .so.
-/

import ProofBrokerMathlib
-- R4.2: the verinf bracket-spike shapes at the end of this file
-- need ZMod; `ProofBrokerMathlib` itself pulls in only the Real
-- / order-instance corner of Mathlib it needs.
import Mathlib.Data.ZMod.Basic

set_option linter.unusedVariables false

namespace ProofBroker.TestMathlib

/-- Two-hypothesis LRA Farkas: `x ≥ 5 ∧ x ≤ 3 ⊢ False`. The
    broker mints a Tier 1 farkas cert (z3 native, or cvc5-Tier 3,
    depending on which adapter wins under preferHigherTier);
    `linarith` discharges. -/
example (x : Real) (h1 : x ≥ 5) (h2 : x ≤ 3) : False := by
  proof_broker

/-- Bound transfer over Real. -/
example (x : Real) (h : x ≤ 3) : x ≤ 5 := by
  proof_broker

/-- Sum-bound: x + y ≤ 10, y ≥ 0 ⊢ x ≤ 10. -/
example (x y : Real) (h1 : x + y ≤ 10) (h2 : y ≥ 0) : x ≤ 10 := by
  proof_broker

/-- Named LRA goal so `#print axioms` can confirm the footprint
    stays within the core ceiling — the linarith closer is
    axiom-free same as omega's. -/
theorem lra_axiom_free
    (x : Real) (h1 : x ≥ 5) (h2 : x ≤ 3) : False := by
  proof_broker

#print axioms lra_axiom_free

/-- Term-mode Tier 2 case-split over LRA: a goal with a
    disjunctive hypothesis `(x ≤ 0) ∨ (x ≥ 10)` under
    `1 ≤ x ≤ 9` closes by destruct + per-branch Farkas. cvc5
    mints a Tier 2 `case_split_farkas` cert (adapter priority
    prefers case-split over Tier 3 alethe when the IR has a
    disjunctive hypothesis). The bridge closer destructs the
    disjunction in the Lean LCtx and applies the matching
    lemma's Tier 1 Farkas witness per branch via
    `rFarkasContradict`. No `linarith` call on the per-branch
    arithmetic — only on the narrow strict-positivity
    polynomial-identity subgoal, same role `omega` plays in
    the Int term-mode closer. Trust footprint matches the
    existing `lra_axiom_free`: `[propext, Classical.choice,
    Quot.sound]` (the Mathlib LRA baseline). Mirror of Rocq's
    `pb_term_case_split_axiom_free`. -/
theorem pb_term_case_split_axiom_free
    (x : Real) (h_disj : x ≤ 0 ∨ x ≥ 10) (h_low : x ≥ 1) (h_high : x ≤ 9)
    : False := by
  proof_broker_term [cvc5]

#print axioms pb_term_case_split_axiom_free

/- ============================================================
   Tier 1 LRA term-mode test suite. Mirrors Rocq's `pb_lra_term_*`
   suite end-to-end on the Lean Mathlib side. Each test pins through
   `[z3]` (z3 mints native Tier 1 Farkas for LRA; cvc5 prefers Tier 3
   alethe-2024 which the term builder doesn't consume).

   Trust footprint for all of these is the standard Mathlib LRA
   baseline `[propext, Classical.choice, Quot.sound]` — same as the
   `linarith`-based closer in `lra_axiom_free` and the Tier 2
   case-split closer above.
   ============================================================ -/

/-- LRA Tier 1 Farkas False-goal, arity-2: `5 ≤ x ∧ x ≤ 3 ⊢ False`.
    Mirror of Rocq's `pb_lra_axiom_free` but via the new Mathlib
    term-mode dispatcher (routed via `tier1FarkasCloser` instead of
    the `linarith` fallback). -/
theorem pb_lra_term_axiom_free
    (x : Real) (h1 : 5 ≤ x) (h2 : x ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_lra_term_axiom_free

/-- LRA Tier 1 Farkas False-goal, arity-3: transitive chain. -/
theorem pb_lra_term_arity3_axiom_free
    (x y : Real) (h1 : 5 ≤ x) (h2 : x ≤ y) (h3 : y ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_lra_term_arity3_axiom_free

/-- Strict-only False-goal: `5 < x ∧ x < 5 ⊢ False`. Linear sum
    collapses to zero; strictness from both premises carries the
    contradiction via `rFarkasContradictNStrict`. -/
theorem pb_lra_term_lt_hyp_axiom_free
    (x : Real) (h1 : 5 < x) (h2 : x < 5) : False := by
  proof_broker_term [z3]

#print axioms pb_lra_term_lt_hyp_axiom_free

/-- Mixed strict + non-strict, arity-3: `1 ≤ x ∧ x ≤ y ∧ y < 1 ⊢ False`.
    Fold sees (Le, Le, Lt) — strictness from the final Lt premise
    threads through via `rAddLeLt` after the Le-Le accumulation. -/
theorem pb_lra_term_lt_mixed_axiom_free
    (x y : Real) (h1 : 1 ≤ x) (h2 : x ≤ y) (h3 : y < 1) : False := by
  proof_broker_term [z3]

#print axioms pb_lra_term_lt_mixed_axiom_free

/-- LRA comparison goal `(≤)`: `(h : n ≤ 5) ⊢ n ≤ 6`. The closer
    routes through `rLeViaLt` and the strict-aware fold (the
    neg_goal's Lt-shape over R is what produces the strict sum). -/
theorem pb_lra_term_goal_axiom_free
    (n : Real) (h : n ≤ 5) : n ≤ 6 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_goal_axiom_free

/-- LRA comparison goal `(<)`: `(h : n ≤ 4) ⊢ n < 5`. The neg_goal
    `¬(n < 5) ≡ 5 ≤ n` compiles as Le over R, so the closer routes
    through `rLtViaLe` and the standard non-strict fold (K > 0). -/
theorem pb_lra_term_lt_axiom_free
    (n : Real) (h : n ≤ 4) : n < 5 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_lt_axiom_free

/-- LRA comparison goal `(≥)`: `(h : 5 ≤ n) ⊢ n ≥ 4`. Lean's
    instance reduction unifies the proof of `4 ≤ n` (built via the
    `rLeViaLt` wrapper) with the `n ≥ 4` goal, so no explicit
    `Rle_ge`-style normalization tactic is needed (Rocq does need
    it because Z.ge / R.ge don't reduce). -/
theorem pb_lra_term_ge_axiom_free
    (n : Real) (h : 5 ≤ n) : n ≥ 4 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_ge_axiom_free

/-- LRA comparison goal `(>)`: `(h : 5 ≤ n) ⊢ n > 3`. Same instance
    reduction trick as `≥`, routes through `rLtViaLe`. -/
theorem pb_lra_term_gt_axiom_free
    (n : Real) (h : 5 ≤ n) : n > 3 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_gt_axiom_free

/-- LRA equality goal: `(h1 : n ≤ 5) (h2 : 5 ≤ n) ⊢ n = 5`. Core's
    `evalProofBrokerTerm` detects the Real-typed Eq via the
    extension's `reifyType`, applies `le_antisymm` (Mathlib's
    generic version, not `Int.le_antisymm`), and recurses on each
    direction. The trivial-K=0 case for each direction routes
    through `rLeViaLt` and the strict-aware fold. Mirror of Rocq's
    `pb_lra_term_eq_axiom_free`. -/
theorem pb_lra_term_eq_axiom_free
    (n : Real) (h1 : n ≤ 5) (h2 : 5 ≤ n) : n = 5 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_eq_axiom_free

/-- Arity-3 comparison goal (LRA, Le): transitive chain
    `x ≤ y ∧ y ≤ 5 ⊢ x ≤ 6`. Mirrors `pb_term_arity3_goal_axiom_free`
    over Real. The unified closer applies `rLeViaLt`, introduces
    `neg_goal : 6 < x` (strict over Real), and feeds the arity-3
    witness through the strict-aware False-fold. Strictness from
    the Lt-shaped neg_goal entry threads through via `rAddLeLt` at
    the final fold step. -/
theorem pb_lra_term_arity3_goal_axiom_free
    (x y : Real) (h1 : x ≤ y) (h2 : y ≤ 5) : x ≤ 6 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_arity3_goal_axiom_free

/-- Arity-3 comparison goal (LRA, Lt): strict goal from a Le-chain.
    Wrapper is `rLtViaLe`, neg_goal compiles as Le (Real has no
    +1 trick; `c ≤ b` is the natural negation of `b < c`). All
    entries Le, fold stays in the non-strict path until contradicting
    `0 < sum` via `rFarkasContradictN`. -/
theorem pb_lra_term_arity3_lt_axiom_free
    (x y : Real) (h1 : x ≤ y) (h2 : y ≤ 4) : x < 5 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_arity3_lt_axiom_free

/-- Strict-`<` hypothesis on a Le-goal: `(h : 0 < x) ⊢ 0 ≤ x`. The
    unified strict-aware fold consumes the Lt-normalized `h` directly
    (`rLtToLt0 → a - b < 0`) and combines it with the neg_goal's
    Lt-shape; no weakening required. -/
theorem pb_lra_term_le_goal_strict_a1_axiom_free
    (x : Real) (h : 0 < x) : 0 ≤ x := by
  proof_broker_term [z3]

#print axioms pb_lra_term_le_goal_strict_a1_axiom_free

/-- Strict-`<` hypothesis on a Lt-goal: `(h : 0 < x) ⊢ 0 < x`. Linear
    sum is exactly zero; strictness flows through `a1` via the
    strict-aware fold (`rMulPosNeg` on the strict premise → `rAddLtLe`
    on the neg_goal accumulator), letting `rFarkasContradictNStrict`
    close with `0 ≤ K` (K = 0 permitted because strictness on the sum
    carries the contradiction). -/
theorem pb_lra_term_lt_goal_strict_a1_axiom_free
    (x : Real) (h : 0 < x) : 0 < x := by
  proof_broker_term [z3]

#print axioms pb_lra_term_lt_goal_strict_a1_axiom_free

/-- Strict-`<` hypothesis on a Ge-goal: `(h : 0 < x) ⊢ x ≥ 0`. Same
    proof shape as the Le-goal variant via Lean's `≥` instance
    reduction. -/
theorem pb_lra_term_ge_goal_strict_a1_axiom_free
    (x : Real) (h : 0 < x) : x ≥ 0 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_ge_goal_strict_a1_axiom_free

/-- Strict-`<` hypothesis on a Gt-goal: `(h : 0 < x) ⊢ x > 0`. Same
    as the Lt-goal variant via instance reduction; the strict-aware
    fold carries the strictness on the trivial-K=0 sum. -/
theorem pb_lra_term_gt_goal_strict_a1_axiom_free
    (x : Real) (h : 0 < x) : x > 0 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_gt_goal_strict_a1_axiom_free

/-- LRA Farkas with leading-coefficient hypotheses, exercising the
    parser's rational-coefficient path end-to-end. Goal:
    `2*x ≤ 1 ∧ x ≥ 1 ⊢ False`. The Farkas combination cancels `x`
    with `c1=1, c2=2` (or any positive rational scale of this
    ratio); whatever the solver emits, the unified parser routes
    through `parseRatStringReal` + `clearDenominatorsReal` to
    integer coefficients before the closer builds the proof term.

    This is a regression test for the rational widening: solvers
    that normalize Farkas coefficients internally still produce
    `1/1`-style rationals in some emitter formats (cvc5's
    `:la_generic :args (1/1 1/1 1/1)`), so the closer must accept
    them. Even when scaled coefficients are integers, the path
    exercises the LCD = 1 short-circuit of clearDenominators. -/
theorem pb_lra_term_rational_axiom_free
    (x : Real) (h1 : 2 * x ≤ 1) (h2 : x ≥ 1) : False := by
  proof_broker_term [z3]

#print axioms pb_lra_term_rational_axiom_free

/-- Eq hypothesis in the witness (Real): mirror of Int's
    `pb_term_eq_hyp_axiom_free`. The solver-emitted cert combines
    `h1 : x = 5` with `h2 : x ≤ 3` to derive `False`; the Eq hyp
    flows through `rEqToLe0` / `rEqToLe0Flipped` depending on the
    coefficient sign. -/
theorem pb_lra_term_eq_hyp_axiom_free
    (x : Real) (h1 : x = 5) (h2 : x ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_lra_term_eq_hyp_axiom_free

/-- Not-hypothesis in the witness (Real): mirror of Int's
    `pb_term_not_hyp_axiom_free`. `¬(x ≤ 5)` over Real compiles to
    the strict `5 < x` (no +1 trick — R doesn't have a discrete
    domain). The closer's strict-aware fold threads this strictness
    through via `rNotLeToLt0` + `rMulPosNeg` / `rAddLtLe`. -/
theorem pb_lra_term_not_hyp_axiom_free
    (x : Real) (h1 : ¬(x ≤ 5)) (h2 : x ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_lra_term_not_hyp_axiom_free

/- ============================================================
   R3-M2: polymorphic α — spec Example 1 as written.

   A goal over a type variable `α` with the ordered-comm-ring
   instances (modern Mathlib spelling `[CommRing α] [LinearOrder α]
   [IsStrictOrderedRing α]`; the roadmap's `LinearOrderedCommRing`
   was removed by Mathlib's 2025 refactor — delta.md §5) reifies
   with `type_variable` metadata + real embedding witnesses, the
   SDK refinement substitutes alpha → Int for the SOLVER only, and
   the term-mode closer replays the cert's Farkas coefficients AT α
   through `ProofBrokerMathlib.TermModePoly` — the inversion of the
   recorded α→Int specialization. Tests pin `[z3]` (native Tier-1
   Farkas; cvc5 prefers Tier-3 alethe, which no α closer consumes —
   same convention as the LRA suite above).
   ============================================================ -/

/-- THE M2 gate: `examples/example1-lia-typeclass.json`'s goal,
    stated in Lean with a type variable, closes `by
    proof_broker_term`; the cert carries the alpha → Int
    `type_specialization` with the class-instance witness (the
    spec gate requires it — a spec-less cert is refused), and the
    footprint stays within Mathlib's classical baseline. -/
theorem pb_poly_example1 {α : Type} [CommRing α] [LinearOrder α]
    [IsStrictOrderedRing α]
    (n m : α) (h1 : n + m = 10) (h2 : 0 ≤ n) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker_term [z3]

#print axioms pb_poly_example1

/-- α False-goal, arity-2. -/
theorem pb_poly_term_false {α : Type} [CommRing α] [LinearOrder α]
    [IsStrictOrderedRing α]
    (x : α) (h1 : 5 ≤ x) (h2 : x ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_poly_term_false

/-- Strict hypothesis on a strict goal: the linear sum is exactly
    zero and strictness alone carries the contradiction through the
    strict-aware fold (`pFarkasContradictNStrict`, K = 0). -/
theorem pb_poly_term_strict {α : Type} [CommRing α] [LinearOrder α]
    [IsStrictOrderedRing α]
    (x : α) (h : 0 < x) : 0 < x := by
  proof_broker_term [z3]

#print axioms pb_poly_term_strict

/-- α equality goal: split via the generic `le_antisymm`
    (`tier1EqSplit` applies at any qualified α), each direction a
    fresh dispatch + α replay. -/
theorem pb_poly_term_eq {α : Type} [CommRing α] [LinearOrder α]
    [IsStrictOrderedRing α]
    (n : α) (h1 : n ≤ 5) (h2 : 5 ≤ n) : n = 5 := by
  proof_broker_term [z3]

#print axioms pb_poly_term_eq

/-- Eq hypothesis with a signed coefficient in the witness
    (`pEqToLe0` / `pEqToLe0Flipped`). -/
theorem pb_poly_term_eq_hyp {α : Type} [CommRing α] [LinearOrder α]
    [IsStrictOrderedRing α]
    (x : α) (h1 : x = 5) (h2 : x ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_poly_term_eq_hyp

/-- Literal-coefficient multiplication (`2 * x`) rides through the
    fold; coefficients arrive rational-normalized like on the LRA
    path. -/
theorem pb_poly_term_mul {α : Type} [CommRing α] [LinearOrder α]
    [IsStrictOrderedRing α]
    (x : α) (h1 : 2 * x ≤ 1) (h2 : 1 ≤ x) : False := by
  proof_broker_term [z3]

#print axioms pb_poly_term_mul

/-- Plain `proof_broker` on an α goal: omega is Int/ℕ-only, so the
    LIA arm's α branch replays the Tier-1 witness through the same
    poly closer (cert-consuming even in plain mode). -/
theorem pb_poly_plain {α : Type} [CommRing α] [LinearOrder α]
    [IsStrictOrderedRing α]
    (n m : α) (h1 : n + m = 10) (h2 : 0 ≤ n) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker [z3]

#print axioms pb_poly_plain

/-- R2 trace guard on the plain α route: the replay consumes the
    cert, so a NON-IDENTITY trace is a named refusal exactly as in
    term mode. The `True ∧ _` hypothesis makes the pipeline's
    prop-simp pass apply (the trace records a real rewrite), so
    plain `proof_broker` must refuse rather than replay a cert
    minted on the rewritten IR; the goal then closes honestly from
    the hypothesis the pipeline never touched. -/
example {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (n : α) (h : True ∧ n ≤ 7) (h2 : n ≤ 5) : n ≤ 5 := by
  fail_if_success proof_broker [z3]
  exact h2

/-- Numeral-body ℕ constant for the α+ℕ-def shape below. -/
def PBPolyDef : Nat := 3

/-- A ℕ-typed hypothesis over a numeral-body constant rides along an
    α goal: it fills the unfold table WITHOUT tripping ℕ mode, the
    pipeline's definition_unfolding pass really rewrites the IR, and
    the plain route admits the trace and inverts it (the same
    `invertDefUnfolds` as term mode) before the α replay — admission
    always pairs with inversion on BOTH cert-consuming α entry
    points. -/
theorem pb_poly_def_unfold_plain {α : Type} [CommRing α]
    [LinearOrder α] [IsStrictOrderedRing α]
    (n m : α) (h1 : n ≤ 5) (h2 : m ≤ 3) (h3 : n + m ≥ 9)
    (hp : PBPolyDef ≤ 3) : False := by
  proof_broker [z3]

#print axioms pb_poly_def_unfold_plain

/-- SOUNDNESS (the M2 attack surface): a Farkas witness valid over
    ℤ only — the +1-trick combination `{h: 1, neg_goal: 1}` for
    `0 < n ⊢ 1 ≤ n`, whose Int residual is `1 - n + n = 1 > 0` but
    whose strictness-preserving α residual is `-n + (n - 1) = -1`
    (false at a dense α: n = 1/2 over ℝ refutes the implication).
    `poly_replay_test` drives the REAL α closer with exactly that
    witness; it must fail, and the goal is then closed honestly from
    the rescue hypothesis the witness never mentions. (The live
    routes were probed to refuse the same shape — z3, cvc4, bare —
    but a live test cannot be committed: without the rescue
    hypothesis the goal is unprovable at generic α, which is the
    point.) -/
example {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (n : α) (h : 0 < n) (hextra : 1 ≤ n) : 1 ≤ n := by
  fail_if_success poly_replay_test
    "{\"coefficients\": [
       {\"hypothesis\": \"h\", \"coefficient\": \"1\"},
       {\"hypothesis\": \"neg_goal\", \"coefficient\": \"1\"}]}"
  exact hextra

/-- Positive control for `poly_replay_test`: an α-valid witness
    closes through the same tactic (the negative above is not an
    always-fail artifact). -/
example {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (n : α) (h : n ≤ 5) : n ≤ 6 := by
  poly_replay_test
    "{\"coefficients\": [
       {\"hypothesis\": \"h\", \"coefficient\": \"1\"},
       {\"hypothesis\": \"neg_goal\", \"coefficient\": \"1\"}]}"

/-- Walker-strict at α: the α specialization is not
    walker-invertible, so the spec gate refuses fail-closed. -/
example {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (n : α) (h : n ≤ 3) : n ≤ 5 := by
  fail_if_success proof_broker_walker
  exact le_trans h (by norm_num)

/-- Fail fast: α cannot mix with ℕ carriers (R3-M2 scope). -/
example {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (n : α) (k : Nat) (h : k ≤ 3) (h2 : n ≤ 3) : n ≤ 5 := by
  fail_if_success proof_broker_term [z3]
  exact le_trans h2 (by norm_num)

/-- Fail fast: α cannot mix with Real carriers. -/
example {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (n : α) (r : Real) (hr : r ≤ 3) (h2 : n ≤ 3) : n ≤ 5 := by
  fail_if_success proof_broker_term [z3]
  exact le_trans h2 (by norm_num)

/-- Fail fast: two qualified type variables (M2 scope: one). -/
example {α β : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    [CommRing β] [LinearOrder β] [IsStrictOrderedRing β]
    (n : α) (h : n ≤ 3) : n ≤ 5 := by
  fail_if_success proof_broker_term [z3]
  exact le_trans h (by norm_num)

/-- An UNQUALIFIED type variable (no ordered-ring instances) is not
    recognized; the reifier fails fast as before M2. -/
example {γ : Type} [Preorder γ] (n : γ) (h : n ≤ n) : n ≤ n := by
  fail_if_success proof_broker_term [z3]
  exact h

/-- A qualified α merely IN SCOPE over an Int goal does not switch
    modes: the core Int path runs, tight footprint preserved. -/
theorem pb_poly_scope_int {α : Type} [CommRing α] [LinearOrder α]
    [IsStrictOrderedRing α] (x y : Int) (h1 : x + 1 ≤ y) (h2 : y ≤ 5) :
    x ≤ 4 := by
  proof_broker_term

#print axioms pb_poly_scope_int

/-- Phase-3 M3 exit criterion (roadmap §Phase 3): the worked
    higher-order goal of `examples/example2-function-composition.json`,
    closed end-to-end through the Vampire path.

    `proof_broker` reifies this to a higher-order IR (`P` over a
    function type, `Function.comp` as an uninterpreted symbol,
    a `∀` over `Nat → Nat`, an equality at function type),
    `order = higher_order` routes dispatch past the first-order
    SMT adapters to Vampire, the THF problem is proved, the
    minted Tier-3 `tstp-thf` cert re-verifies through
    `Tier3_tptp`'s provenance gate (`verifiedTier3Provenance`),
    and the registered `holCloser` (`aesop`) emits the kernel
    proof term. Cert-gated and axiom-free — same H1 contract as
    `omega` for LIA / `linarith` for LRA; the footprint stays
    within the documented core ceiling (pinned in
    `tools/axiom_allowlist.json`). -/
theorem hol_function_composition_axiom_free
    (f g : Nat → Nat) (P : (Nat → Nat) → Prop)
    (h1 : ∀ h : Nat → Nat, P h → P (h ∘ h))
    (h2 : P f) (h3 : f = g) : P (g ∘ g) := by
  proof_broker

#print axioms hol_function_composition_axiom_free


/- ============================================================
   R4.2 — the verinf bracket-spike obligations, Mathlib shapes

   The Mathlib-flavored half of the R4 pins (the Mathlib-free half
   is the `pb_r4_*` block at the end of `Test/Tactic.lean`): the
   `ZMod.val` and `Fin n` shapes that only exist once Mathlib is
   imported. Line numbers refer to
   `lean/BracketSpike/BracketSpike/Bracket.lean` on verinf's
   `lean-bracket-spike` branch.
   ============================================================ -/

/-- Goldilocks, as in the spike. -/
private def pbBracketP : ℕ := 18446744069414584321

/-- D1 / `Bracket.lean:69`. `x.val` is `ZMod.val`, an applied
    ℕ-valued function: an opaque atom carrying `0 ≤ ↑atom` and
    nothing else. Before R4.2 this was
    `unsupported ℕ term x.val` and the tactic never dispatched. -/
theorem pb_r4_bracket_hzsum (x z : ZMod pbBracketP) (Zmax : ℕ)
    (hx : x.val < 2^24) (hz : z.val < 2 * Zmax) :
    x.val + z.val < 2^24 + 2 * Zmax := by proof_broker_term
#print axioms pb_r4_bracket_hzsum

/-- D1 / `Bracket.lean:71`. The definition `pbBracketP` occurs both
    at an arithmetic position (the goal's right-hand side) and
    inside a TYPE (`ZMod pbBracketP`, the type of `x` and `z`).
    R4.2: the def-unfold inversion is a defeq `change`, not a
    `rewrite` — `rewrite`'s motive `fun _a => @ZMod.val _a x < _a`
    does not typecheck. -/
theorem pb_r4_bracket_hxz (x z : ZMod pbBracketP) (Zmax : ℕ)
    (hzsum : x.val + z.val < 2^24 + 2 * Zmax)
    (hle : (2:ℕ)^24 + 2 * Zmax ≤ pbBracketP) :
    x.val + z.val < pbBracketP := by proof_broker_term
#print axioms pb_r4_bracket_hxz

/-- D1 / `Bracket.lean:78`. The nonlinear atom `Zmax * zhigh.val`
    (a product of a ℕ variable and an atomized application) next to
    the LINEAR `Zmax * 2^16`. -/
theorem pb_r4_bracket_hlt (x z zhigh : ZMod pbBracketP) (Zmax : ℕ)
    (hx : x.val < 2^24) (hz : z.val < 2 * Zmax)
    (hprod_le : Zmax * zhigh.val ≤ Zmax * 2^16) :
    x.val + z.val + Zmax * zhigh.val < 2^24 + 2 * Zmax + Zmax * 2^16 := by
  proof_broker_term
#print axioms pb_r4_bracket_hlt

/-- D3 / `Bracket.lean:204`. `R.x i` is a projection applied at
    `Fin n`, a type the IR cannot declare: `R` is left out of the
    free vars (recorded in `skippedLocals`) and the application is
    an Int atom. -/
theorem pb_r4_bracket_s1_noninc {n : ℕ} (R : Fin n → ℤ) (i : Fin n)
    (a b : ℤ) (hab : a ≤ b) : a - R i ≤ b - R i := by proof_broker
#print axioms pb_r4_bracket_s1_noninc

end ProofBroker.TestMathlib

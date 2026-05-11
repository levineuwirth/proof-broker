/-
Helper lemmas for term-mode Tier 1 Farkas reconstruction.

The plugin's term-mode closer (`evalProofBrokerTerm` in
`ProofBroker.Tactic`) takes a Farkas witness JSON (coefficients
keyed by hypothesis name) and builds an application of
`farkasContradict` from the LCtx-derived linear combination. The
cert IS the proof, not a certificate that one exists. No `omega`
call closes the *original* goal along this path; the closer's
trust footprint is exactly these lemmas plus a single `omega`
invocation on the strictly-positive linear combination subgoal
(`0 < c1*a1 + c2*a2` with literal c_i and symbolic a_i differences)
— a strictly narrower role than the LIA closer's full goal-discharge
omega call. Both are axiom-free.

Mirror of `rocq-bridge/theories/ProofBrokerTermMode.v`'s `farkas_le_2`,
except Lean has no core `ring` so we fold the residual `K` into a
single positive-sum premise and skip the `Heq` polynomial-identity
subgoal Rocq's term builder discharges via `ring`. The proof term
still names every coefficient explicitly — the Farkas multipliers
flow through.

Everything here is axiom-free: only `Init.Data.Int.Order` is touched.
`#print axioms` of any theorem that funnels through `farkasContradict`
reports "does not depend on any axioms".

Arity scope: arity 2 only today, matching the smallest non-trivial
Farkas cert (e.g. `5 ≤ x ∧ x ≤ 3 ⊢ False` with witness
`[(h1, 1), (h2, 1)]`). Arities 3..N are mechanical copies — write
them when a cert in practice exceeds arity 2.
-/

namespace ProofBroker.TermMode

/-- Direction-normalization helper: convert `a ≤ b` to `a - b ≤ 0`. -/
theorem leToLe0 {a b : Int} (h : a ≤ b) : a - b ≤ 0 :=
  Int.sub_nonpos_of_le h

/-- Direction-normalization helper: convert `a ≥ b` to `b - a ≤ 0`. -/
theorem geToLe0 {a b : Int} (h : a ≥ b) : b - a ≤ 0 :=
  Int.sub_nonpos_of_le h

/-- Strict-`<` normalization, +1 trick: `a < b` over `Int` is
    equivalent to `a + 1 ≤ b` (discrete domain), so the canonical
    `a' ≤ 0` form is `(a + 1) - b ≤ 0`. Matches the SDK's
    `lift_strict_pair` for LIA in `farkas.ml` — when the closer's
    OCaml-side `compute_residual` calls `compile_hypothesis` on a
    strict `<`, it gets back `Le (a-b+1)`, and the residual sum
    lines up with what this proof term emits. -/
theorem ltToLe0 {a b : Int} (h : a < b) : (a + 1) - b ≤ 0 :=
  Int.sub_nonpos_of_le (Int.add_one_le_of_lt h)

/-- Mirror of `ltToLe0` for `>`. Lean's `GT.gt a b` reduces to
    `LT.lt b a` by instance, so the closer could route `>` through
    `ltToLe0` after a syntactic swap; we provide this directly so
    `normalizeHypothesis` doesn't have to manage the reduction. -/
theorem gtToLe0 {a b : Int} (h : a > b) : (b + 1) - a ≤ 0 :=
  ltToLe0 h

/-- Farkas contradiction, arity 2. Hypotheses are pre-normalized to
    `a ≤ 0` form by the OCaml side via `leToLe0` / `geToLe0`. The
    `hpos` premise is discharged by `omega` at closer-build time —
    the only narrow tactical step the closer takes. The coefficients
    `c1`, `c2` are visible in the proof term as explicit Int literal
    arguments, so the cert's witness is *consumed* by reconstruction
    rather than thrown away. -/
theorem farkasContradict
    {a1 a2 : Int} (h1 : a1 ≤ 0) (h2 : a2 ≤ 0)
    {c1 c2 : Int} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hpos : 0 < c1 * a1 + c2 * a2) : False :=
  let s1 : c1 * a1 ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hc1 h1
  let s2 : c2 * a2 ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hc2 h2
  let ssum : c1 * a1 + c2 * a2 ≤ 0 := Int.add_nonpos s1 s2
  absurd hpos (Int.not_lt_of_ge ssum)

/-- Farkas reconstruction for a non-`False` goal of shape `b ≤ c`.
    Wraps `Decidable.byContradiction` over the goal (`Int.decLe`
    makes ≤ decidable, so no `Classical.choice`); the introduced
    `hng : ¬(b ≤ c)` is normalized to the SDK's compiled `Le` form
    (`c + 1 - b ≤ 0`, the LIA +1-trick image of `b ≤ c`'s negation)
    via the `Int.lt_of_not_ge / add_one_le_of_lt / sub_nonpos_of_le`
    chain, then plugged into `farkasContradict` along with one
    LCtx-derived normalized hypothesis. Arity 2: one real
    hypothesis + the `neg_goal` slot from the witness.

    The `heq` premise (strict-positivity of the Farkas linear
    combination) is discharged by `omega` at closer-build time, just
    as in `farkasContradict` — omega here only sees a literal-coefficient
    polynomial identity over symbolic `a1` and `b`, `c`, NOT the original
    LIA goal. -/
theorem farkasGoalLe2
    {b c : Int} {a1 : Int} (h1 : a1 ≤ 0)
    {c1 cng : Int} (hc1 : 0 ≤ c1) (hcng : 0 ≤ cng)
    (heq : 0 < c1 * a1 + cng * (c + 1 - b))
    : b ≤ c :=
  Decidable.byContradiction fun hng =>
    let hng_le : c + 1 - b ≤ 0 :=
      Int.sub_nonpos_of_le (Int.add_one_le_of_lt (Int.lt_of_not_ge hng))
    farkasContradict h1 hng_le hc1 hcng heq

/-- Farkas reconstruction for a strict goal `b < c`. Same shape as
    `farkasGoalLe2` but without the +1 trick — `¬(b < c) ↔ c ≤ b`
    (`Int.not_lt`) compiles directly to `c - b ≤ 0`, matching the
    SDK's [lift_le_pair c b] for `Not (LT.lt b c)`. `≥` and `>`
    over `Int` reduce to swapped `≤` / `<` by instance reduction
    (`GE.ge a b ↘ LE.le b a`, `GT.gt a b ↘ LT.lt b a`), so the
    closer routes them through these two helpers with swapped
    args rather than needing four lemmas. -/
theorem farkasGoalLt2
    {b c : Int} {a1 : Int} (h1 : a1 ≤ 0)
    {c1 cng : Int} (hc1 : 0 ≤ c1) (hcng : 0 ≤ cng)
    (heq : 0 < c1 * a1 + cng * (c - b))
    : b < c :=
  Decidable.byContradiction fun hng =>
    let hng_le : c - b ≤ 0 :=
      Int.sub_nonpos_of_le (Int.not_lt.mp hng)
    farkasContradict h1 hng_le hc1 hcng heq

/-- General-arity contradiction step. The OCaml-side closer builds
    `s = c1*a1 + c2*a2 + ... + cN*aN` (left-associative) and proves
    `s ≤ 0` by folding `Int.mul_nonpos_of_nonneg_of_nonpos` +
    `Int.add_nonpos` over the witness's entries — both `Int.*`
    lemmas are axiom-free, and so is this contradiction step.
    Generalizes `farkasContradict` to any arity (`farkasContradict`
    is the special case where the fold is one mul + one add). -/
theorem farkasContradictN
    (s : Int) (hsum : s ≤ 0) (hpos : 0 < s) : False :=
  absurd hpos (Int.not_lt_of_ge hsum)

end ProofBroker.TermMode

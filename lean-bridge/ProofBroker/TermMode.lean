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

Arity scope: arity-2 `farkasContradict` anchors the binary fixture;
arities 3..N are handled by `farkasContradictN` over a left-associative
sum the OCaml-side closer builds and discharges by `omega`. Comparison
goals (`≤`, `<`, `≥`, `>`, `=`) reach the same fold via the wrapper
helpers (`intLeViaLt` / `intLtViaLe`) which convert each goal shape
to an implication-False whose body the closer recurses into.
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

/-- Eq-hypothesis normalization: from `h : a = b`, produce
    `a - b ≤ 0`. The contribution is exactly `0` (since `a - b = 0`
    from `h`), but the symbolic Le-form lets Eq hypotheses fold into
    the existing strict-aware Le-only fold without special-casing.
    Solver-emitted certs use Eq with signed coefficients to capture
    both directions of an equality in a single witness slot; the
    bridge closer applies this to `h.symm` when the witness's
    coefficient is negative, flipping the linear-form direction
    while keeping the closer's positive-coefficient invariant on
    inequality premises. -/
theorem eqToLe0 {a b : Int} (h : a = b) : a - b ≤ 0 :=
  Int.sub_nonpos_of_le (Int.le_of_eq h)

/-- Flipped variant for negative coefficients on Eq hypotheses:
    same lemma applied to `h.symm`. Folded into a single helper so
    the closer doesn't need to construct `Eq.symm` as a separate
    application. -/
theorem eqToLe0Flipped {a b : Int} (h : a = b) : b - a ≤ 0 :=
  Int.sub_nonpos_of_le (Int.le_of_eq h.symm)

/-- Not-hypothesis normalization (LIA). Solver-emitted certs can
    reference hypotheses in negated form `(h : ¬(a ≤ b))` etc. —
    the SDK accepts these via `Farkas.compile_hypothesis`'s `Not`
    branch, which compiles `¬(a ≤ b)` to `b < a` (strict, then
    folded via the LIA +1 trick to `(b + 1) - a ≤ 0`). The bridge
    closer applies one of these helpers based on the inner head
    of the negation. All four are axiom-free via `omega`. -/
theorem notLeToLe0 {a b : Int} (h : ¬(a ≤ b)) : (b + 1) - a ≤ 0 := by omega

theorem notGeToLe0 {a b : Int} (h : ¬(a ≥ b)) : (a + 1) - b ≤ 0 := by omega

theorem notLtToLe0 {a b : Int} (h : ¬(a < b)) : b - a ≤ 0 := by omega

theorem notGtToLe0 {a b : Int} (h : ¬(a > b)) : a - b ≤ 0 := by omega

/-- Arity-N comparison-goal wrappers (Int). Convert a comparison goal
    into a `(neg_form → False)` shape so the closer can introduce the
    negated goal as a regular hypothesis and delegate to the existing
    arity-N False-fold; the same fold then consumes `neg_goal`
    alongside the witness's real-hypothesis entries at any arity.

    Both wrappers are axiom-free: `Decidable.byContradiction` resolves
    via `Int.decLe` / `Int.decLt`, and `Int.lt_of_not_ge` / `Int.not_lt`
    are themselves axiom-free in `Init.Data.Int.Order`. -/
theorem intLeViaLt {b c : Int} (h : c < b → False) : b ≤ c :=
  Decidable.byContradiction fun hng =>
    h (Int.lt_of_not_ge hng)

theorem intLtViaLe {b c : Int} (h : c ≤ b → False) : b < c :=
  Decidable.byContradiction fun hng =>
    h (Int.not_lt.mp hng)

/-- R3-M1 ℕ comparison-goal wrappers: the ℕ analogues of
    `intLeViaLt` / `intLtViaLe`. The ℕ→ℤ lift applies one of these
    to the ORIGINAL ℕ goal, obtains the positive ℕ counterexample
    hypothesis, casts it (and every witness-named hypothesis) to ℤ
    by term construction, and runs the Int Farkas fold — no
    decision procedure ever touches the original goal on this
    path. Axiom-free: `Decidable.byContradiction` over `Nat.decLe`
    / `Nat.decLt`, and `Nat.not_le` / `Nat.not_lt` are core. -/
theorem natLeViaLt {b c : Nat} (h : c < b → False) : b ≤ c :=
  Decidable.byContradiction fun hng =>
    h (Nat.not_le.mp hng)

theorem natLtViaLe {b c : Nat} (h : c ≤ b → False) : b < c :=
  Decidable.byContradiction fun hng =>
    h (Nat.not_lt.mp hng)

/-- R3-M1 cast-transfer shims: one per ℕ hypothesis shape the lift
    inverts, each a direct application of the embedding-witness
    lemmas the reifier records (`Int.ofNat_le` / `Int.ofNat_lt` /
    `Int.ofNat_inj` / `Int.natCast_nonneg` — see
    `Reify.natEmbeddingWitnessLemmas`). The closer applies the shim
    matching the hypothesis's shape and the kernel's defeq folds the
    cast through `+`/`*`/literals (core's `Int.natCast_add`/`_mul`
    are `rfl`), so no rewriting pass is needed. The `≥`/`>` variants
    lean on `GE.ge`/`GT.gt` reducing to the swapped `≤`/`<`. All
    axiom-free. -/
theorem natCastLe {a b : Nat} (h : a ≤ b) :
    (a : Int) ≤ (b : Int) := Int.ofNat_le.mpr h

theorem natCastLt {a b : Nat} (h : a < b) :
    (a : Int) < (b : Int) := Int.ofNat_lt.mpr h

theorem natCastGe {a b : Nat} (h : a ≥ b) :
    (b : Int) ≤ (a : Int) := Int.ofNat_le.mpr h

theorem natCastGt {a b : Nat} (h : a > b) :
    (b : Int) < (a : Int) := Int.ofNat_lt.mpr h

theorem natCastEq {a b : Nat} (h : a = b) :
    (a : Int) = (b : Int) := Int.ofNat_inj.mpr h

theorem natCastNotLe {a b : Nat} (h : ¬(a ≤ b)) :
    ¬((a : Int) ≤ (b : Int)) := fun hz => h (Int.ofNat_le.mp hz)

theorem natCastNotLt {a b : Nat} (h : ¬(a < b)) :
    ¬((a : Int) < (b : Int)) := fun hz => h (Int.ofNat_lt.mp hz)

theorem natCastNotGe {a b : Nat} (h : ¬(a ≥ b)) :
    ¬((b : Int) ≤ (a : Int)) := fun hz => h (Int.ofNat_le.mp hz)

theorem natCastNotGt {a b : Nat} (h : ¬(a > b)) :
    ¬((b : Int) < (a : Int)) := fun hz => h (Int.ofNat_lt.mp hz)

theorem natCastNotEq {a b : Nat} (h : ¬(a = b)) :
    ¬((a : Int) = (b : Int)) := fun hz => h (Int.ofNat_inj.mp hz)

theorem natCastNonneg (a : Nat) : (0 : Int) ≤ (a : Int) :=
  Int.natCast_nonneg a

end ProofBroker.TermMode

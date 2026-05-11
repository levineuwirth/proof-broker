/-
End-to-end tactic-elaboration tests for `ProofBroker.proof_broker`.

Each `example` below is a real Lean goal closed by the broker:
the tactic reifies the goal + Prop hypotheses into a LIA IR, hands
it to `runDispatchBroker` (consulting the cvc4/cvc5/z3 manifests
under `examples/`), re-checks the minted Tier 1 Farkas cert via
`runVerifyCertificate`, and closes the goal — for the LIA Tier 1
case via core Lean's `omega` (axiom-free, gated on cert
verification), for any other tier/fragment via the
`proofBrokerCertSound` trust axiom (removable per-tier).

Build success of this library *is* the test: any failure to
elaborate `by proof_broker` (no available adapter, cert that
fails to re-verify, reified IR shape outside the LIA fragment)
fails the build. The library has no precompile output and is
not imported by anything else; its sole purpose is to exercise
the elaboration-time FFI path.

Pre-condition: the test must be invoked with cwd =
`lean-bridge/`, so that the tactic's manifest loader finds
`../examples/manifest-{cvc4,cvc5,z3}.json`. Override via the
`PROOF_BROKER_EXAMPLES_DIR` env var if needed.
-/

import ProofBroker

-- The broker closes the goal with an axiom keyed on the goal
-- proposition; the resulting proof term doesn't textually mention
-- the hypotheses that were Farkas-combined inside the cert, so
-- Lean's unused-variable linter would otherwise flag every test.
set_option linter.unusedVariables false

namespace ProofBroker.Test

/-- Closed-form Farkas: `n + m = 10` and `0 ≤ m` together force `n ≤ 10`.
    Coefficients (h1=1, h3=1, neg_goal=1) sum to a contradiction. -/
example (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker

/-- Single-hypothesis bound transfer. -/
example (n : Int) (h : n ≤ 5) : n ≤ 10 := by
  proof_broker

/-- Trivial transitive case. -/
example (a b c : Int) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  proof_broker

/-- Equality propagated through addition. -/
example (x y : Int) (h : x = y) : x + 1 ≤ y + 1 := by
  proof_broker

/-- Adapter-list syntax: restrict dispatch to a single adapter. -/
example (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker [cvc5]

/-- Adapter-list syntax with order: input order is respected
    (preferHigherTier=false), so cvc4 is tried first even though
    cvc5 has a higher max-tier capability. -/
example (n : Int) (h : n ≤ 5) : n ≤ 10 := by
  proof_broker [cvc4, cvc5]

/-- Verbose form: `proof_broker?` emits a `logInfo` summary of the
    extraction path (IR shape, dispatch attempts + timing, cert
    tier/format, verify outcome) and then closes the goal as
    normal. The build will print one info line per invocation. -/
example (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker? [cvc4]

/-- Named LIA goal proven via the default `proof_broker` form,
    which `preferHigherTier := true` floats to cvc5's Tier 3
    alethe-2024 path. Even with a Tier 3 cert (no Lean-side
    Alethe walker yet) the closer is `omega` because the goal is
    LIA — cert verification gates the call, omega does the rest.
    omega is axiom-free, so this theorem's transitive axiom set
    must not contain `proofBrokerCertSound`; verified inline by
    `#print axioms` below. -/
theorem lia_axiom_free
    (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker

#print axioms lia_axiom_free

/-- Same theorem pinned through cvc4 (Tier 1 Farkas) — confirms
    the dispatch-on-fragment closer doesn't regress on the
    original Tier 1 path that motivated the omega-based closure
    in the first place. -/
theorem tier1_lia_axiom_free
    (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker [cvc4]

#print axioms tier1_lia_axiom_free

/-- BV vertical-slice gate: a closed `BitVec 8` arithmetic
    equality routes through the broker (QF_BV → cvc5/z3 oracle
    → cert-gated `decide`). The broker is overkill for a trivially
    decidable goal — the architectural payoff is showing the BV
    pipeline runs end-to-end (reifier emits `BitVec(8)` / `BV.add`,
    SMT-LIB serializer emits `(_ bv5 8)` / `bvadd`, the cvc5 / z3
    adapter dispatches under QF_BV, the verifier envelope-checks,
    the closer fires `decide`). `decide` is axiom-free, so this
    theorem's transitive axiom set should match the LIA path's
    `[propext, Quot.sound]` (or fewer) — verified by `#print
    axioms` below. -/
theorem bv_axiom_free : (5 : BitVec 8) + 3 = 8 := by
  proof_broker

#print axioms bv_axiom_free

/-- BV comparison ops (`<` / `<=`) over `BitVec` resolve to the
    unsigned variants in Lean's typeclass setup, so the reifier
    emits `BV.ult` / `BV.ule` rather than the polymorphic `LT.lt`
    / `LE.le`. The closer's `decide` path discharges this just as
    cleanly as the additive case. -/
theorem bv_compare_axiom_free : (3 : BitVec 8) < 5 := by
  proof_broker

#print axioms bv_compare_axiom_free

/-- Term-mode Tier 1 Farkas: `5 ≤ x ∧ x ≤ 3 ⊢ False`. Pinned through
    `[z3]` because z3 mints native Tier 1 Farkas certs (cvc5 mints
    Tier 3 alethe-2024 which the term builder doesn't yet consume,
    cvc4 mints Tier 0 oracle). The closer reads the witness's
    coefficients and applies `farkasContradict` from
    `ProofBroker.TermMode`; only the strictly-positive
    linear-combination subgoal goes through `omega` (a narrower
    role than the LIA closer's full goal-discharge omega call).
    Mirror of Rocq's `pb_term_axiom_free`. -/
theorem pb_term_axiom_free
    (x : Int) (h1 : 5 ≤ x) (h2 : x ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_term_axiom_free

/-- Term-mode arity-3 Tier 1 Farkas. The fold-based closer builds
    `c1*a1 + c2*a2 + c3*a3 ≤ 0` step by step via
    `Int.mul_nonpos_of_nonneg_of_nonpos` + `Int.add_nonpos`, then
    applies `farkasContradictN` to discharge the strict-positivity
    with `omega`. Lifts the closer's arity ceiling from 2 to N
    (every entry in the witness flows through as an explicit Int
    literal coefficient in the proof term). z3 mints the
    3-coefficient Farkas witness for this transitive chain. Mirror
    of Rocq's `pb_term_arity3_axiom_free`. -/
theorem pb_term_arity3_axiom_free
    (x y : Int) (h1 : 5 ≤ x) (h2 : x ≤ y) (h3 : y ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_term_arity3_axiom_free

/-- Term-mode Tier 1 Farkas with a non-`False` goal. The witness
    has one real-hypothesis entry plus a `neg_goal` slot the closer
    discharges via `farkasGoalLe2` (which wraps
    `Decidable.byContradiction` over `Int.decLe`, axiom-free). The
    cert minted by z3 carries coefficients on both `h` and
    `neg_goal`; the closer builds the proof term explicitly,
    omega-discharging only the strict-positivity polynomial
    identity. The `[propext, Quot.sound]` footprint matches the
    omega-closure path — no `Classical.choice`. -/
theorem pb_term_goal_axiom_free
    (n : Int) (h : n ≤ 5) : n ≤ 6 := by
  proof_broker_term [z3]

#print axioms pb_term_goal_axiom_free

/-- Term-mode with strict-`<` goal: closer routes through
    `farkasGoalLt2` (no LIA +1 trick — `¬(n < 5) ↔ 5 ≤ n` via
    `Int.not_lt`). -/
theorem pb_term_lt_axiom_free
    (n : Int) (h : n ≤ 4) : n < 5 := by
  proof_broker_term [z3]

#print axioms pb_term_lt_axiom_free

/-- Term-mode with `≥` goal: `GE.ge n 4` reduces by instance to
    `LE.le 4 n`, so the closer routes through `farkasGoalLe2` with
    arg swap and the resulting `4 ≤ n` proof term unifies with the
    `n ≥ 4` goal definitionally. -/
theorem pb_term_ge_axiom_free
    (n : Int) (h : 5 ≤ n) : n ≥ 4 := by
  proof_broker_term [z3]

#print axioms pb_term_ge_axiom_free

/-- Term-mode with strict-`>` goal: `GT.gt n 3` reduces to
    `LT.lt 3 n`; same routing as `≥` but through `farkasGoalLt2`. -/
theorem pb_term_gt_axiom_free
    (n : Int) (h : 5 ≤ n) : n > 3 := by
  proof_broker_term [z3]

#print axioms pb_term_gt_axiom_free

/-- Term-mode with equality goal: the closer pre-splits via
    `Int.le_antisymm` (since `¬(a = b)` is a disjunction outside
    single-witness Farkas scope) and runs the existing ≤-shape
    term-mode on each direction. Two solver dispatches, two
    `farkasGoalLe2` applications, one `Int.le_antisymm`. The
    axiom footprint stays `[propext, Quot.sound]` — splitting
    adds no new trust delta over the single-direction case. -/
theorem pb_term_eq_axiom_free
    (n : Int) (h1 : n ≤ 5) (h2 : 5 ≤ n) : n = 5 := by
  proof_broker_term [z3]

#print axioms pb_term_eq_axiom_free

/-- UF vertical-slice gate: a congruence-style goal with an
    uninterpreted function `f : Int → Int` and an equality hypothesis
    routes through the broker (QF_UFLIA → cvc5 oracle → cert-gated
    `subst_eqs; rfl` closer). The reifier walks the function-typed
    free var into the IR's free_vars list with `ty = "Int->Int"`,
    the SDK serializer emits `(declare-fun f (Int) Int)` plus
    `(f x)` / `(f y)` use sites, the verifier envelope-checks, and
    the closer's `subst h; rfl` chain discharges constructively.
    `subst_eqs` is axiom-free; this theorem's transitive axiom set
    matches the LIA / BV paths' [propext, Quot.sound] (or fewer). -/
theorem uf_axiom_free
    (f : Int → Int) (x y : Int) (h : x = y) : f x = f y := by
  proof_broker

#print axioms uf_axiom_free

/-- Multi-arg UF: a binary uninterpreted function. Reifier walks
    `Int → Int → Int` into the type-ref `"Int->Int->Int"` and the
    SDK's `parse_arrow_type` splits to `(declare-fun f (Int Int) Int)`.
    Closer: `subst_eqs` rewrites `b → a`, leaving `f a a = f a a`
    for `rfl`. -/
theorem uf_two_arg_axiom_free
    (f : Int → Int → Int) (a b : Int) (h : a = b) : f a b = f a a := by
  proof_broker

#print axioms uf_two_arg_axiom_free

/-- Composed / nested UF: function composition `f (g x)` with an
    equality hypothesis. Reifier emits nested `App "UF.f" [App "UF.g" [x]]`;
    closer chain (`subst_eqs; rfl`) handles the depth uniformly. -/
theorem uf_composed_axiom_free
    (f g : Int → Int) (x y : Int) (h : x = y) : f (g x) = f (g y) := by
  proof_broker

#print axioms uf_composed_axiom_free

/-- Predicate-valued UF: `P : Int → Prop`, modus-ponens-style goal.
    Exercises the reifier on `Prop` as an arrow codomain (SDK maps to
    `Bool`) and the closer on a non-equality goal. -/
theorem uf_predicate_axiom_free
    (P : Int → Prop) (x y : Int) (hp : P x) (h : x = y) : P y := by
  proof_broker

#print axioms uf_predicate_axiom_free

end ProofBroker.Test

# R6-016 — bridge build, for implementation review

**Build revision 2**, 2026-10-02. It responds to [the implementation review of revision 1](reviews/2026-10-02/R6-016-BUILD-REVIEW.md),
which found two P2 gaps. Interpretations 1 and 3 were accepted. Revision 1 is `bdfc1c97` (bridge `84ea4634`). This is the bridge
step of [the proposal, revision 2](R6-016-PROPOSAL.md), whose design was
[approved for implementation](reviews/2026-10-02/R6-016-AND-AUDIT-AMENDMENT-1-REVIEW-2.md) with the audit amendment (revision 3)
at `3b9d0795`.

**What changed in revision 2:**
1. **A size budget on numeral evaluation.** Revision 1's exponent cap did not bound evaluation: `((2 ^ 1024) ^ 1024)` passed it and
   computed a numeral of over a million bits. The cap is replaced by a 512-bit budget.
   - Every operand and every value computed must fit, or the term is not a numeral and stays an atom.
   - A power `b ^ k` (`b ≥ 2`) is rejected **before it is computed** whenever its least possible size, `log2(b)·k + 1` bits,
     exceeds the budget. Whatever passes is at most about 1,022 bits, so nested powers cannot grow past the budget.
   - **The pinned boundary:**
     - `2 ^ 511`, 512 bits, is a numeral, and the combination it carries closes;
     - `2 ^ 512`, and `(2 ^ 256) ^ 2`, stay atoms, and the same combination fails;
     - `x * ((2 ^ 1024) ^ 1024) ^ 1024` closes quickly as one atom, with nothing computed.
2. **The full axiom inventory is pinned** (proposal section 2): all 28 `TermMode` lemmas, and the 15 core lemmas the route's proof
   terms use. Each depends on at most `propext` and `Quot.sound`.

**Status:**
- **The bridge revision is `64585867`.** Nothing is locked, nothing is replayed, and no retained certificate was read for this
  build.
- **Tests:**
  - the synthetic tests pass (`Test/TermModeConstrained.lean`), with control 9's cases and the axiom pins;
  - the existing `Test.Tactic` and `Test.TacticStress` pass with live solvers;
  - `Test.TacticMathlib` and the corpus walker suite were not run.
- **Control 8 was exercised on synthetic proofs**, again at `64585867`
  ([record, revision 2](reviews/2026-10-02/R6-016-SYNTHETIC-AUDIT-PRELOCK-2.json); [revision 1's](reviews/2026-10-02/R6-016-SYNTHETIC-AUDIT-PRELOCK.json)
  is superseded). R6-015's seven
  constrained pairs and two new ones (c8, a product in the same order; c9, a numeral product) are all `certificate_alone`, and pass.
  The two pinned contrast pairs fail, as before. The driver is R6-015's, copied into `r6-016/`, with its bridge revision and pairs.
- **The overlays still apply.** R6's observation overlay and R6-015's replay overlay (`replay_bridge.lean_edits`) both apply to
  the new `Tactic.lean` unchanged.

## What was built

**`TermMode.posOfLinearNum`**, exactly as frozen in the proposal's section 1. It replaces `posOfNormNum`, which is removed; R6-015
stays reproducible from `476fab31`. The returned term, the gates and the fold are unchanged.

**The reifier,** implementing section 3's rules:
1. **Linear structure.** A *closed numeral* is a literal, or `+`, `−`, `*`, negation, `Nat.succ` and `^` of closed numerals, or a
   cast of a closed ℕ numeral, within the 512-bit budget. It is evaluated at the meta level and reified as `num`; the kernel checks
   the evaluation by unfolding. A product with a closed numeral on either side becomes `mulL` or `mulR`.
2. **Casts** are pushed through ℕ `+`, closed ℕ numerals, `Nat.succ`, and ℕ `*` with a closed-numeral factor. Every other ℕ term
   stays under the cast, as an atom.
3. **A ℕ product of two non-numeral factors under a cast** becomes the product of the casts, in the same order. **It is applied
   recursively through nested ℕ products:** `↑(a * b * c)` becomes `(↑a * ↑b) * ↑c`, so that it meets `↑a * ↑b * ↑c` written at
   `Int`. An `Int` product of two non-numeral factors is an atom as written.
4. **Atoms** are identified up to definitional equality at instance transparency. The first occurrence is the context's
   representative.
5. **The kernel gate** rechecks every identification, as before.

**The residual message** now prints `k * (atom)` per term, the `Int.Linear` form, without R6-015's `^1`.

**The axiom docstrings** in `TermMode.lean` are corrected, as the proposal said. The bridge tests pin:
- `posOfLinearNum`: `propext` and `Quot.sound`;
- `farkasContradictN`, `intLeViaLt` and `natCastLe`: `propext`;
- `natCastNonneg`: none;
- `notLeToLe0`: `propext` and `Quot.sound`.

## Tests (`lean-bridge/Test/TermModeConstrained.lean`)

**R6-015's cases are kept.** Six expected messages changed, in format only: each prints the same polynomial without `^1`, possibly
in a different term order. Each was checked by hand; for example, `−1·(z/3) − 1·↑n + 7` is unchanged. Every closing case still
closes, both cast/product directions included.

**Control 9's cases are new:**

| case | expectation |
|---|---|
| 9a, the axiom gate | `posOfLinearNum` and the route's lemmas, as pinned above. A constrained proof of the mixed-carrier goal depends on `propext` and `Quot.sound`, exactly as an `omega` proof of the same goal does, and as the pinned fold's does. Under R6-015's step it also had `Classical.choice` |
| 9b, no commutativity | `h : x * y ≤ 5 ⊢ y * x ≤ 5` with (`h` 1, `neg_goal` 1) fails: `−1·(y*x) + 1·(x*y) + 1`, two atoms. R6-015's ring normalizer would have closed it |
| 9c, product identity | the same product in the same order closes; `↑(a * b * c)` against `↑a * ↑b * ↑c` closes |
| 9d, numeral products | `3 * (a − b)` with `neg_goal` 3, `a * 0`, and `↑(Zmax * 2 ^ 16)` against `65536 * ↑Zmax` close |
| 9e, 9f | ℕ nonnegativity not used, and a hypothesis reached through the sum: the existing sections, unchanged |

## Interpretations (accepted in review)

1. **Rule 3 recurses through nested ℕ products.** The proposal says "the product of the casts in the same order". It is applied
   recursively, so that a nested ℕ product meets the same product written at `Int`. It never reorders or reassociates.
2. **The closed-numeral scope:** `+`, `−`, `*`, negation, `Nat.succ`, `^`, and casts of ℕ numerals, within the 512-bit budget,
   which replaced revision 1's exponent cap.
3. **An `Int` product is an atom as written.** Casts inside its factors are not rewritten. Two such atoms meet only through
   instance-transparency definitional equality, as section 3, rule 3 says for products.

   **The limitation, kept explicit:** `↑(a * b) * ↑a` does not meet `↑(a * b * a)` under this policy, although they are
   arithmetically equal. The first is an `Int` product of a cast and a cast; the second becomes `(↑a * ↑b) * ↑a`, and
   `↑(a * b)` is not rewritten inside an `Int` product.

## Next

- **The amended audit** (build revision 3 of `Audit.lean`) and its controls, for its own implementation review.
- **Then the R6-016 harness and analysis.**

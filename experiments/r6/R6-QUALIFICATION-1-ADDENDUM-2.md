# R6 qualification 1, addendum 2 — l096 and l099, bound through the recorded renaming

Recorded 2026-10-02. This classifies the 16 slots that [addendum 1](R6-QUALIFICATION-1-ADDENDUM-1.md) left unbound. It follows
[amendment 1 to the audit, revision 3](R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md) and
[its build, revision 5](R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-BUILD.md), in the recorded order:
1. build revision 5 approved for locking at `9eee1a0d` ([approval](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-BUILD-REVIEW-3.md));
2. locked as `qualification-audit-v2` (`c42906ed…`, commit `ad4aef72`);
3. controls C1–C9 and R1–R10 re-run under the lock, all passing, every report identical to the pre-lock record
   ([record](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-CONTROLS.json));
4. **the regression:** the amended program reproduced addendum 1 at R6's 32 classified slots
   ([record](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-REGRESSION.json), `5c06fa7a…`):
   - every report valid: exit 0, real mode on Lean 4.32.2, `matches_residual`, both targets locatable;
   - no difference in any classification, or in any whole target's mapped hypotheses. So `qualification-audit-v1`'s parameter
     mapping was right at all 32, and no defect of it is recorded;
5. the 16 audited ([record](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-ADDENDUM-2.json)), gated on that regression record.

**The audit verified** the lock and `live-evaluation-v3` before and after, and the regression record before and after. It
re-checked each export's digest as it read it, and each slot's rename rows against its run's seal. **Addendum 1, the
`qualification-audit-v1` lock and its record are unchanged,** as are R6's runs, records, locks, analysis and counts.

## Result

| obligation | slots | classification |
|---|---|---|
| l096 | 8 | **sufficient, but context referenced**: the weighted sum alone proves `0 < s` (hypothesis-free, kernel-checked), but R6's proof of `0 < s` drew on `hlt` and `neg_goal` |
| l099 | 8 | **sufficient, but context referenced**, with `hgt` and `neg_goal` |

**At every one of the 16 slots:**
- **The binding is `matches_residual_after_renaming`.** The three rename rows, `c'` → `c_` (index 4), `h1'` → `h1_` (index 8) and
  `h2'` → `h2_` (index 9), were verified against the run's sealed rows and the site's frozen context, and applied by binder
  identity. The renamed print equals the retained residual:
  - l096: `0 < 1 * (c + 1 - c_) + 1 * (c_ - 1 + 1 - c)`;
  - l099: `0 < 1 * (c_ + 1 - c) + 1 * (c - 1 + 1 - c_)`.

  One residual per site, the same at all eight draws.
- **The parameters are established,** 11 of them, by the lockstep walk.
- **Both targets are locatable,** and their classifications agree.
- **Check 2 was established directly** (kernel accepted), without generalization. At l096 the statement is
  `∀ {c c' : Int}, 0 < 1 * (c + 1 - c') + 1 * (c' - 1 + 1 - c)`; l099's swaps the roles.
- **The mapping:** in the whole declaration, `hlt` (l096) or `hgt` (l099) is parameter 10 of the local theorem, and `neg_goal` is
  internal to the local proof.

## What this means for qualification 1

**All 48 of R6's slots are now classified,** by addenda 1 and 2 together:

| classification | slots | obligations |
|---|---|---|
| certificate alone | 24 | l069, l071, l078 (addendum 1) |
| sufficient, but context referenced | 23 | l070, draws 1–4 and 6–8 (addendum 1); l096 and l099 (this addendum) |
| sufficiency not established | 1 | l070, draw 5 (addendum 1) |

- **At l096 and l099,** the certificate would have sufficed on its own at every draw. R6's final step nevertheless reached
  `hlt` or `hgt`, and `neg_goal`, through contextual `omega`. They do not meet the stronger reading.
- **"Consumed", in its strong sense,** stays established for 24 of the 48 proofs, at three of the six obligations. This addendum
  does not add to that. For the other 24 slots, the qualification's weaker meaning stands: the closer folded an independently
  verified certificate, and the kernel accepted the result.

R6-014's results are unchanged.

## Disclosure

- **The outcome was anticipated.** Addendum 1 recorded these slots' Check 1 and Check 2 values as diagnostics, not results:
  Check 2 established, with `hlt` or `hgt` and `neg_goal` referenced. The amendment's binding rule was designed after that, with
  this outcome visible. The rule, its synthetic controls (R1–R6, R4b) and the rows it reads were frozen and reviewed before the
  amended program read any of these exports.
- **What the build read before the lock:** the dry runs of the lock record read the 16 runs' sealed rename rows and the site's
  frozen context. They hashed the compressed exports, and neither decompressed nor audited any of them.

## What follows

- **R6-016's control 5** computes its labels from the classifications recorded at its lock: addendum 1 and this addendum
  ([R6-016 proposal](R6-016-PROPOSAL.md), section 5).
- **R6-015's l175 proofs** under the amended program are recorded separately and informationally
  ([R6-015-L175-AUDIT-V2.md](R6-015-L175-AUDIT-V2.md)). So is the [erratum](R6-015.md#erratum-2026-10-02) to R6-015's account
  of l175.
- **A sharper version of the synthesis's qualification sentence,** citing both addenda, remains the author's decision.

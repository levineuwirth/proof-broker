/-
RmsNormBracket/Model.lean — the RMSNorm rsqrt bracket: field, configuration,
derived widths, and the integer core of the uniqueness argument.

Correspondence (verinf, branch of this worktree):
  * `P`            — `prover/cuda_primitives.py::P`, the verifier's `P`.
  * `LIMB_W`       — `claims.RMS_LIMB_W` = `handlers.RMS_LIMB_W` = 18.
  * `Config`       — `claims.RmsNormConfig` (d, s, eps_int) with the widths its
                     properties derive and `handlers.rs::rms_widths` re-derives.
  * `WellFormed`   — the asserts of those two derivations (`2·y_width + LIMB_W ≤
                     63`, `magic + 2^slack_width < P`, `G2_width + 2·LIMB_W ≤ 62`)
                     plus the chunk-count shape of the production layout, which
                     `Bracket.lean` fixes (see the generated header there).
  * `production`   — d = 4096, s = 2^12, eps_int = 168 (Llama 7B / Maverick),
                     the widths `rmsnorm-bracket-fix.md` §3 lists; `Witnesses.lean`
                     re-checks them against the derivation formulas by `decide`.

The constraint structures (`OldBracket`, `RepairedBracket`) are generated into
`Bracket.lean` from the Python model so their text cannot drift from the
witness checks; the proposed uniqueness theorem is in `Uniqueness.lean`.
-/
import Mathlib

namespace RmsNorm

/-- Goldilocks prime `2^64 − 2^32 + 1`. -/
def P : ℕ := 18446744069414584321

instance : NeZero P := ⟨by norm_num [P]⟩

/-- `claims.RMS_LIMB_W` / `handlers.RMS_LIMB_W`: width of the three `S_total`
    limbs and of the carry lows `g0l`, `g1l`. -/
def LIMB_W : ℕ := 18

/-- The public claim configuration together with the range windows both
    verifier sides derive from it. The widths are *fields* rather than
    definitions so that a changed bound can be modeled by changing a number
    and re-checking `WellFormed`; `Witnesses.lean` pins the production values
    to the derivation formulas. -/
structure Config where
  d : ℕ
  s : ℕ
  eps : ℕ
  y_width : ℕ
  slack_width : ℕ
  g0h_width : ℕ
  g1h_width : ℕ
  G2_width : ℕ

namespace Config

/-- `RmsNormConfig.magic = d · s⁴`. -/
def magic (c : Config) : ℕ := c.d * c.s ^ 4

/-- The smallest row energy the claim admits, `S_min = d · eps_int`. -/
def S_min (c : Config) : ℕ := c.d * c.eps

/-- The asserts of `RmsNormConfig` / `rms_widths`, the two width identities,
    and the production chunk layout (`_chunk_widths`: 16-bit chunks plus one
    narrower top chunk) that `Bracket.lean` fixes: y−1 in 2 chunks, slack in 4,
    g0h and g1h in 3, G2 in 2. -/
structure WellFormed (c : Config) : Prop where
  eps_pos      : 1 ≤ c.eps
  y_limb       : 2 * c.y_width + LIMB_W ≤ 63
  slack_nowrap : c.magic + 2 ^ c.slack_width < P
  G2_nowrap    : c.G2_width + 2 * LIMB_W ≤ 62
  g0h_eq       : c.g0h_width = 2 * c.y_width
  g1h_eq       : c.g1h_width = 2 * c.y_width + 1
  y_shape      : 16 < c.y_width ∧ c.y_width ≤ 32
  slack_shape  : 48 < c.slack_width ∧ c.slack_width ≤ 64
  g0h_shape    : 32 < c.g0h_width ∧ c.g0h_width ≤ 48
  g1h_shape    : 32 < c.g1h_width ∧ c.g1h_width ≤ 48
  G2_shape     : 16 < c.G2_width ∧ c.G2_width ≤ 32

end Config

/-- Llama 7B / Maverick: `d = 4096`, `s = 2^12`, `eps_int = 168`;
    widths from `rmsnorm-bracket-fix.md` §3 (y 21, slack 59, g0h 42, g1h 43,
    G2 25), cross-checked in `Witnesses.lean`. -/
def production : Config :=
  { d := 4096, s := 4096, eps := 168,
    y_width := 21, slack_width := 59, g0h_width := 42, g1h_width := 43, G2_width := 25 }

theorem production_wf : production.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## The honest-input domain (checkpoint 3)

Scalar uniqueness says nothing about which inputs have a witness at all
(review of checkpoint 2: a narrower `y_width` keeps uniqueness and two
sampled honest rows while admitting no witness for the all-zero row). A
candidate configuration therefore also declares the row-energy domain
`[S_min, S_max]` it must serve, and `Domain.Complete` collects the
conditions under which every energy in that domain has an honest witness
(`Completeness.honest_exists`). The two exhibited numbers (`y_max`, the
scalar at `S_min`; `slack_root`, the integer square root of
`magic · S_max`) make every condition decidable by `decide`. -/

/-- A declared honest-input domain for a configuration, with the two
    exhibited roots the completeness conditions need. -/
structure Domain (c : Config) where
  S_max : ℕ
  y_max : ℕ
  slack_root : ℕ

namespace Domain

/-- Completeness conditions for `[c.S_min, D.S_max]`:
    * the domain is nonempty and fits the three limbs;
    * `y_max` satisfies the lower bracket at `S_min` and fits `y_width`, so
      every honest scalar on the domain (which is at most `y_max`) fits;
    * `slack_root = isqrt(magic · S_max)`, and the largest honest slack
      `2·slack_root + S_max` fits `slack_width`;
    * the top carry accumulator fits `G2_width` (`(magic + 2^slack_width) ≫ 2·LIMB_W`);
    * `magic ≥ 1` (so the upper bracket's `magic − 1` is honest). -/
structure Complete {c : Config} (D : Domain c) : Prop where
  S_min_pos  : 1 ≤ c.S_min
  S_min_le   : c.S_min ≤ D.S_max
  S_max_lt   : D.S_max < 2 ^ (3 * LIMB_W)
  y_max_pos  : 1 ≤ D.y_max
  y_max_ge   : c.magic ≤ D.y_max * D.y_max * c.S_min
  y_max_fits : D.y_max - 1 < 2 ^ c.y_width
  root_le    : D.slack_root * D.slack_root ≤ c.magic * D.S_max
  root_lt    : c.magic * D.S_max < (D.slack_root + 1) * (D.slack_root + 1)
  slack_fits : 2 * D.slack_root + D.S_max < 2 ^ c.slack_width
  G2_fits    : (c.magic + 2 ^ c.slack_width) / 2 ^ (2 * LIMB_W) < 2 ^ c.G2_width
  magic_pos  : 1 ≤ c.magic

end Domain

/-! ## The integer core

Once both brackets are integer identities — `y² · S ≥ magic` and
`(y−1)² · S < magic` with `y ≥ 1` — the scalar is pinned. This is the
monotone-threshold schema of the softmax spike (`threshold_unique`), stated
directly on ℕ for the rsqrt instance. Nothing about the field, the limbs or
the windows enters here; the whole difficulty of the case study is in
*reaching* these four hypotheses from the constraint system. -/

/-- Two scalars satisfying the integer brackets against the same row energy
    coincide. `S` may be any natural (the hypotheses are contradictory at
    `S = 0`, which is the honest reading: no witness exists there). -/
theorem rsqrt_unique_nat {S m y y' : ℕ} (hy : 1 ≤ y) (hy' : 1 ≤ y')
    (h1 : m ≤ y * y * S) (h2 : (y - 1) * (y - 1) * S < m)
    (h1' : m ≤ y' * y' * S) (h2' : (y' - 1) * (y' - 1) * S < m) : y = y' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hle : y ≤ y' - 1 := by omega
    have : y * y * S ≤ (y' - 1) * (y' - 1) * S :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hle hle)
    omega
  · have hle : y' ≤ y - 1 := by omega
    have : y' * y' * S ≤ (y - 1) * (y - 1) * S :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hle hle)
    omega

end RmsNorm

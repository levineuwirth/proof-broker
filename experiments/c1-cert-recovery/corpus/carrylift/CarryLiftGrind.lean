/-
RmsNormBracket/CarryLiftGrind.lean — GENERATED from CarryLift.lean by
tools/make_variants.py: the four `-- SITE n` closers are `grind`.
Everything else is byte-identical to CarryLift.lean (diff is the audit).

The stage modeled is `F10` (lower bracket) / `F14` (upper bracket) of
`rmsnorm_compile` together with the quad `rms.loH0` / `rms.hiH0`:

    H0 = q · S0                        (quad, mod P)
    H0 = g0l + 2^LIMB_W · g0h          (F+0, mod P; g0h assembled from chunks)

with `S0`, `g0l` LIMB_W-bit, `q ≤ 2^{2·y_width}`, `g0h < 2^{g0h_width}`. The
square bound is INCLUSIVE: the range check gives `y−1 < 2^y_width`, hence
`y ≤ 2^y_width` and `q ≤ 2^{2·y_width}`, and the endpoint is admitted by the
repaired bracket (`Witnesses.wE_rep`: `S_total = 2^18`, `y = 2^21`,
`q1 = 2^42` — reviewer finding, checkpoint 1). The strict LIMB_W bound on
`S0` still gives `q·S0 < 2^{2·y_width + LIMB_W}`. The lemma says the two
field equations are the integer identity
`q·S0 = g0l + 2^LIMB_W·g0h`, i.e. `(g0l, g0h)` is the exact (mod, div) split
of the product — the fact `rmsnorm-bracket-fix.md` §2 states as "no
intermediate can wrap". `g0h` enters as one field element with a range
fact; recomposing it from its three chunks is a separate lift (not in this
checkpoint).

Two statements:
  * `carry_stage_lift`             — generic widths, the version the full
                                     bracket argument will instantiate;
  * `carry_stage_lift_production`  — literal production widths, the
                                     COMPARISON SUBJECT. Its arithmetic side
                                     goals are marked `-- SITE n`; the broker
                                     copy `CarryLiftPB.lean` is this file with
                                     exactly those tactics swapped
                                     (`diff CarryLift.lean CarryLiftPB.lean`
                                     is the audit). The nonlinear step
                                     `q.val * S.val < 2^42 * 2^18` is a
                                     FIXED HELPER in both copies (the
                                     "fixed-helper comparison"); the
                                     `experiments/` probes drop it.
-/
import RmsNormBracket.Model

set_option profiler true
set_option profiler.threshold 0

namespace RmsNorm

/-- Adding two field elements whose representatives do not overflow is exact
    (the softmax spike's `val_add_lt`, verbatim). -/
lemma val_add_lt {a b : ZMod P} (h : a.val + b.val < P) :
    (a + b).val = a.val + b.val := by
  rw [ZMod.val_add, Nat.mod_eq_of_lt h]

/-- Multiplying two field elements whose representatives' product stays below
    `P` is exact. -/
lemma val_mul_lt {a b : ZMod P} (h : a.val * b.val < P) :
    (a * b).val = a.val * b.val := by
  rw [ZMod.val_mul, Nat.mod_eq_of_lt h]

/-- `(2^L : ZMod P).val = 2^L` when `2^L < P`. -/
lemma val_two_pow {L : ℕ} (h : 2^L < P) : ((2:ZMod P)^L).val = 2^L := by
  have : ((2:ZMod P)^L) = ((2^L : ℕ) : ZMod P) := by push_cast; rfl
  rw [this]
  exact ZMod.val_natCast_of_lt h

/-- **One carry stage, lifted (generic widths).**
    `hquad`, `hF` are the emitted constraints verbatim (`x·y + a·z = b` and the
    `L2_IdentityScalar` family, both mod P); `hq … hhi` are the range facts the
    lookups certify; `hwP`, `hwP'` are the width conditions
    (`2·y_width + LIMB_W ≤ 63` and `LIMB_W + g0h_width ≤ 61` at production). -/
theorem carry_stage_lift {q S H g_lo g_hi : ZMod P} {wq L whi : ℕ}
    (hquad : q * S - H = 0)
    (hF : H - g_lo - 2^L * g_hi = 0)
    (hq : q.val ≤ 2^wq) (hS : S.val < 2^L)
    (hlo : g_lo.val < 2^L) (hhi : g_hi.val < 2^whi)
    (hwP : 2^(wq + L) < P) (hwP' : 2^(L + whi) < P) :
    q.val * S.val = g_lo.val + 2^L * g_hi.val := by
  have hqS : q * S = H := by linear_combination hquad
  have hH : H = g_lo + 2^L * g_hi := by linear_combination hF
  have h2L : 2^L < P :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right L whi)) hwP'
  have hpow : ((2:ZMod P)^L).val = 2^L := val_two_pow h2L
  have hside1 : 2^L * g_hi.val < P := by
    calc 2^L * g_hi.val < 2^L * 2^whi := Nat.mul_lt_mul_of_pos_left hhi (by positivity)
      _ = 2^(L + whi) := by rw [pow_add]
      _ < P := hwP'
  have hmul : ((2:ZMod P)^L * g_hi).val = 2^L * g_hi.val := by
    rw [val_mul_lt (by rw [hpow]; exact hside1), hpow]
  have hside2 : g_lo.val + 2^L * g_hi.val < P := by
    have h1 : 2^L * g_hi.val + 2^L ≤ 2^L * 2^whi := by
      have : g_hi.val + 1 ≤ 2^whi := hhi
      calc 2^L * g_hi.val + 2^L = 2^L * (g_hi.val + 1) := by ring
        _ ≤ 2^L * 2^whi := Nat.mul_le_mul_left _ this
    have h2 : 2^L * 2^whi = 2^(L + whi) := by rw [pow_add]
    omega
  have hsum : (g_lo + (2:ZMod P)^L * g_hi).val = g_lo.val + 2^L * g_hi.val := by
    rw [val_add_lt (by rw [hmul]; exact hside2), hmul]
  have hside3 : q.val * S.val < P := by
    calc q.val * S.val ≤ 2^wq * S.val := Nat.mul_le_mul_right _ hq
      _ < 2^wq * 2^L := Nat.mul_lt_mul_of_pos_left hS (by positivity)
      _ = 2^(wq + L) := by rw [pow_add]
      _ < P := hwP
  have hprod : (q * S).val = q.val * S.val := val_mul_lt hside3
  rw [← hprod, hqS, hH, hsum]

/-- **The comparison subject.** `carry_stage_lift` at the production widths
    (`q = q1 < 2^42`, 18-bit limb and carry low, `g0h < 2^42`), the width
    conditions now closed numerals. `hP` names the prime as a numeral so that
    every SITE is a goal over ℕ atoms with literal coefficients — the same
    hypothesis list is visible to both closers. -/
theorem carry_stage_lift_production {q S H g_lo g_hi : ZMod P}
    (hquad : q * S - H = 0)
    (hF : H - g_lo - 2^18 * g_hi = 0)
    (hq : q.val ≤ 2^42) (hS : S.val < 2^18)
    (hlo : g_lo.val < 2^18) (hhi : g_hi.val < 2^42) :
    q.val * S.val = g_lo.val + 2^18 * g_hi.val := by
  have hP : P = 18446744069414584321 := rfl
  have hqS : q * S = H := by linear_combination hquad
  have hH : H = g_lo + 2^18 * g_hi := by linear_combination hF
  have h2L : (2:ℕ)^18 < P := by grind                                    -- SITE 1
  have hpow : ((2:ZMod P)^18).val = 2^18 := val_two_pow h2L
  have hside1 : 2^18 * g_hi.val < P := by grind                            -- SITE 2
  have hmul : ((2:ZMod P)^18 * g_hi).val = 2^18 * g_hi.val := by
    rw [val_mul_lt (by rw [hpow]; exact hside1), hpow]
  have hside2 : g_lo.val + 2^18 * g_hi.val < P := by grind                 -- SITE 3
  have hsum : (g_lo + (2:ZMod P)^18 * g_hi).val = g_lo.val + 2^18 * g_hi.val := by
    rw [val_add_lt (by rw [hmul]; exact hside2), hmul]
  -- fixed helper: the one nonlinear step, identical in both copies
  have hprodlt : q.val * S.val < 2^42 * 2^18 :=
    calc q.val * S.val ≤ 2^42 * S.val := Nat.mul_le_mul_right _ hq
      _ < 2^42 * 2^18 := Nat.mul_lt_mul_of_pos_left hS (by positivity)
  have hside3 : q.val * S.val < P := by grind                              -- SITE 4
  have hprod : (q * S).val = q.val * S.val := val_mul_lt hside3
  rw [← hprod, hqS, hH, hsum]

/-- The production instance is an instance of the generic lemma (sanity: the
    two statements agree). -/
example {q S H g_lo g_hi : ZMod P}
    (hquad : q * S - H = 0) (hF : H - g_lo - 2^18 * g_hi = 0)
    (hq : q.val ≤ 2^42) (hS : S.val < 2^18) (hlo : g_lo.val < 2^18) (hhi : g_hi.val < 2^42) :
    q.val * S.val = g_lo.val + 2^18 * g_hi.val :=
  carry_stage_lift hquad hF hq hS hlo hhi (by norm_num [P]) (by norm_num [P])

end RmsNorm

#print axioms RmsNorm.carry_stage_lift
#print axioms RmsNorm.carry_stage_lift_production

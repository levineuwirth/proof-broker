/-
ir/CarryLiftDump.lean — CAPTURE ONLY, not a comparison subject.

`corpus/carrylift/CarryLiftPBTerm.lean` (byte-identical to the completed case
study's copy) with each `-- SITE n` closer replaced by `pb_dump_ir` + `omega`.
The imports, the file, the surrounding proof and the hypotheses in scope are
therefore exactly the ones `proof_broker_term` sees at that site; what is
dumped is the IR the production tactic would dispatch there. `omega` closes
each site, so this is a real elaboration of the real proof — the capture does
not stand in for a proof of anything.
-/
import RmsNormBracket.Model
import ProofBroker
import ProofBrokerMathlib
import PbDiag

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
  have h2L : (2:ℕ)^18 < P := by                             -- SITE 1
    pb_dump_ir "ir/O1.json"
    omega
  have hpow : ((2:ZMod P)^18).val = 2^18 := val_two_pow h2L
  have hside1 : 2^18 * g_hi.val < P := by                             -- SITE 2
    pb_dump_ir "ir/O2.json"
    omega
  have hmul : ((2:ZMod P)^18 * g_hi).val = 2^18 * g_hi.val := by
    rw [val_mul_lt (by rw [hpow]; exact hside1), hpow]
  have hside2 : g_lo.val + 2^18 * g_hi.val < P := by                             -- SITE 3
    pb_dump_ir "ir/O3.json"
    omega
  have hsum : (g_lo + (2:ZMod P)^18 * g_hi).val = g_lo.val + 2^18 * g_hi.val := by
    rw [val_add_lt (by rw [hmul]; exact hside2), hmul]
  -- fixed helper: the one nonlinear step, identical in both copies
  have hprodlt : q.val * S.val < 2^42 * 2^18 :=
    calc q.val * S.val ≤ 2^42 * S.val := Nat.mul_le_mul_right _ hq
      _ < 2^42 * 2^18 := Nat.mul_lt_mul_of_pos_left hS (by positivity)
  have hside3 : q.val * S.val < P := by                             -- SITE 4
    pb_dump_ir "ir/O4.json"
    omega
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

(** Helper lemmas for term-mode Tier 1 Farkas reconstruction.

    The plugin's term-mode closer ([rocq-bridge/src/term_mode.ml],
    surfaced as the [proof_broker_term] tactic) takes a Farkas
    witness JSON (coefficients keyed by hypothesis name) and builds
    an application of [farkas_le_n] from a goal-state-derived
    linear combination. The cert IS the proof, not a certificate
    that one exists. No call to [lia]/[lra] is made along this
    path; the closer's trust footprint is exactly these lemmas
    plus [ring] (used to discharge the polynomial identity that
    [c1*a1 + c2*a2 = K]).

    Everything here is axiom-free: only [Stdlib.ZArith.BinInt] and
    [Stdlib.ZArith.Zorder] are touched, plus [Pos2Z.is_pos] for the
    positive-Z ordering witnesses. [Print Assumptions] of any
    theorem that funnels through [farkas_le_n] reports "Closed
    under the global context".

    Arity scope: arity-2 [farkas_le_2] anchors the binary fixture;
    arities 3..N are handled by [farkas_contradict_n] over a
    left-associative sum the OCaml-side closer builds and discharges
    by [ring]. Comparison goals ([<=], [<], [>=], [>], [=]) reach
    the same fold via the wrapper helpers below ([z_le_via_lt] /
    [z_lt_via_le] for Z; [r_le_via_lt] / [r_lt_via_le] for R), which
    convert each goal shape to an implication-False whose body the
    closer recurses into. *)

From Stdlib Require Import ZArith Reals Arith.

Open Scope Z_scope.

(** Normalization helpers: convert direction-specific Z comparisons
    into the canonical [a - b <= 0] form the Farkas combine helper
    expects. Lets the OCaml-side plugin work uniformly without
    chasing Stdlib lemma-name drift across versions. *)
Lemma le_to_le0 (a b : Z) : a <= b -> a - b <= 0.
Proof. intros H. apply Z.sub_nonpos. exact H. Qed.

Lemma ge_to_le0 (a b : Z) : a >= b -> b - a <= 0.
Proof. intros H. apply Z.sub_nonpos. apply Z.ge_le. exact H. Qed.

(** Strict-[<] normalization, +1 trick: [a < b] over [Z] is equivalent
    to [a + 1 <= b] (discrete-domain), so the canonical [a' <= 0] form
    is [(a + 1) - b <= 0]. Matches the SDK's [lift_strict_pair] for
    LIA in [farkas.ml] — when the closer's [compute_residual] calls
    [compile_hypothesis] on a strict [<], it gets back [Le (a-b+1)]
    and the residual sum lines up with what the proof term emits. *)
Lemma lt_to_le0 (a b : Z) : a < b -> (a + 1) - b <= 0.
Proof.
  intros H.
  apply Z.sub_nonpos.
  rewrite Z.add_1_r.
  apply Z.le_succ_l.
  exact H.
Qed.

(** Mirror of [lt_to_le0] for [>]. Rocq's [Z.gt] doesn't reduce to
    swapped [<] (it's defined via [Z.compare]), so the +1 trick has
    to be re-applied here rather than going through [lt_to_le0]
    after a syntactic swap; we still delegate the heavy lifting. *)
Lemma gt_to_le0 (a b : Z) : a > b -> (b + 1) - a <= 0.
Proof. intros H. apply Z.gt_lt in H. exact (lt_to_le0 b a H). Qed.

Register le_to_le0 as proof_broker.term_mode.le_to_le0.
Register ge_to_le0 as proof_broker.term_mode.ge_to_le0.
Register lt_to_le0 as proof_broker.term_mode.lt_to_le0.
Register gt_to_le0 as proof_broker.term_mode.gt_to_le0.

(** Coefficient-witness builders. [Pos2Z.is_pos] is in Stdlib but
    isn't a registered [Rocqlib.lib_ref], so the plugin can't reach
    it directly; aliasing here under proof_broker.term_mode.* gives
    the plugin a stable handle. [pos_is_nonneg] composes it with
    [Z.lt_le_incl] to satisfy the [0 <= c_i] coefficient hypothesis
    in [farkas_le_n] — Tier 1 Farkas certs use non-negative integer
    coefficients (z3 emits them as [Zpos p]), so this is the
    coefficient-witness builder the OCaml side reaches for. *)
Lemma pos_is_pos (p : positive) : 0 < Zpos p.
Proof. exact (Pos2Z.is_pos p). Qed.

Lemma pos_is_nonneg (p : positive) : 0 <= Zpos p.
Proof. exact (Z.lt_le_incl _ _ (Pos2Z.is_pos p)). Qed.

Register pos_is_pos as proof_broker.term_mode.pos_is_pos.
Register pos_is_nonneg as proof_broker.term_mode.pos_is_nonneg.

(** Farkas combine, arity 2. Hypotheses are pre-normalized to
    [a <= 0] form by the OCaml side (via [le_to_le0] / [ge_to_le0]
    above). *)
Lemma farkas_le_2
  (a1 a2 : Z) (H1 : a1 <= 0) (H2 : a2 <= 0)
  (c1 c2 : Z) (Hc1 : 0 <= c1) (Hc2 : 0 <= c2)
  (K : Z) (HK : 0 < K) (Heq : c1 * a1 + c2 * a2 = K)
  : False.
Proof.
  assert (S1 : c1 * a1 <= 0) by (apply Z.mul_nonneg_nonpos; assumption).
  assert (S2 : c2 * a2 <= 0) by (apply Z.mul_nonneg_nonpos; assumption).
  assert (Ssum : c1 * a1 + c2 * a2 <= 0)
    by (apply Z.add_nonpos_nonpos; assumption).
  rewrite Heq in Ssum.
  exact (Z.lt_irrefl 0 (Z.lt_le_trans 0 K 0 HK Ssum)).
Qed.

(** Register hint so the OCaml-side plugin can resolve this lemma
    via [Rocqlib.lib_ref "proof_broker.term_mode.farkas_le_2"]. *)
Register farkas_le_2 as proof_broker.term_mode.farkas_le_2.

(** General-arity contradiction step. The OCaml-side closer builds
    [s = c1*a1 + c2*a2 + ... + cN*aN] (left-associative), proves
    [s <= 0] by folding [Z.mul_nonneg_nonpos] + [Z.add_nonpos_nonpos]
    over the entries, computes [K] numerically from the witness, and
    applies this lemma. The polynomial identity [s = K] is
    discharged by [ring] as before. Generalizes [farkas_le_2] to
    any arity (including 1, where the fold degenerates to a single
    product). *)
Lemma farkas_contradict_n
  (s K : Z) (Hs : s <= 0) (HK : 0 < K) (Heq : s = K) : False.
Proof.
  rewrite Heq in Hs.
  exact (Z.lt_irrefl 0 (Z.lt_le_trans 0 K 0 HK Hs)).
Qed.

(** Building blocks for the fold. Stable re-exports of Stdlib
    lemmas with names the OCaml side can resolve via [Rocqlib.lib_ref]
    (the Stdlib names aren't all registered as lib_refs). *)
Lemma z_mul_nonneg_nonpos (c a : Z) (Hc : 0 <= c) (Ha : a <= 0) : c * a <= 0.
Proof. apply Z.mul_nonneg_nonpos; assumption. Qed.

Lemma z_add_nonpos (x y : Z) (Hx : x <= 0) (Hy : y <= 0) : x + y <= 0.
Proof. apply Z.add_nonpos_nonpos; assumption. Qed.

Register farkas_contradict_n as proof_broker.term_mode.farkas_contradict_n.
Register z_mul_nonneg_nonpos as proof_broker.term_mode.z_mul_nonneg_nonpos.
Register z_add_nonpos as proof_broker.term_mode.z_add_nonpos.

(** Arity-N comparison-goal wrappers (Z). Convert a comparison goal
    into an implication-False shape so the closer can introduce the
    negated goal as a regular hypothesis and delegate to the existing
    arity-N False-fold; the same fold then consumes [neg_goal]
    alongside the witness's real-hypothesis entries at any arity.

    Soundness rests on constructive decidability of [<=] / [<] on
    [Z] ([Z_le_gt_dec] / [Z_lt_ge_dec], both from Stdlib's
    [ZArith]). *)
Lemma z_le_via_lt (b c : Z) (H : c < b -> False) : b <= c.
Proof.
  destruct (Z_le_gt_dec b c) as [Hle | Hgt]; [exact Hle | exfalso].
  apply Z.gt_lt in Hgt.
  exact (H Hgt).
Qed.

Lemma z_lt_via_le (b c : Z) (H : c <= b -> False) : b < c.
Proof.
  destruct (Z_lt_ge_dec b c) as [Hlt | Hge]; [exact Hlt | exfalso].
  apply Z.ge_le in Hge.
  exact (H Hge).
Qed.

Register z_le_via_lt as proof_broker.term_mode.z_le_via_lt.
Register z_lt_via_le as proof_broker.term_mode.z_lt_via_le.

(** Eq-hypothesis normalization (Z). From [h : a = b], produce
    [a - b <= 0]. The contribution is exactly 0 (since [a - b = 0]
    from [h]), but the symbolic Le-form lets Eq hypotheses fold
    into the strict-aware Le-only fold without special-casing the
    contradiction step. Solver-emitted certs apply signed
    coefficients on Eq hypotheses to capture both directions of an
    equality in a single witness slot; for negative coefficients
    the closer routes through [z_eq_to_le0_flipped] (below) to get
    the [b - a <= 0] direction, keeping the closer's positive-
    coefficient invariant on inequality premises. *)
Lemma z_eq_to_le0 (a b : Z) (h : a = b) : a - b <= 0.
Proof. subst. rewrite Z.sub_diag. apply Z.le_refl. Qed.

(** Flipped variant for negative coefficients on Eq hypotheses:
    same lemma applied to [eq_sym h]. Folded into a single helper
    so the OCaml-side closer doesn't need to plumb [eq_sym]'s
    [lib_ref]. *)
Lemma z_eq_to_le0_flipped (a b : Z) (h : a = b) : b - a <= 0.
Proof. subst. rewrite Z.sub_diag. apply Z.le_refl. Qed.

Register z_eq_to_le0 as proof_broker.term_mode.z_eq_to_le0.
Register z_eq_to_le0_flipped as proof_broker.term_mode.z_eq_to_le0_flipped.

(** Not-hypothesis normalization (Z). Solver-emitted certs can
    reference hypotheses in negated form `(h : ~ a <= b)` etc. —
    the SDK accepts these via [Farkas.compile_hypothesis]'s [Not]
    branch, which compiles `~ (a <= b)` to `b < a` (strict, then
    folded via the LIA +1 trick to `(b + 1) - a <= 0`). The bridge
    closer applies one of these helpers based on the inner head of
    the negation. All four route through existing helpers, keeping
    the axiom-free trust footprint. *)
Lemma z_not_le_to_le0 (a b : Z) (h : ~ a <= b) : (b + 1) - a <= 0.
Proof. apply lt_to_le0. apply Z.gt_lt. apply Znot_le_gt. exact h. Qed.

Lemma z_not_ge_to_le0 (a b : Z) (h : ~ a >= b) : (a + 1) - b <= 0.
Proof. apply lt_to_le0. apply Znot_ge_lt. exact h. Qed.

Lemma z_not_lt_to_le0 (a b : Z) (h : ~ a < b) : b - a <= 0.
Proof. apply le_to_le0. apply Z.ge_le. apply Znot_lt_ge. exact h. Qed.

Lemma z_not_gt_to_le0 (a b : Z) (h : ~ a > b) : a - b <= 0.
Proof. apply le_to_le0. apply Znot_gt_le. exact h. Qed.

Register z_not_le_to_le0 as proof_broker.term_mode.z_not_le_to_le0.
Register z_not_ge_to_le0 as proof_broker.term_mode.z_not_ge_to_le0.
Register z_not_lt_to_le0 as proof_broker.term_mode.z_not_lt_to_le0.
Register z_not_gt_to_le0 as proof_broker.term_mode.z_not_gt_to_le0.

(** ============================================================
    Real-typed (LRA) Tier 1 Farkas reconstruction.

    Mirror of the Z-typed helpers above, scaled up to [R]. The
    [r_farkas_le_2] helper is the load-bearing lemma for the Tier 2
    case-split closer (term_mode.ml::close_term_case_split): each
    branch's proof term is [r_farkas_le_2] applied to the matching
    lemma's Farkas coefficients, with the case hypothesis introduced
    by [destruct] flowing through as the second [<= 0] premise.

    Direct Stdlib R lemmas only — no [lra] tactic inside the helper
    proofs themselves, so the trust footprint stays narrow (the same
    way the Z helpers use [Z.mul_nonneg_nonpos] etc. directly rather
    than [lia]). [lra] elsewhere (the existing [proof_broker]
    decide-procedure LRA closer) is unaffected. *)

Open Scope R_scope.

Lemma r_le_to_le0 (a b : R) : a <= b -> a - b <= 0.
Proof.
  intros H.
  apply (Rplus_le_compat_r (- b)) in H.
  rewrite Rplus_opp_r in H.
  unfold Rminus. exact H.
Qed.

Lemma r_ge_to_le0 (a b : R) : a >= b -> b - a <= 0.
Proof. intros H. apply r_le_to_le0. apply Rge_le. exact H. Qed.

Register r_le_to_le0 as proof_broker.term_mode.r_le_to_le0.
Register r_ge_to_le0 as proof_broker.term_mode.r_ge_to_le0.

Lemma r_mul_nonneg_nonpos (c a : R) (Hc : 0 <= c) (Ha : a <= 0) : c * a <= 0.
Proof.
  rewrite <- (Rmult_0_r c).
  apply Rmult_le_compat_l; assumption.
Qed.

Lemma r_farkas_le_2
  (a1 a2 : R) (H1 : a1 <= 0) (H2 : a2 <= 0)
  (c1 c2 : R) (Hc1 : 0 <= c1) (Hc2 : 0 <= c2)
  (K : R) (HK : 0 < K) (Heq : c1 * a1 + c2 * a2 = K)
  : False.
Proof.
  assert (S1 : c1 * a1 <= 0) by (apply r_mul_nonneg_nonpos; assumption).
  assert (S2 : c2 * a2 <= 0) by (apply r_mul_nonneg_nonpos; assumption).
  assert (Ssum : c1 * a1 + c2 * a2 <= 0).
  { rewrite <- Rplus_0_r. apply Rplus_le_compat; assumption. }
  rewrite Heq in Ssum.
  exact (Rlt_irrefl 0 (Rlt_le_trans 0 K 0 HK Ssum)).
Qed.

Register r_farkas_le_2 as proof_broker.term_mode.r_farkas_le_2.

(** General-arity Real contradiction step. Mirror of
    [farkas_contradict_n] over [R], used by the Tier 1 Farkas + Tier 2
    case-split closers on LRA goals when the witness exceeds arity 2. *)
Lemma r_farkas_contradict_n
  (s K : R) (Hs : s <= 0) (HK : 0 < K) (Heq : s = K) : False.
Proof.
  rewrite Heq in Hs.
  exact (Rlt_irrefl 0 (Rlt_le_trans 0 K 0 HK Hs)).
Qed.

(** Real-typed building blocks for the fold. *)
Lemma r_add_nonpos (x y : R) (Hx : x <= 0) (Hy : y <= 0) : x + y <= 0.
Proof.
  rewrite <- Rplus_0_r.
  apply Rplus_le_compat; assumption.
Qed.

Register r_farkas_contradict_n as proof_broker.term_mode.r_farkas_contradict_n.
Register r_mul_nonneg_nonpos as proof_broker.term_mode.r_mul_nonneg_nonpos.
Register r_add_nonpos as proof_broker.term_mode.r_add_nonpos.

(** Real-typed positive-literal coefficient witness: a closed positive
    rational [p/q] flows through as [0 < IZR p / IZR q] (or [0 < IZR n]
    for integer coefficients). The Tier 2 case-split path uses
    integer coefficients today (cvc5's [la_generic :args (1/1 1/1 1/1)]
    in the fixture), so this lemma covers the [Zpos]-derived
    coefficient slot via a trivial [<-] reduction; the OCaml side
    constructs the matching [IZR (Zpos p)] EConstr and the proof
    follows. *)
Lemma r_pos_is_pos (p : positive) : 0 < IZR (Zpos p).
Proof. apply IZR_lt. exact (Pos2Z.is_pos p). Qed.

Lemma r_pos_is_nonneg (p : positive) : 0 <= IZR (Zpos p).
Proof. apply Rlt_le. exact (r_pos_is_pos p). Qed.

Register r_pos_is_pos as proof_broker.term_mode.r_pos_is_pos.
Register r_pos_is_nonneg as proof_broker.term_mode.r_pos_is_nonneg.

(** Real-typed [0 <= 0] witness. Needed for the LRA closer when the
    Farkas residual [K] is exactly zero (the trivial-equality case
    [n <= 5 ⊢ n <= 5] post-Rle_antisym): there's no [+1] trick over R
    to push [K] strictly positive, so the strict-aware fold takes
    [0 <= K] and that premise has to be built for [K = 0] specifically
    (the existing [r_pos_is_nonneg] only builds [0 <= IZR (Zpos p)]
    for [p : positive] — no zero representation). *)
Lemma r_zero_nonneg : (0 <= 0)%R.
Proof. apply Rle_refl. Qed.

Register r_zero_nonneg as proof_broker.term_mode.r_zero_nonneg.

(** Strict-[<] hypothesis normalization for R: produce [a - b < 0]
    (strict) rather than the [le0]-style weakening. The Z-side
    [lt_to_le0] uses the LIA +1 trick to fold strictness into [Le];
    there's no analog over R, so the strict-aware fold path
    preserves [<] all the way to the contradiction step. *)
Lemma r_lt_to_lt0 (a b : R) : a < b -> a - b < 0.
Proof. intros H. apply Rlt_minus. exact H. Qed.

Lemma r_gt_to_lt0 (a b : R) : a > b -> b - a < 0.
Proof. intros H. apply Rgt_lt in H. apply Rlt_minus. exact H. Qed.

Register r_lt_to_lt0 as proof_broker.term_mode.r_lt_to_lt0.
Register r_gt_to_lt0 as proof_broker.term_mode.r_gt_to_lt0.

(** Strict-aware Farkas building blocks. The fold tracks strictness
    state per accumulator step; each combination (Le+Le | Le+Lt | Lt+Le
    | Lt+Lt) picks the matching [add_*] lemma. Once any premise is
    strict, the result is strict (Lt-preserving). The dispatch at the
    end of the fold picks between [r_farkas_contradict_n] (all Le
    premises, requires [0 < K]) and [r_farkas_contradict_n_strict]
    (at least one Lt premise with positive coefficient, allows
    [0 ≤ K]). *)
Lemma r_mul_pos_neg (c a : R) (Hc : 0 < c) (Ha : a < 0) : c * a < 0.
Proof.
  apply (Rmult_lt_compat_l c a 0 Hc) in Ha.
  rewrite Rmult_0_r in Ha.
  exact Ha.
Qed.

Lemma r_add_le_lt (x y : R) (Hx : x <= 0) (Hy : y < 0) : x + y < 0.
Proof.
  replace 0 with (0 + 0) by ring.
  apply Rplus_le_lt_compat; assumption.
Qed.

Lemma r_add_lt_le (x y : R) (Hx : x < 0) (Hy : y <= 0) : x + y < 0.
Proof.
  replace 0 with (0 + 0) by ring.
  apply Rplus_lt_le_compat; assumption.
Qed.

Lemma r_add_neg (x y : R) (Hx : x < 0) (Hy : y < 0) : x + y < 0.
Proof.
  replace 0 with (0 + 0) by ring.
  apply Rplus_lt_compat; assumption.
Qed.

(** Strict-aware contradiction step. Counterpart to
    [r_farkas_contradict_n] (which takes [Hs : s <= 0] and [HK : 0 < K]):
    here the strict premise comes from at least one [Lt]-compiled
    hypothesis with positive coefficient, giving [s < 0]; in exchange
    [K] only needs to be non-negative (a Farkas residual of exactly
    zero is fine when strictness carries the contradiction, eg
    [(h1 : 5 < x) (h2 : x < 5) ⊢ False] where the linear combination
    constant is zero but the inequality is strict). *)
Lemma r_farkas_contradict_n_strict
  (s K : R) (Hs : s < 0) (HK : 0 <= K) (Heq : s = K) : False.
Proof.
  rewrite Heq in Hs.
  (* Hs : K < 0 *)
  exact (Rlt_irrefl 0 (Rle_lt_trans 0 K 0 HK Hs)).
Qed.

Register r_mul_pos_neg as proof_broker.term_mode.r_mul_pos_neg.
Register r_add_le_lt as proof_broker.term_mode.r_add_le_lt.
Register r_add_lt_le as proof_broker.term_mode.r_add_lt_le.
Register r_add_neg as proof_broker.term_mode.r_add_neg.
Register r_farkas_contradict_n_strict
  as proof_broker.term_mode.r_farkas_contradict_n_strict.

(** Arity-N comparison-goal wrappers (R). Mirror of [z_le_via_lt] /
    [z_lt_via_le] over the reals. Uses [Rle_dec] / [Rlt_dec] for
    constructive decidability, both from [Stdlib.Reals]. *)
Lemma r_le_via_lt (b c : R) (H : c < b -> False) : b <= c.
Proof.
  destruct (Rle_dec b c) as [Hle | Hngt]; [exact Hle | exfalso].
  apply Rnot_le_lt in Hngt.
  exact (H Hngt).
Qed.

Lemma r_lt_via_le (b c : R) (H : c <= b -> False) : b < c.
Proof.
  destruct (Rlt_dec b c) as [Hlt | Hnlt]; [exact Hlt | exfalso].
  apply Rnot_lt_le in Hnlt.
  exact (H Hnlt).
Qed.

Register r_le_via_lt as proof_broker.term_mode.r_le_via_lt.
Register r_lt_via_le as proof_broker.term_mode.r_lt_via_le.

(** Eq-hypothesis normalization (R). Mirror of [z_eq_to_le0] over
    the reals. *)
Lemma r_eq_to_le0 (a b : R) (h : a = b) : (a - b <= 0)%R.
Proof. subst. rewrite Rminus_diag. apply Rle_refl. Qed.

(** Flipped variant for negative coefficients on Eq hypotheses
    over R. *)
Lemma r_eq_to_le0_flipped (a b : R) (h : a = b) : (b - a <= 0)%R.
Proof. subst. rewrite Rminus_diag. apply Rle_refl. Qed.

Register r_eq_to_le0 as proof_broker.term_mode.r_eq_to_le0.
Register r_eq_to_le0_flipped as proof_broker.term_mode.r_eq_to_le0_flipped.

(** Not-hypothesis normalization (R). Mirror of [z_not_le_to_le0]
    family over the reals. Strictness is preserved (no +1 trick over
    R) — the strict inner inequality from negation reaches the
    closer's strict-aware fold via [Rlt_minus]; the loose forms route
    through the existing [r_le_to_le0]. *)
Lemma r_not_le_to_lt0 (a b : R) (h : ~ (a <= b)%R) : (b - a < 0)%R.
Proof. apply Rlt_minus. apply Rnot_le_lt. exact h. Qed.

Lemma r_not_ge_to_lt0 (a b : R) (h : ~ (a >= b)%R) : (a - b < 0)%R.
Proof. apply Rlt_minus. apply Rnot_ge_lt. exact h. Qed.

Lemma r_not_lt_to_le0 (a b : R) (h : ~ (a < b)%R) : (b - a <= 0)%R.
Proof. apply r_le_to_le0. apply Rnot_lt_le. exact h. Qed.

Lemma r_not_gt_to_le0 (a b : R) (h : ~ (a > b)%R) : (a - b <= 0)%R.
Proof. apply r_le_to_le0. apply Rnot_gt_le. exact h. Qed.

Register r_not_le_to_lt0 as proof_broker.term_mode.r_not_le_to_lt0.
Register r_not_ge_to_lt0 as proof_broker.term_mode.r_not_ge_to_lt0.
Register r_not_lt_to_le0 as proof_broker.term_mode.r_not_lt_to_le0.
Register r_not_gt_to_le0 as proof_broker.term_mode.r_not_gt_to_le0.

Close Scope R_scope.

Open Scope Z_scope.

(** Trust-footprint check: every helper above closes under the
    global context (axiom-free). Build-time [Print Assumptions]
    surfaces this in the dune output. The [Print <name>.] line
    immediately preceding each is the marker that
    [tools/check_axioms.py] uses to pair theorem names with their
    [Print Assumptions] block — Rocq's [Print Assumptions] alone
    doesn't include the theorem name in its output, so we need
    the explicit [Print] to anchor the parse. *)
(* ============================================================
   R3-M1: ℕ→ℤ push-cast + transfer shims.

   The ℕ lift casts every witness-named ℕ hypothesis to its ℤ image
   by TERM CONSTRUCTION before the Z Farkas fold runs. Unlike Lean
   (where core's cast-distribution lemmas are `rfl` and kernel
   defeq folds the cast through +/*/literals), Coq's [Z.of_nat]
   does not reduce on open terms — so the push is explicit: each
   shim takes the pushed forms [za]/[zb] together with push
   equations [Z.of_nat a = za] (built recursively from the
   [nat_push_*] lemmas; [eq_refl] at leaves), and transfers the ℕ
   fact through [Nat2Z]. Everything is constructive — [Print
   Assumptions] below pins the whole family "Closed under the
   global context", which is what keeps the ℕ term-mode footprint
   EMPTY (the M1 Rocq gate).
   ============================================================ *)

Lemma nat_push_add (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb) :
  Z.of_nat (a + b) = za + zb.
Proof. subst; apply Nat2Z.inj_add. Qed.

Lemma nat_push_mul (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb) :
  Z.of_nat (a * b) = za * zb.
Proof. subst; apply Nat2Z.inj_mul. Qed.

(* The pow case carries the FOLDED literal: the reifier emits
   [2^24] as the numeral 16777216, and [H] is discharged by
   [eq_refl] at application time — [Z.pow] on binary literals is
   kernel-cheap, where normalizing [Z.of_nat (2^24)] through the
   unary numeral would not be. *)
Lemma nat_push_pow (a b : nat) (z : Z)
  (H : (Z.of_nat a) ^ (Z.of_nat b) = z) :
  Z.of_nat (a ^ b) = z.
Proof. subst; apply Nat2Z.inj_pow. Qed.

Lemma nat_cast_le (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb)
  (H : (a <= b)%nat) : za <= zb.
Proof. subst; exact (proj1 (Nat2Z.inj_le a b) H). Qed.

Lemma nat_cast_lt (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb)
  (H : (a < b)%nat) : za < zb.
Proof. subst; exact (proj1 (Nat2Z.inj_lt a b) H). Qed.

(* [ge]/[gt] at nat are definitionally the swapped [le]/[lt]; the
   shims emit the swapped Z form directly (the IR reifier swapped
   the operands the same way). *)
Lemma nat_cast_ge (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb)
  (H : (a >= b)%nat) : zb <= za.
Proof. subst; exact (proj1 (Nat2Z.inj_le b a) H). Qed.

Lemma nat_cast_gt (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb)
  (H : (a > b)%nat) : zb < za.
Proof. subst; exact (proj1 (Nat2Z.inj_lt b a) H). Qed.

Lemma nat_cast_eq (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb)
  (H : a = b) : za = zb.
Proof. subst za zb. now rewrite H. Qed.

Lemma nat_cast_not_le (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb)
  (H : ~ (a <= b)%nat) : ~ (za <= zb).
Proof. subst; intro hz; exact (H (proj2 (Nat2Z.inj_le a b) hz)). Qed.

Lemma nat_cast_not_lt (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb)
  (H : ~ (a < b)%nat) : ~ (za < zb).
Proof. subst; intro hz; exact (H (proj2 (Nat2Z.inj_lt a b) hz)). Qed.

Lemma nat_cast_not_ge (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb)
  (H : ~ (a >= b)%nat) : ~ (zb <= za).
Proof. subst; intro hz; exact (H (proj2 (Nat2Z.inj_le b a) hz)). Qed.

Lemma nat_cast_not_gt (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb)
  (H : ~ (a > b)%nat) : ~ (zb < za).
Proof. subst; intro hz; exact (H (proj2 (Nat2Z.inj_lt b a) hz)). Qed.

Lemma nat_cast_not_eq (a b : nat) (za zb : Z)
  (Ha : Z.of_nat a = za) (Hb : Z.of_nat b = zb)
  (H : a <> b) : za <> zb.
Proof. subst; intro hz; exact (H (Nat2Z.inj _ _ hz)). Qed.

(* One nonneg fact per ℕ atom — the ℤ image of what the reifier's
   [_pb_nonneg_*] hypotheses assert. *)
Lemma nat_cast_nonneg (a : nat) (za : Z)
  (Ha : Z.of_nat a = za) : 0 <= za.
Proof. subst; apply Nat2Z.is_nonneg. Qed.

(* ℕ comparison-goal wrappers (mirror of [z_le_via_lt]/[z_lt_via_le],
   constructive via [le_lt_dec]). -*)
Lemma nat_le_via_lt (b c : nat) (H : (c < b)%nat -> False) : (b <= c)%nat.
Proof.
  destruct (le_lt_dec b c) as [Hle | Hgt]; [exact Hle | exfalso].
  exact (H Hgt).
Qed.

Lemma nat_lt_via_le (b c : nat) (H : (c <= b)%nat -> False) : (b < c)%nat.
Proof.
  destruct (le_lt_dec c b) as [Hle | Hgt]; [exfalso; exact (H Hle) | exact Hgt].
Qed.

Register nat_push_add as proof_broker.term_mode.nat_push_add.
Register nat_push_mul as proof_broker.term_mode.nat_push_mul.
Register nat_push_pow as proof_broker.term_mode.nat_push_pow.
Register nat_cast_le as proof_broker.term_mode.nat_cast_le.
Register nat_cast_lt as proof_broker.term_mode.nat_cast_lt.
Register nat_cast_ge as proof_broker.term_mode.nat_cast_ge.
Register nat_cast_gt as proof_broker.term_mode.nat_cast_gt.
Register nat_cast_eq as proof_broker.term_mode.nat_cast_eq.
Register nat_cast_not_le as proof_broker.term_mode.nat_cast_not_le.
Register nat_cast_not_lt as proof_broker.term_mode.nat_cast_not_lt.
Register nat_cast_not_ge as proof_broker.term_mode.nat_cast_not_ge.
Register nat_cast_not_gt as proof_broker.term_mode.nat_cast_not_gt.
Register nat_cast_not_eq as proof_broker.term_mode.nat_cast_not_eq.
Register nat_cast_nonneg as proof_broker.term_mode.nat_cast_nonneg.
Register nat_le_via_lt as proof_broker.term_mode.nat_le_via_lt.
Register nat_lt_via_le as proof_broker.term_mode.nat_lt_via_le.

Print farkas_le_2.
Print Assumptions farkas_le_2.

Print le_to_le0.
Print Assumptions le_to_le0.

Print ge_to_le0.
Print Assumptions ge_to_le0.

Print lt_to_le0.
Print Assumptions lt_to_le0.

Print gt_to_le0.
Print Assumptions gt_to_le0.

Print pos_is_pos.
Print Assumptions pos_is_pos.

Print pos_is_nonneg.
Print Assumptions pos_is_nonneg.

Print r_farkas_le_2.
Print Assumptions r_farkas_le_2.

Print r_le_to_le0.
Print Assumptions r_le_to_le0.

Print r_ge_to_le0.
Print Assumptions r_ge_to_le0.

Print r_pos_is_pos.
Print Assumptions r_pos_is_pos.

Print r_pos_is_nonneg.
Print Assumptions r_pos_is_nonneg.

Print r_zero_nonneg.
Print Assumptions r_zero_nonneg.

Print r_lt_to_lt0.
Print Assumptions r_lt_to_lt0.

Print r_gt_to_lt0.
Print Assumptions r_gt_to_lt0.

Print r_mul_pos_neg.
Print Assumptions r_mul_pos_neg.

Print r_add_le_lt.
Print Assumptions r_add_le_lt.

Print r_add_lt_le.
Print Assumptions r_add_lt_le.

Print r_add_neg.
Print Assumptions r_add_neg.

Print r_farkas_contradict_n_strict.
Print Assumptions r_farkas_contradict_n_strict.

Print farkas_contradict_n.
Print Assumptions farkas_contradict_n.

Print z_mul_nonneg_nonpos.
Print Assumptions z_mul_nonneg_nonpos.

Print z_add_nonpos.
Print Assumptions z_add_nonpos.

Print r_farkas_contradict_n.
Print Assumptions r_farkas_contradict_n.

Print r_add_nonpos.
Print Assumptions r_add_nonpos.

Print z_le_via_lt.
Print Assumptions z_le_via_lt.

Print z_lt_via_le.
Print Assumptions z_lt_via_le.

Print r_le_via_lt.
Print Assumptions r_le_via_lt.

Print r_lt_via_le.
Print Assumptions r_lt_via_le.

Print z_eq_to_le0.
Print Assumptions z_eq_to_le0.

Print z_eq_to_le0_flipped.
Print Assumptions z_eq_to_le0_flipped.

Print r_eq_to_le0.
Print Assumptions r_eq_to_le0.

Print r_eq_to_le0_flipped.
Print Assumptions r_eq_to_le0_flipped.

Print z_not_le_to_le0.
Print Assumptions z_not_le_to_le0.

Print z_not_ge_to_le0.
Print Assumptions z_not_ge_to_le0.

Print z_not_lt_to_le0.
Print Assumptions z_not_lt_to_le0.

Print z_not_gt_to_le0.
Print Assumptions z_not_gt_to_le0.

Print r_not_le_to_lt0.
Print Assumptions r_not_le_to_lt0.

Print r_not_ge_to_lt0.
Print Assumptions r_not_ge_to_lt0.

Print r_not_lt_to_le0.
Print Assumptions r_not_lt_to_le0.

Print r_not_gt_to_le0.
Print Assumptions r_not_gt_to_le0.

Print nat_push_add.
Print Assumptions nat_push_add.

Print nat_push_mul.
Print Assumptions nat_push_mul.

Print nat_push_pow.
Print Assumptions nat_push_pow.

Print nat_cast_le.
Print Assumptions nat_cast_le.

Print nat_cast_lt.
Print Assumptions nat_cast_lt.

Print nat_cast_ge.
Print Assumptions nat_cast_ge.

Print nat_cast_gt.
Print Assumptions nat_cast_gt.

Print nat_cast_eq.
Print Assumptions nat_cast_eq.

Print nat_cast_not_le.
Print Assumptions nat_cast_not_le.

Print nat_cast_not_lt.
Print Assumptions nat_cast_not_lt.

Print nat_cast_not_ge.
Print Assumptions nat_cast_not_ge.

Print nat_cast_not_gt.
Print Assumptions nat_cast_not_gt.

Print nat_cast_not_eq.
Print Assumptions nat_cast_not_eq.

Print nat_cast_nonneg.
Print Assumptions nat_cast_nonneg.

Print nat_le_via_lt.
Print Assumptions nat_le_via_lt.

Print nat_lt_via_le.
Print Assumptions nat_lt_via_le.

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

    Arity scope: arity 2 only today, matching the smallest non-
    trivial Farkas cert (e.g. example1's [forall x : Z, x >= 5 ->
    x <= 3 -> False] with witness [(H2,1); (H1,1)]). Arities 3..N
    are mechanical copies of [farkas_le_2] — write them when a
    cert in practice exceeds arity 2.

    Goal-shape scope: [False], [<=], [<] handled directly here;
    [>=] / [>] / [=] handled at the closer level (pb_rocq_main.ml)
    by applying [Z.le_ge] / [Z.lt_gt] / [Z.le_antisymm] first, so
    the recursive descent lands in one of the three shapes above.
    Mirrors Lean's design except Lean's [GE.ge a b ↘ LE.le b a]
    reduces by instance — Rocq's [Z.ge] is defined via [Z.compare]
    rather than as an alias, so the explicit normalization step is
    required. *)

From Stdlib Require Import ZArith Reals.

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

(** Farkas reconstruction for a non-[False] goal of shape [b <= c].
    Mirror of Lean's [farkasGoalLe2] from [ProofBroker.TermMode] —
    wraps the constructive decidability witness [Z_le_gt_dec], then
    normalizes the negated goal [c < b] through [c + 1 <= b]
    ([Z.le_succ_l] + [Z.add_1_r]) to the SDK's compiled
    [Le (c + 1 - b)] shape (the LIA +1-trick image of [¬(b <= c)]).
    Delegates to [farkas_le_2] with arity 2: one real hypothesis
    (the [a1] slot) plus the synthetic neg-goal slot.
    The [Heq] premise (polynomial identity [c1*a1 + cng*(c+1-b) = K])
    is discharged by [ring] at closer-build time, just as in
    [farkas_le_2]. *)
Lemma farkas_le_goal_2
  (b c : Z) (a1 : Z) (H1 : a1 <= 0)
  (c1 cng : Z) (Hc1 : 0 <= c1) (Hcng : 0 <= cng)
  (K : Z) (HK : 0 < K)
  (Heq : c1 * a1 + cng * (c + 1 - b) = K)
  : b <= c.
Proof.
  destruct (Z_le_gt_dec b c) as [Hle | Hgt]; [exact Hle | exfalso].
  apply Z.gt_lt in Hgt.
  apply Z.le_succ_l in Hgt.
  rewrite <- Z.add_1_r in Hgt.
  apply (proj2 (Z.sub_nonpos (c + 1) b)) in Hgt.
  exact (farkas_le_2 a1 (c + 1 - b) H1 Hgt c1 cng Hc1 Hcng K HK Heq).
Qed.

(** Farkas reconstruction for a strict goal [b < c]. Same shape as
    [farkas_le_goal_2] but without the +1 trick — [~ (b < c)] becomes
    [c <= b] directly via [Z_lt_ge_dec] + [Z.ge_le], so the synthetic
    neg-goal slot compiles to [Le (c - b)]. Matches the SDK's
    [lift_le_pair c b] for the negation of [LT.lt b c].

    [>=] and [>] over [Z] do NOT reduce to swapped [<=] / [<] the
    way Lean's instance reduction does (Rocq's [Z.ge] / [Z.gt] are
    defined via [Z.compare] rather than as aliases). The Rocq closer
    [pb_rocq_main.run_close_term] handles them by applying
    [Z.le_ge] / [Z.lt_gt] first, leaving a [<=] / [<] subgoal that
    routes through these two helpers. *)
Lemma farkas_lt_goal_2
  (b c : Z) (a1 : Z) (H1 : a1 <= 0)
  (c1 cng : Z) (Hc1 : 0 <= c1) (Hcng : 0 <= cng)
  (K : Z) (HK : 0 < K)
  (Heq : c1 * a1 + cng * (c - b) = K)
  : b < c.
Proof.
  destruct (Z_lt_ge_dec b c) as [Hlt | Hge]; [exact Hlt | exfalso].
  apply Z.ge_le in Hge.
  apply (proj2 (Z.sub_nonpos c b)) in Hge.
  exact (farkas_le_2 a1 (c - b) H1 Hge c1 cng Hc1 Hcng K HK Heq).
Qed.

Register farkas_le_goal_2 as proof_broker.term_mode.farkas_le_goal_2.
Register farkas_lt_goal_2 as proof_broker.term_mode.farkas_lt_goal_2.

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

(** Real-typed Farkas reconstruction for a non-[False] goal of shape
    [b <= c]. The signature is strict-aware: [Hcng : 0 < cng] (strict
    coefficient on the neg_goal slot) and [HK : 0 <= K] (non-strict
    residual). Over R the negation of [b <= c] is the strict
    [c < b] (compiled by the SDK as [Lt (c - b)] under LRA), and the
    Farkas combination from a strict premise with a positive coefficient
    is itself strictly less than 0. That strictness is what produces
    the contradiction against [0 <= K] — even when [K = 0], the
    trivial-equality case ([n <= 5] ⊢ [n <= 5] gives [(n-5)+(5-n) = 0]).
    The Z-side helper [farkas_le_goal_2] doesn't need this because
    the LIA +1 trick shifts the residual to [K > 0]; over R there's
    no such shift, so the strictness path is load-bearing.

    The decider is constructive over R ([Rle_dec] from [Stdlib.Reals]),
    so no [Classical] beyond what [r_farkas_le_2] already pulls in.
    The [Heq] premise (polynomial identity [c1*a1 + cng*(c-b) = K])
    is discharged by [ring] at closer-build time. *)
Lemma r_farkas_le_goal_2
  (b c : R) (a1 : R) (H1 : a1 <= 0)
  (c1 cng : R) (Hc1 : 0 <= c1) (Hcng : 0 < cng)
  (K : R) (HK : 0 <= K)
  (Heq : c1 * a1 + cng * (c - b) = K)
  : b <= c.
Proof.
  destruct (Rle_dec b c) as [Hle | Hngt]; [exact Hle | exfalso].
  apply Rnot_le_lt in Hngt.
  (* Hngt : c < b *)
  assert (S1 : c1 * a1 <= 0)
    by (apply r_mul_nonneg_nonpos; assumption).
  assert (S2 : cng * (c - b) < 0).
  { apply (Rmult_lt_compat_l cng c b Hcng) in Hngt.
    (* Hngt : cng * c < cng * b *)
    replace (cng * (c - b)) with (cng * c - cng * b) by ring.
    apply Rlt_minus. exact Hngt. }
  assert (Ssum : c1 * a1 + cng * (c - b) < 0).
  { replace 0 with (0 + 0) by ring.
    apply Rplus_le_lt_compat; assumption. }
  rewrite Heq in Ssum.
  (* Ssum : K < 0 *)
  exact (Rlt_irrefl 0 (Rle_lt_trans 0 K 0 HK Ssum)).
Qed.

(** Real-typed Farkas reconstruction for a strict goal [b < c]. The
    negation of [b < c] over R is [c <= b] directly (no strictness
    flip, no +1), which [Rnot_lt_le] gives us, and [r_le_to_le0]
    normalizes to [c - b <= 0]. The compiled neg-goal shape thus
    matches [Le (c - b)] — same as the SDK's [lift_le_pair c b]
    output for [Not (LT.lt b c)] under any fragment. *)
Lemma r_farkas_lt_goal_2
  (b c : R) (a1 : R) (H1 : a1 <= 0)
  (c1 cng : R) (Hc1 : 0 <= c1) (Hcng : 0 <= cng)
  (K : R) (HK : 0 < K)
  (Heq : c1 * a1 + cng * (c - b) = K)
  : b < c.
Proof.
  destruct (Rlt_dec b c) as [Hlt | Hnlt]; [exact Hlt | exfalso].
  apply Rnot_lt_le in Hnlt.
  (* Hnlt : c <= b *)
  pose proof (r_le_to_le0 c b Hnlt) as H2.
  exact (r_farkas_le_2 a1 (c - b) H1 H2 c1 cng Hc1 Hcng K HK Heq).
Qed.

Register r_farkas_le_goal_2 as proof_broker.term_mode.r_farkas_le_goal_2.
Register r_farkas_lt_goal_2 as proof_broker.term_mode.r_farkas_lt_goal_2.

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

(** Real-typed [0 <= 0] witness. Needed for the LRA Le-goal closer
    when the Farkas residual [K] is exactly zero (the trivial-equality
    case [n <= 5 ⊢ n <= 5] post-Rle_antisym): there's no [+1] trick
    over R to push [K] strictly positive, so the strict-aware
    [r_farkas_le_goal_2] takes [0 <= K] and that premise has to be
    built for [K = 0] specifically (the existing [r_pos_is_nonneg]
    only builds [0 <= IZR (Zpos p)] for [p : positive] — no zero
    representation). *)
Lemma r_zero_nonneg : (0 <= 0)%R.
Proof. apply Rle_refl. Qed.

Register r_zero_nonneg as proof_broker.term_mode.r_zero_nonneg.

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
Print farkas_le_2.
Print Assumptions farkas_le_2.

Print farkas_le_goal_2.
Print Assumptions farkas_le_goal_2.

Print farkas_lt_goal_2.
Print Assumptions farkas_lt_goal_2.

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

Print r_farkas_le_goal_2.
Print Assumptions r_farkas_le_goal_2.

Print r_farkas_lt_goal_2.
Print Assumptions r_farkas_lt_goal_2.

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

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
    cert in practice exceeds arity 2. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

(** Normalization helpers: convert direction-specific Z comparisons
    into the canonical [a - b <= 0] form the Farkas combine helper
    expects. Lets the OCaml-side plugin work uniformly without
    chasing Stdlib lemma-name drift across versions. *)
Lemma le_to_le0 (a b : Z) : a <= b -> a - b <= 0.
Proof. intros H. apply Z.sub_nonpos. exact H. Qed.

Lemma ge_to_le0 (a b : Z) : a >= b -> b - a <= 0.
Proof. intros H. apply Z.sub_nonpos. apply Z.ge_le. exact H. Qed.

Register le_to_le0 as proof_broker.term_mode.le_to_le0.
Register ge_to_le0 as proof_broker.term_mode.ge_to_le0.

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

Print le_to_le0.
Print Assumptions le_to_le0.

Print ge_to_le0.
Print Assumptions ge_to_le0.

Print pos_is_pos.
Print Assumptions pos_is_pos.

Print pos_is_nonneg.
Print Assumptions pos_is_nonneg.

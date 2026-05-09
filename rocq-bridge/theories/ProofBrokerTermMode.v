(** Helper lemmas for term-mode Tier 1 Farkas reconstruction.

    The plugin's term-mode closer (planned, not yet wired — see
    "Pickup state" below) takes a Farkas witness JSON (coefficients
    keyed by hypothesis name) and builds an application of one of
    these lemmas. The cert IS the proof, not a certificate that one
    exists. No call to [lia]/[lra] is made along this path; the
    closer's trust footprint is exactly these lemmas plus [ring]
    (used to discharge the polynomial identity that the linear-
    combination sum equals the cert's residual constant K).

    Everything here is axiom-free: only [Stdlib.ZArith.BinInt] and
    [Stdlib.ZArith.Zorder] are touched. [Print Assumptions] of any
    theorem that funnels through [farkas_le_n] reports "Closed
    under the global context".

    Pickup state. Phase 0 of the plan (the Plan agent's writeup,
    captured in conversation) is done: [proof_broker_verbose [z3]]
    on the example1 LIA goal mints a Tier 1 Farkas cert with
    witness coefficients [(H2, 1); (H1, 1)] (no [neg_goal] entry —
    the goal is [False], so the broker omits it). Phase 1 is also
    done: this file. The OCaml-side term builder ([term_mode.ml])
    is unwritten; what blocks it isn't the design but the
    plugin-API spelunking — three concrete dead-ends from the
    half-written attempt:

      1. [Pos2Z.is_pos] (which gives [0 < Zpos p]) is not a
         registered [Rocqlib.lib_ref], so reaching it from the
         plugin needs either an explicit [Register Pos2Z.is_pos as
         proof_broker.term_mode.pos_is_pos] here, or an alternative
         construction of [0 < K] that lives entirely behind helpers
         we register.

      2. [Hc1 : 0 <= c1] for a positive integer coefficient [c1]
         needs its own builder — most ergonomic is to add
         [pos_is_nonneg : forall p, 0 <= Zpos p] here, registered.
         The c=0 case (rare in practice, since the cert dedup
         strips zero coefficients) would use [Z.le_refl 0].

      3. [Heq : c1*a1 + c2*a2 = K] is left as an evar and closed
         by sequencing [Refine.refine] with a [ring] tactic call.
         Concretely: [Proofview.tclTHEN (Refine.refine ...) ring].
         The ring invocation pattern mirrors [invoke_lia] in
         [pb_rocq_main.ml] (parse "ring" through Procq, intern,
         eval) — a one-liner once the sequencing shape is right.

    The plan's helper-arity dimension is also outstanding: only
    arity-2 is here. Arities 3..N are mechanical copies (Lemma
    farkas_le_3 (a1 a2 a3) ...). One could write a generic
    list-shaped lemma, but the plan called fixed-arity simpler at
    the [EConstr.mkApp] site, and the SDK's witness-coefficient
    counts in practice are small (Tier 1 Farkas typically arity
    ≤ 5). *)

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

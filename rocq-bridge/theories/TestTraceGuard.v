(** Identity-trace guard tests (R2).

    The dispatch pipeline (prop-simp + registry def-unfold) runs
    inside [Dispatch.run] on every dispatch. A hypothesis of shape
    [True /\ P] is a prop-simp redex (And_True_left), so dispatching
    these goals produces a NON-identity trace: the cert addresses the
    rewritten IR, not the reified goal. The guard must (a) keep plain
    [proof_broker] closing via the decision-procedure fallback on the
    original goal, and (b) make the cert-consuming closers
    ([proof_broker_walker], [proof_broker_term]) fail with the named
    guard error instead of consuming the cert against the wrong goal.
    Own file so the [Print]/[Print Assumptions] pairs survive dune's
    per-action output truncation (RUNBOOK trap). *)

From Stdlib Require Import ZArith Lia.

Declare ML Module "proof_broker_rocq.plugin".

Open Scope Z_scope.

(* (a) Non-identity trace falls back and still closes: the walker arm
   is guard-skipped and cert-gated [lia] proves the original goal. *)
Theorem pb_guard_nonidentity_falls_back_axiom_free :
  forall x : Z, True /\ x <= 5 -> x <= 5.
Proof. intros x h. proof_broker. Qed.

Print pb_guard_nonidentity_falls_back_axiom_free.
Print Assumptions pb_guard_nonidentity_falls_back_axiom_free.

(* (b) Walker-strict on a rewritten dispatch fails closed with the
   guard error; the goal stays open and is then closed honestly. *)
Theorem pb_guard_walker_fails_closed :
  forall x : Z, True /\ x <= 5 -> x <= 5.
Proof.
  intros x h.
  Fail proof_broker_walker.
  lia.
Qed.

Print pb_guard_walker_fails_closed.
Print Assumptions pb_guard_walker_fails_closed.

(* (b') Term mode on a rewritten dispatch fails closed with the
   guard error; the goal stays open and is then closed honestly. *)
Theorem pb_guard_term_fails_closed :
  forall x : Z, True /\ x <= 5 -> x <= 5.
Proof.
  intros x h.
  Fail proof_broker_term.
  lia.
Qed.

Print pb_guard_term_fails_closed.
Print Assumptions pb_guard_term_fails_closed.

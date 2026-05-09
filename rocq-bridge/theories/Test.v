(** End-to-end reifier test (Phase 3): example1-shape LIA goal.

    Build success of this file is the test. The [proof_broker_test]
    tactic walks the current goal + hypotheses, reifies them into the
    proof_broker IR, and prints the result via [Feedback.msg_notice];
    the build captures that output. Phase 4 swaps the print for an
    actual broker dispatch + verify. *)

From Stdlib Require Import ZArith Lia.

Declare ML Module "proof_broker_rocq.plugin".

Open Scope Z_scope.

Goal forall x : Z, x >= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker_test.
  (* Phase 3: tactic prints the reified IR; Phase 4 will close the
     goal directly. For now the goal is still open after the call,
     so we discharge it by hand. *)
  lia.
Qed.

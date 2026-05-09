(** Smoke test for the proof_broker Rocq plugin (Phase 2 stub).

    Build success of this file is the test: if [Declare ML Module]
    can find the plugin and [proof_broker_test] dispatches into the
    OCaml entry point without erroring, the scaffold is wired up.
    Phase 3 swaps the goal here for a real LIA reification target. *)

From Stdlib Require Import ZArith.

Declare ML Module "proof_broker_rocq.plugin".

Goal True.
Proof.
  proof_broker_test.
  exact I.
Qed.

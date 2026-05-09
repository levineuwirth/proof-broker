(** Proof Broker Rocq plugin — vernac/tactic entry points.

    Phase 4 architectural probe: a Rocq tactic that reifies the
    current goal + Prop hypotheses into the proof_broker IR,
    dispatches through the broker, and prints the cert tier /
    format / verify reason. Does NOT close the goal yet (Phase 4.5).
    The point is to validate that the IR is genuinely cross-system
    by running a second source language (Rocq's [Constr]) through
    the same dispatch + verify pipeline that Lean uses.

    Failure modes (cert=[None] from dispatch, or verify reason !=
    [Verified_*]) raise [CErrors.user_err] so the test [.v] file
    fails-loudly during [rocq compile]. *)

val run_default : unit Proofview.tactic
(** [proof_broker_test] tactic: walk the current goal, reify into
    [Ir.t], dispatch through the broker, print the result. Phase 2
    stub: just confirms the plugin loaded by emitting a notice. *)

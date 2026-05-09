(** Proof Broker Rocq plugin — vernac/tactic entry points.

    Phase 4 architectural probe + Phase 4.5 closer: the Rocq plugin
    reifies the current goal into the proof_broker IR, dispatches
    through the broker, verifies the cert, and (in [run_close])
    closes the goal via [lia] under cert-gating — same trust
    discipline as Lean's [omega] path.

    Trust footprint mirrors Lean's [Tactic.lean] header. The OCaml
    verifier accepting the cert gates the [lia] call, and [lia]
    itself is axiom-free (it's Stdlib's micromega LIA decision
    procedure), so closures along this path don't introduce a
    cert-trust axiom. Non-LIA fragments are out of scope here and
    surface as a hard error; LRA opt-in via [lra] is the symmetric
    extension to Lean's Mathlib-flavored [linarith] closer. *)

val run_test : unit Proofview.tactic
(** [proof_broker_test]: dispatch + verify, then print a one-line
    summary via [Feedback.msg_notice]. Does NOT close the goal —
    leaves it open for inspection. Useful for debugging the
    reifier or the cert path. *)

val run_close : unit Proofview.tactic
(** [proof_broker]: dispatch + verify + close. On a verified LIA
    cert, hands the goal to Stdlib's [lia]; on any other outcome
    (no cert, verifier rejected, non-LIA fragment) raises
    [CErrors.user_err] so the failure surfaces during [rocq compile]. *)

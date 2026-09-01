(** Proof Broker Rocq plugin — tactic entry points.

    Surface mirrors Lean's [Tactic.lean]:

    * [proof_broker]                — bare; default adapters,
                                       higher-tier first.
    * [proof_broker [cvc5, z3]]    — explicit list, input order
                                       respected verbatim.
    * [proof_broker_test]          — debug; dispatch + verify, then
                                       print summary, do NOT close.
    * [proof_broker_verbose]       — like [proof_broker] but emits
                                       multi-line extraction-path
                                       summary (IR shape, attempts,
                                       cert, verify) before closing.

    Trust footprint: cert verification gates the close. LIA goals
    close via Stdlib's axiom-free [lia]; non-LIA fragments raise
    [CErrors.user_err] for now (LRA opt-in is the symmetric extension
    to Lean's [ProofBrokerMathlib]). *)

val run_close : Names.Id.t list option -> unit Proofview.tactic
(** Dispatch + verify + close. [None] uses default manifests sorted
    by tier descending; [Some names] respects the input order. *)

val run_close_walker : Names.Id.t list option -> unit Proofview.tactic
(** Walker-STRICT close: dispatch + verify + reconstruct via the
    Alethe walker on the minted cert, with NO [lia] fallback. The
    tactic fails unless a live solve mints a Tier-3 alethe-2024 cert
    AND the walker walks it into a kernel term — end-to-end coverage
    for the production cvc5 -> walker -> kernel path that
    [run_close]'s [tclORELSE _ lia] otherwise masks. Test-only. *)

val run_test : Names.Id.t list option -> unit Proofview.tactic

val run_spec_gate_test : string -> string -> unit Proofview.tactic
(** TEST-ONLY (R3-M1, C3a ROUND 1 finding 2): drive
    [check_cert_specializations] on a synthetic cert —
    mode ∈ {nat, int}, kind ∈ {none, nat_spec, foreign_spec,
    mixed_spec}; the fail-closed branches must throw, the invertible
    shapes must pass and close a [True] goal. *)
(** Dispatch + verify + print summary; does not close. *)

val run_verbose : Names.Id.t list option -> unit Proofview.tactic
(** Dispatch + verify + multi-line summary + close (or error).
    Mirrors Lean's [proof_broker?] verbose form. *)

val run_close_term : Names.Id.t list option -> unit Proofview.tactic
(** Term-mode closer: dispatch + verify + reconstruct the goal
    proof from the cert's Tier 1 Farkas witness. No [lia]/[lra]
    call along this path; the cert IS the proof. Falls through
    to [CErrors.user_err] (not the trust axiom) on cert shapes
    outside [Term_mode.close_term]'s scope (non-Tier-1 cert,
    arity > 2, non-Le hypotheses, etc.) — the user explicitly
    opted into term mode by typing [proof_broker_term] over
    plain [proof_broker]. *)

val replay_reconstructed_script :
  string -> string -> unit Proofview.tactic
(** [replay_reconstructed_script trace_format script] feeds the
    LLM-translated script through [Llm_replay.replay_script]
    (the audit-H1 gate) and, on success, emits a
    [Feedback.msg_info] line naming the source trace format so
    the audit trail is visible in build output. Exported for the
    test-only [llm_reconstruct_test] tactic to drive the
    reconstruction-side closer without a live LLM endpoint. *)

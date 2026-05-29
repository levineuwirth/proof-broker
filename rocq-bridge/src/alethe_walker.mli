(** Rocq-side Alethe walker.

    Mirror of [lean-bridge/ProofBroker/Alethe.lean]'s walker module
    (Lean arc PRs #41-#52). Elaborates cvc5's alethe-2024 trace
    into a Coq kernel proof term — the "cert IS the proof"
    architectural play, parallel to the Tier-1 Farkas [Term_mode]
    closer for Tier-1 certs but for Tier-3 alethe-2024.

    Audit H1: walker failure surfaces as a tactic failure, with
    the existing [lia] fallback re-running (closer chain in
    [Pb_rocq_main.close_or_fail]). No axioms are introduced —
    proof-term construction goes through the kernel like every
    other tactic, and the cert never widens the trust footprint.

    Current scope (through R-5 equality):
    * Walker monad: [walker_ctx] (atom → EConstr local-var
      mapping, plus the goal env + live evar_map ref for
      retyping), [walker_state] (step id → proven proof+clause).
    * [sexp_to_constr] over the LIA + UF fragment: integer
      literals, arithmetic ops, comparisons, propositional
      connectives, clause construction, implication, polymorphic
      equality (retyped, not hardcoded to Z), and generic
      uninterpreted-function application.
    * Rule elaborators: [assume], [false], [or] (passthrough),
      [resolution] (n-ary, R-4), [la_generic]/[la_mult_neg]
      (evar + [lia] discharge, R-3), and the equality cluster
      [refl]/[symm]/[trans]/[cong] (R-5).
    * [alethe_walker_test] tactic accepting a string-literal
      trace, parallel to Lean's [aletheWalkerTest].

    Subsequent PRs follow the Lean cluster decomposition: R-3
    arithmetic, R-4 n-ary resolution, R-5 equality, R-6 trust-
    tagged leaves, R-7 boolean cleanup, R-8 [equiv_simplify], R-9
    wire into closer, R-10 [equiv_pos1]/[equiv_pos2], R-11 [cong]
    over operators, R-12 snapshot test. See plan in [.claude/]. *)

(** Re-export of the SDK's [proof] type as the canonical Alethe
    proof representation used by the walker. The SDK is shared by
    both bridges and already includes named-reference expansion. *)
type proof = Proof_broker.Alethe.proof

(** Parse an alethe-2024 trace string into a [proof]. Failure
    modes: parser error (malformed trace, depth exceeded) → Error;
    stack overflow → Error; any other unexpected exception →
    Error (so the caller can fall through to [lia] cleanly). *)
val parse_trace : string -> (proof, string) result

(** TEST-ONLY tactic for the Alethe walker (mirror of Lean's
    [alethe_walker_test] in lean-bridge/ProofBroker/Tactic.lean).
    Parses the string literal as an alethe-2024 trace, walks the
    proof into a Coq kernel term, and assigns the goal. Lets CI
    exercise the walker's per-rule elaboration on hand-written
    traces without dispatching to a live cvc5 — the same
    CI-stable pattern as [llm_replay_test].

    Failure modes: parse error, walker error (unsupported rule,
    no matching assume), or walked-term type mismatch with the
    goal. All become tactic-level errors via [CErrors.user_err];
    the goal is left OPEN, never closed by an unjustified axiom.
    Production [close_or_fail] integration (R-9) wraps the same
    walker logic in a [tclORELSE] so failure falls through to
    [lia] cleanly. *)
val walker_test : string -> unit Proofview.tactic

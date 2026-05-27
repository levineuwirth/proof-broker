(** Rocq-side Alethe walker — R-1 foundation.

    Mirror of [lean-bridge/ProofBroker/Alethe.lean]'s walker module
    (PR #41-#52 on the Lean side). This module elaborates cvc5's
    alethe-2024 trace into a Coq kernel proof term — the "cert IS
    the proof" architectural play, parallel to the Tier-1 Farkas
    [Term_mode] closer for Tier-1 certs but for Tier-3 alethe-2024.

    Audit H1: walker failure surfaces as a tactic failure, with
    the existing [lia] fallback re-running (closer chain in
    [Pb_rocq_main.close_or_fail]). No axioms are introduced by the
    walker itself — proof-term construction goes through the
    kernel like every other tactic, and the cert never widens the
    trust footprint.

    R-1 scope (this PR): module file scaffolding + the parse
    wrapper exposing the SDK's [Proof_broker.Alethe.parse] in a
    Result-typed form. No walking yet; the per-rule elaborators
    arrive in R-2 (clausal layer) and onward. The SDK's ADT
    ([Sexp.t], [step], [proof]) and parser are shared across both
    bridges, so the Rocq side reuses them directly via
    [Proof_broker.Alethe] rather than mirroring in OCaml the way
    Lean had to mirror them in Lean.

    Subsequent PRs follow the same cluster decomposition as the
    Lean arc: R-2 clausal, R-3 arithmetic, R-4 multi-literal
    resolution, R-5 equality, R-6 trust-tagged leaves, R-7
    boolean cleanup, R-8 [equiv_simplify], R-9 wire into closer,
    R-10 [equiv_pos1]/[equiv_pos2], R-11 [cong] over operators,
    R-12 snapshot test. See plan in [.claude/]. *)

(** Re-export of the SDK's [proof] type as the canonical Alethe
    proof representation used by the walker. The SDK is shared by
    both bridges and already includes named-reference expansion,
    so the walker consumes a fully-resolved proof from the start. *)
type proof = Proof_broker.Alethe.proof

(** Parse an alethe-2024 trace string into a [proof].

    Failure modes:
    - parser error (malformed trace, unterminated S-expression,
      depth exceeded) → [Error msg];
    - stack overflow (deeply-nested untrusted solver output) →
      [Error msg];
    - any other unexpected exception is converted to [Error msg]
      so the caller can fall through to [lia] cleanly. *)
val parse_trace : string -> (proof, string) result

(** Replay an LLM-supplied Ltac script and gate the resulting
    proof term's axiom footprint against the classical Rocq
    Stdlib allowlist. See [Llm_replay] module doc. *)
val replay_script : string -> unit Proofview.tactic

(** Term-mode Tier 1 Farkas closer.

    Walks a Farkas witness JSON the SDK already produced (verified
    by [Verifier.verify]'s envelope check), reifies each entry into
    a Rocq proof of [a_i <= 0], and builds an application of
    [ProofBrokerTermMode.farkas_le_2] that closes the goal
    directly. The polynomial identity [c1*a1 + c2*a2 = K] is left
    as an evar and discharged by [ring]; no [lia]/[lra] call along
    this path.

    Trust footprint: the helpers in [theories/ProofBrokerTermMode.v]
    plus [ring]'s reflective normalization. Both are axiom-free.

    Scope of this iteration: arity-2 LIA Farkas with hypotheses of
    shape [Z.le a b] / [Z.ge a b] and a [False] goal (no
    [neg_goal] entry in the witness). Higher arities, the +1 LIA
    strict-inequality trick (Lt-compiled hypotheses), equalities,
    and the goal-not-False case are mechanical follow-ups against
    the same machinery; raise [Unsupported] when out of scope so
    the caller can fall back to [lia]. *)

exception Unsupported of string

val close_term :
  Proof_broker.Ir.t -> Yojson.Safe.t -> unit Proofview.tactic
(** [close_term ir witness] reifies the witness into an applied
    [farkas_le_2] term and refines the goal with it, then
    discharges the residual polynomial-identity subgoal with
    [ring]. Raises [Unsupported _] if the cert shape is outside
    arity-2 LIA False-goal coverage. *)

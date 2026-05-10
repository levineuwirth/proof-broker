(** Term-mode Tier 1 Farkas closer.

    Walks a Farkas witness JSON the SDK already produced (verified
    by [Verifier.verify]'s envelope check), reifies each entry into
    a Rocq proof of [a_i <= 0], and builds an application of the
    matching helper from [theories/ProofBrokerTermMode.v] that
    closes the goal directly:

    * [False] goals → [farkas_le_2] with both witness slots naming
      real hypotheses.
    * [b <= c] / [b < c] goals → [farkas_le_goal_2] /
      [farkas_lt_goal_2]; one witness slot names a real hypothesis,
      the other is the reserved [neg_goal] slot and the synthesized
      neg-goal-norm EConstr ([c + 1 - b] or [c - b]) replaces the
      [a2] slot inside the helper.

    [>=] / [>] / [=] goals are normalized to one of the three shapes
    above by [pb_rocq_main.run_close_term] (applying [Z.le_ge] /
    [Z.lt_gt] / [Z.le_antisymm] before recursing) — close_term itself
    rejects them as an internal invariant.

    The polynomial identity [c1*a1 + c?*?? = K] is left as an evar
    and discharged by [ring]; no [lia]/[lra] call along this path.
    Trust footprint: the helpers in [theories/ProofBrokerTermMode.v]
    plus [ring]'s reflective normalization. Both are axiom-free.

    Scope of this iteration: arity-2 LIA Farkas with hypotheses of
    shape [Z.le a b] / [Z.ge a b]. Higher arities and the [Lt]-
    compiled hypotheses (the +1 LIA strict-inequality trick on the
    hypothesis side) are mechanical follow-ups against the same
    machinery; raise [Unsupported] when out of scope so the caller
    can fall back to [lia]. *)

exception Unsupported of string

(** Goal shapes term-mode recognizes. Mirrors lean-bridge's
    [matchLiaGoal?] / [matchIntEqGoal?] but as an explicit sum
    because Rocq's [Z.ge] / [Z.gt] don't reduce to swapped [Z.le]
    / [Z.lt] the way Lean's instance reduction does. *)
type goal_kind =
  | Goal_false
  | Goal_le of EConstr.t * EConstr.t
  | Goal_lt of EConstr.t * EConstr.t
  | Goal_ge of EConstr.t * EConstr.t
  | Goal_gt of EConstr.t * EConstr.t
  | Goal_eq of EConstr.t * EConstr.t

val goal_kind : Evd.evar_map -> EConstr.t -> goal_kind option
(** [goal_kind sigma ty] classifies a goal type [ty]. Used by
    [pb_rocq_main.run_close_term] to decide whether to apply a
    normalization step ([Z.le_ge] for [>=], [Z.lt_gt] for [>],
    [Z.le_antisymm] for [=]) before invoking [close_term], and by
    [close_term] itself to dispatch to the matching helper. *)

val close_term :
  Proof_broker.Ir.t -> Yojson.Safe.t -> unit Proofview.tactic
(** [close_term ir witness] reifies the witness into an applied
    [farkas_le_2] / [farkas_le_goal_2] / [farkas_lt_goal_2] term and
    refines the goal with it, then discharges the residual
    polynomial-identity subgoal with [ring]. Raises [Unsupported _]
    if the cert shape is outside arity-2 LIA coverage (and the
    caller wraps it as [CErrors.user_err]). *)

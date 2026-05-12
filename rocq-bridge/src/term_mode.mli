(** Term-mode Tier 1 Farkas closer.

    Walks a Farkas witness JSON the SDK already produced (verified
    by [Verifier.verify]'s envelope check), reifies each entry into
    a Rocq proof of [a_i <= 0] (or [a_i < 0] on the strict-aware R
    path), and builds an application of the matching arity-N
    contradiction helper from [theories/ProofBrokerTermMode.v]
    ([farkas_contradict_n] / [r_farkas_contradict_n] /
    [r_farkas_contradict_n_strict]) that closes the goal directly.

    For non-[False] comparison goals ([<=], [<], [>=], [>], [=]),
    the closer first applies a wrapper ([z_le_via_lt] / [z_lt_via_le]
    on Z; [r_le_via_lt] / [r_lt_via_le] on R, with the dispatcher
    in [pb_rocq_main.run_close_term] applying [Z.le_ge] / [Z.lt_gt]
    / [Z.le_antisymm] beforehand for [>=] / [>] / [=]) to convert
    the goal to an implication-False whose body recurses into the
    same arity-N False-fold with [neg_goal] introduced as an extra
    hypothesis-side entry.

    The polynomial identity [s = K] (left-associative sum equals the
    Farkas residual) is left as an evar and discharged by [ring]; no
    [lia]/[lra] call along this path. Trust footprint: the helpers
    in [theories/ProofBrokerTermMode.v] plus [ring]'s reflective
    normalization. Both are axiom-free.

    Coverage: arity-N Farkas certs on LIA and LRA, all five comparison
    goal shapes, all four inequality hypothesis shapes plus their
    negations, and Eq hypotheses with signed coefficients. Raises
    [Unsupported] for cert shapes outside this coverage so the caller
    can fall back to [lia] / [lra]. *)

exception Unsupported of string

(** Goal-comparator type universe tag. Discriminates Z- vs R-typed
    comparators so the dispatcher in [pb_rocq_main.run_close_term]
    picks the right normalization tactic ([Z.le_ge] vs [Rle_ge] etc.)
    and [close_term] picks the right helper + neg_norm shape (+1 trick
    for LIA only). *)
type universe_tag = U_Z | U_R

(** Goal shapes term-mode recognizes. Mirrors lean-bridge's
    [matchLiaGoal?] / [matchIntEqGoal?] but as an explicit sum
    because Rocq's [Z.ge] / [Z.gt] don't reduce to swapped [Z.le]
    / [Z.lt] the way Lean's instance reduction does. Comparator
    constructors carry a [universe_tag] so the recursive dispatcher
    can pick the matching Z- vs R-specific normalization step. *)
type goal_kind =
  | Goal_false
  | Goal_le of EConstr.t * EConstr.t * universe_tag
  | Goal_lt of EConstr.t * EConstr.t * universe_tag
  | Goal_ge of EConstr.t * EConstr.t * universe_tag
  | Goal_gt of EConstr.t * EConstr.t * universe_tag
  | Goal_eq of EConstr.t * EConstr.t * universe_tag

val goal_kind : Evd.evar_map -> EConstr.t -> goal_kind option
(** [goal_kind sigma ty] classifies a goal type [ty]. Used by
    [pb_rocq_main.run_close_term] to decide whether to apply a
    normalization step ([Z.le_ge] / [Z.lt_gt] / [Z.le_antisymm] for
    Z; [Rle_ge] / [Rlt_gt] / [Rle_antisym] for R) before invoking
    [close_term], and by [close_term] itself to dispatch to the
    matching universe-specific helper. *)

val close_term :
  Proof_broker.Ir.t -> Yojson.Safe.t -> unit Proofview.tactic
(** [close_term ir witness] reifies the witness into an applied
    [farkas_contradict_n] (or R-typed counterpart) term and refines
    the goal with it, then discharges the residual polynomial-identity
    subgoal with [ring]. Comparison-goal shapes ([<=], [<], [>=], [>],
    [=]) are routed through a wrapper that introduces the negated
    goal and recurses into the same fold. Picks the type universe
    (Z or R) from [Farkas.effective_fragment ir]. Raises [Unsupported _]
    if the cert shape is out of coverage (and the caller wraps it as
    [CErrors.user_err]). *)

val close_term_case_split :
  Proof_broker.Ir.t -> Yojson.Safe.t list -> Yojson.Safe.t option ->
  unit Proofview.tactic
(** [close_term_case_split ir lemmas_used structural_hint] closes a
    goal whose cert is a Tier 2 [case_split_farkas] payload. Reads
    the structural hint to find the disjunctive IR hypothesis,
    destructs it in the Coq context, and per branch applies the
    matching lemma's Tier 1 Farkas witness via [close_term] (with
    the IR extended by the case hypothesis named "case"). The
    SDK's [Verifier.match_disjunct_index] is the bridge between
    cert lemma case shapes and destruct branch order.

    Coverage: arity-N disjunctive hypothesis ([A \/ B \/ C \/ ...]),
    flattened by [Alethe_farkas.disjuncts_of] on the SDK side and
    destructed via a nested OrAndIntroPattern generated at
    closer-build time. *)

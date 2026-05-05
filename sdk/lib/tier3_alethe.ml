(** Tier 3 alethe-2024 per-step checker.

    The Lean re-checker (direction 2 of the Tier 3 plan) parses the
    Alethe proof and walks each step, dispatching the per-step
    soundness check to a rule-specific checker. This module is the
    OCaml side of one such checker: a single rule, [la_generic],
    routed through the existing [Alethe_farkas] + [Farkas]
    infrastructure. The Lean walker calls this via FFI for
    [la_generic] steps; future rules either get their own OCaml
    checkers here, or get implemented natively in Lean.

    Why per-step rather than whole-proof. The Lean walker owns the
    rule-dispatch decision and the [unsupported_rule] bailout — that
    structure is the point of direction 2. Per-step calls keep the
    walker honest: each FFI hop checks exactly one rule's
    application; failures pinpoint the offending step rather than
    swallow the whole proof. The cost (one FFI hop per step) is
    fine for proofs up to a few hundred steps and will only become
    a bottleneck if we ever ship Tier 3 for large industrial
    proofs, at which point batching becomes the optimization.

    Result taxonomy:
    * [Step_verified] — the rule-specific checker accepted the step.
    * [Step_unsupported_rule rule] — no checker registered for [rule]
      on the OCaml side; the walker can either bail or skip.
    * [Step_failed { rule; detail }] — checker rejected the step;
      [detail] explains which arithmetic invariant or shape match
      failed. *)

type step_result =
  | Step_verified
  | Step_unsupported_rule of string
  | Step_failed of { rule : string; detail : string }

(** Check a single [la_generic] step. Reuses the existing
    [Alethe_farkas] extraction (clause-vs-IR-hypothesis matching by
    linear-form scaling, plus LIA tightening) to produce a Farkas
    witness, then runs [Farkas.verify] on the witness against the
    same IR. Verified iff [Farkas.verify] returns [Verified]. *)
let check_la_generic (ir : Ir.t) (step : Alethe.step) : step_result =
  let fragment = ir.logic_classification.first_order_fragment in
  let inputs = Alethe_farkas.compile_ir_inputs ir in
  match Alethe_farkas.extract_from_step ~fragment ~inputs step with
  | Error e ->
    Step_failed {
      rule = "la_generic";
      detail = Printf.sprintf "%s: %s"
        (Alethe_farkas.error_kind e)
        (Alethe_farkas.error_detail e);
    }
  | Ok entries ->
    let witness =
      Alethe_farkas.witness_to_json (Alethe_farkas.dedupe entries)
    in
    (match Farkas.verify ir witness with
     | Verified -> Step_verified
     | other ->
       Step_failed {
         rule = "la_generic";
         detail = (match other with
           | Verified -> "verified"
           | Unknown_hypothesis { hypothesis } ->
             "unknown_hypothesis: " ^ hypothesis
           | Nonlinear { hypothesis; detail } ->
             Printf.sprintf "nonlinear in %s: %s" hypothesis detail
           | Bad_coefficient { hypothesis; raw } ->
             Printf.sprintf "bad coefficient on %s: %s" hypothesis raw
           | Negative_coefficient { hypothesis; value } ->
             Printf.sprintf "negative coefficient on %s: %s"
               hypothesis value
           | Not_contradictory { residual } ->
             "not contradictory; residual=" ^ residual
           | Malformed_witness { detail } -> detail);
       })

(** Top-level rule dispatch. Add a new clause here when wiring an
    OCaml-side checker for another Alethe rule, and add the same
    rule name to [supported_rules] below. The Lean walker treats
    [Step_unsupported_rule _] as the bailout — Tier 3 verification
    fails when any step uses a rule no checker handles. *)
let check_step (ir : Ir.t) (step : Alethe.step) : step_result =
  match step.rule with
  | "la_generic" -> check_la_generic ir step
  | other -> Step_unsupported_rule other

(** Sorted list of every Alethe rule [check_step] has a registered
    checker for. Must stay in sync with the [check_step] match
    above; [test_supported_rules_sync] in [test_tier3_alethe]
    pins this. The cvc5 minter consults this set to decide whether
    a parsed proof is eligible for Tier 3 minting (the "fail
    closed" gate of direction 3). *)
let supported_rules : string list = [ "la_generic" ]

(** True iff every step in [p] uses a rule [check_step] knows. The
    cvc5 minter uses this to decide between minting Tier 3 (gate
    passes) and falling back to lower-tier paths (gate fails);
    keeps the minting side and the verifier side aligned, so a
    minted Tier 3 cert is always re-checkable by the verifier as
    of mint time. *)
let proof_rules_supported (p : Alethe.proof) : bool =
  let supported = supported_rules in
  List.for_all
    (fun (s : Alethe.step) ->
      String.length s.rule = 0 || List.mem s.rule supported)
    p.steps

(** Render a [step_result] as the FFI envelope payload shape:
    [{ok: bool, kind: <reason kind>, [detail | rule]: ...}]. *)
let step_result_to_json (r : step_result) : Yojson.Safe.t =
  match r with
  | Step_verified ->
    `Assoc [ "ok", `Bool true; "kind", `String "step_verified" ]
  | Step_unsupported_rule rule ->
    `Assoc [
      "ok", `Bool false;
      "kind", `String "step_unsupported_rule";
      "rule", `String rule;
    ]
  | Step_failed { rule; detail } ->
    `Assoc [
      "ok", `Bool false;
      "kind", `String "step_failed";
      "rule", `String rule;
      "detail", `String detail;
    ]

(* --- whole-proof verification --------------------------------------- *)

(** Whole-proof verification verdict. [Verified] when every step's
    rule has a registered checker and every check accepted; one of
    the two failure variants names the offending step so dashboards
    can pinpoint where Tier 3 verification stopped. *)
type verify_result =
  | Verified
  | Unsupported_rule of { rule : string; step_id : string }
  | Step_failed of { step_id : string; rule : string; detail : string }

(** Verify a Tier 3 alethe-2024 proof end-to-end. Walks every step
    in input order, dispatching to [check_step]; returns on the
    first unsupported-rule or step-failure, or [Verified] when all
    steps pass. The proof must parse as a valid Alethe S-expression;
    a parse error surfaces as a [Step_failed] with [step_id = ""]
    and [rule = "<parse>"] so callers don't need a third failure
    arm. *)
let verify (ir : Ir.t) (proof_str : string) : verify_result =
  let proof =
    try Ok (Alethe.parse proof_str)
    with Alethe.Parse_error msg -> Error msg
  in
  match proof with
  | Error msg ->
    Step_failed { step_id = ""; rule = "<parse>"; detail = msg }
  | Ok p ->
    let rec walk = function
      | [] -> Verified
      | (step : Alethe.step) :: rest ->
        (match check_step ir step with
         | Step_verified -> walk rest
         | Step_unsupported_rule rule ->
           Unsupported_rule { rule; step_id = step.id }
         | Step_failed { rule; detail } ->
           Step_failed { step_id = step.id; rule; detail })
    in
    walk p.steps

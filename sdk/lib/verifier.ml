(** Certificate verification (spec v1.0 §8.2).

    Two layers. [envelope_check] does the structural audit only:
    [cert_version] in scope, payload tier matches envelope tier,
    [dispatch_context_hash] matches the IR the cert claims to
    address, and (when supplied) [rewrite_trace_hash] matches the
    trace. [verify] runs envelope checks and then dispatches to a
    tier-specific soundness verifier when one is implemented.

    Hash discipline. The certificate's [dispatch_context_hash]
    must equal [Hash.sha256_of_json (Codec.to_json ir)] —
    same canonicalization the rewriter uses for trace before/after
    hashes. The [rewrite_trace_hash] is checked the same way
    against [Trace.to_json] when a trace is supplied, and the
    trace's [final_ir_hash] must then equal the hash of [ir] (the
    IR being verified is the trace's endpoint). When [trace] is
    [None] those two checks are skipped — but the all-zeros
    sentinel [rewrite_trace_hash] is rejected unconditionally
    (R2): every mint path stamps the real trace hash, so a
    sentinel-bearing cert never passes the envelope.

    Tier-specific verification implemented. Tier 1 [farkas]
    witnesses are checked by [Farkas.verify]: hypotheses (and the
    negated goal) are linearized, weighted by the cert's
    coefficients, and the residual is inspected for a contradiction.
    The fragment dispatch is read from the IR — under LIA the +1
    trick is applied to strict shapes and the residual must be
    strictly positive; under LRA strict witnesses stay strict and
    the residual is allowed to be merely non-negative whenever a
    strict witness contributed positively. Tier 2 with
    [strategy_hint=case_split_farkas] is also implemented: each
    lemma carries a [case] (one disjunct of an IR disjunctive
    hypothesis) and a Farkas [witness] valid under the IR extended
    with that case; the verifier runs each Farkas check and then
    checks the cases partition the disjunctive hypothesis named in
    [structural_hint]. Other Tier 1 witness kinds (sat_assignment,
    sat_unsat_core, polynomial_positivstellensatz), other Tier 2
    strategies, and Tiers 0/3 fall through to
    [Tier_check_deferred] / [Unsupported_witness_kind] — [verify]
    succeeds at the envelope level only for those.

    Trust scope. A [Verified_envelope] result asserts envelope
    well-formedness only — the cert is *addressed* to the right
    IR, but its claim of provability is not checked. A
    [Verified_farkas] result extends that with the arithmetic
    soundness check: the weighted sum of the cert's coefficients
    really is a contradiction over the IR's hypotheses, modulo
    the linearization vocabulary [Farkas] recognizes. *)

type reason =
  | Verified_envelope
  | Verified_farkas
  | Verified_case_split
  | Verified_tier3
  (** Tier-3 TSTP (Vampire): the proof passed [Tier3_tptp]'s
      provenance + DAG-structure gate. Distinct from
      [Verified_tier3] (Alethe per-step re-derivation) because the
      guarantee is genuinely weaker — see [Tier3_tptp]. It is still
      a positive verdict: it gates the home-system's axiom-free
      closer (the kernel check, per audit H1), exactly as
      [Verified_farkas] gates [omega]. *)
  | Verified_tier3_provenance
  | Hash_mismatch of {
      field : string;
      expected : string;
      got : string;
    }
  | Tier_payload_mismatch of {
      envelope_tier : int;
      payload_tier : int;
    }
  | Cert_version_mismatch of { got : string }
  | Farkas_unknown_hypothesis of { hypothesis : string }
  | Farkas_nonlinear of { hypothesis : string; detail : string }
  | Farkas_bad_coefficient of { hypothesis : string; raw : string }
  | Farkas_negative_coefficient of { hypothesis : string; value : string }
  | Farkas_not_contradictory of { residual : string }
  | Farkas_malformed_witness of { detail : string }
  | Case_split_malformed of { detail : string }
  | Case_split_branch_failed of { case_index : int; reason_kind : string }
  | Case_split_partition_mismatch of { detail : string }
  | Tier3_unsupported_rule of { rule : string; step_id : string }
  | Tier3_step_failed of {
      step_id : string;
      rule : string;
      detail : string;
    }
  | Tier3_unsupported_format of { trace_format : string }
  (** A Tier-3 trace whose format the broker recognizes but
      cannot soundness-check in OCaml because verification is the
      home system's job — specifically [lean-tactic-script] or
      [rocq-tactic-script] from the LLM adapter, which only the
      home system's kernel can re-check. Envelope-verified
      (hashes / tier / dispatch context all passed) but NOT a
      soundness verdict: the home-system replay is the proof
      (audit H1). Distinct from [Tier3_unsupported_format] (no
      replayer anywhere) and from [Tier_check_deferred] (no tier
      verifier at all). *)
  | Tier3_replay_deferred of { trace_format : string }
  | Unsupported_witness_kind of { kind : string }
  | Tier_check_deferred of { tier : int }
  (** The cert carries the all-zeros [rewrite_trace_hash] sentinel
      (R2). No dispatch path mints it any more — every adapter
      stamps the real trace hash — so a sentinel here means the
      cert predates R2 or was hand-built to dodge the trace check.
      Rejected unconditionally, [trace] supplied or not: envelope
      verification must never pass on a cert that names no trace. *)
  | Trace_hash_sentinel
  | Other of { kind : string; detail : string }

let kind_of_reason = function
  | Verified_envelope -> "verified_envelope"
  | Verified_farkas -> "verified_farkas"
  | Verified_case_split -> "verified_case_split"
  | Verified_tier3 -> "verified_tier3"
  | Verified_tier3_provenance -> "verified_tier3_provenance"
  | Hash_mismatch _ -> "hash_mismatch"
  | Tier_payload_mismatch _ -> "tier_payload_mismatch"
  | Cert_version_mismatch _ -> "cert_version_mismatch"
  | Farkas_unknown_hypothesis _ -> "farkas_unknown_hypothesis"
  | Farkas_nonlinear _ -> "farkas_nonlinear"
  | Farkas_bad_coefficient _ -> "farkas_bad_coefficient"
  | Farkas_negative_coefficient _ -> "farkas_negative_coefficient"
  | Farkas_not_contradictory _ -> "farkas_not_contradictory"
  | Farkas_malformed_witness _ -> "farkas_malformed_witness"
  | Case_split_malformed _ -> "case_split_malformed"
  | Case_split_branch_failed _ -> "case_split_branch_failed"
  | Case_split_partition_mismatch _ -> "case_split_partition_mismatch"
  | Tier3_unsupported_rule _ -> "tier3_unsupported_rule"
  | Tier3_step_failed _ -> "tier3_step_failed"
  | Tier3_unsupported_format _ -> "tier3_unsupported_format"
  | Tier3_replay_deferred _ -> "tier3_replay_deferred"
  | Unsupported_witness_kind _ -> "unsupported_witness_kind"
  | Tier_check_deferred _ -> "tier_check_deferred"
  | Trace_hash_sentinel -> "trace_hash_sentinel"
  | Other { kind; _ } -> kind

let detail_of_reason = function
  | Verified_envelope -> ""
  | Verified_farkas -> ""
  | Verified_case_split -> ""
  | Verified_tier3 -> ""
  | Verified_tier3_provenance ->
    "tstp derivation: provenance + DAG-structure verified (no \
     smuggled axioms, refutes the negated goal, reaches $false); \
     inference steps not individually re-derived"
  | Case_split_malformed { detail } -> detail
  | Case_split_branch_failed { case_index; reason_kind } ->
    Printf.sprintf "branch %d failed: %s" case_index reason_kind
  | Case_split_partition_mismatch { detail } -> detail
  | Tier3_unsupported_rule { rule; step_id } ->
    Printf.sprintf "step %s: rule %s has no registered checker"
      step_id rule
  | Tier3_step_failed { step_id; rule; detail } ->
    Printf.sprintf "step %s (rule %s) failed: %s" step_id rule detail
  | Tier3_unsupported_format { trace_format } ->
    Printf.sprintf "no Tier 3 verifier registered for trace_format=%s"
      trace_format
  | Tier3_replay_deferred { trace_format } ->
    Printf.sprintf
      "trace_format=%s is replayed by the home-system kernel, not \
       the broker (envelope verified)" trace_format
  | Hash_mismatch { field; expected; got } ->
    Printf.sprintf "%s: expected %s, got %s" field expected got
  | Tier_payload_mismatch { envelope_tier; payload_tier } ->
    Printf.sprintf "envelope.tier=%d but payload encoding is tier %d"
      envelope_tier payload_tier
  | Cert_version_mismatch { got } ->
    Printf.sprintf "expected cert_version=1.0, got %s" got
  | Farkas_unknown_hypothesis { hypothesis } ->
    Printf.sprintf "hypothesis %s not found in IR (and not the reserved \
                    name neg_goal)" hypothesis
  | Farkas_nonlinear { hypothesis; detail } ->
    Printf.sprintf "%s: %s" hypothesis detail
  | Farkas_bad_coefficient { hypothesis; raw } ->
    Printf.sprintf "%s: could not parse coefficient %s as rational"
      hypothesis raw
  | Farkas_negative_coefficient { hypothesis; value } ->
    Printf.sprintf "%s: coefficient %s is negative on an inequality \
                    (Farkas requires nonneg here)" hypothesis value
  | Farkas_not_contradictory { residual } ->
    Printf.sprintf "weighted sum is %s, not a contradictory constant \
                    (need >0 for loose, >=0 with a positively-weighted \
                    strict witness)"
      residual
  | Farkas_malformed_witness { detail } -> detail
  | Unsupported_witness_kind { kind } ->
    Printf.sprintf "tier-specific verifier not implemented for \
                    witness_kind=%s" kind
  | Tier_check_deferred { tier } ->
    Printf.sprintf "tier-%d soundness check not implemented \
                    (envelope verified)" tier
  | Trace_hash_sentinel ->
    "rewrite_trace_hash is the all-zeros sentinel: the cert names \
     no rewrite trace, so it cannot be tied to the IR it claims to \
     address (R2 deleted the sentinel from every mint path)"
  | Other { detail; _ } -> detail

let reason_to_json (r : reason) : Yojson.Safe.t =
  let kind = kind_of_reason r in
  let detail = detail_of_reason r in
  if detail = "" then `Assoc [ "kind", `String kind ]
  else `Assoc [ "kind", `String kind; "detail", `String detail ]

(* --- individual checks ----------------------------------------------- *)

let check_cert_version (cert : Certificate.t) : reason option =
  if cert.cert_version = "1.0" then None
  else Some (Cert_version_mismatch { got = cert.cert_version })

(** Tier number on the envelope must match the tier the payload
    actually encodes. This catches the case where a malformed cert
    declared [tier=1] but the codec parsed a Tier 3 payload (which
    can't happen via [of_json] today because that function uses
    the envelope tier to choose the parse branch — but a cert
    constructed in OCaml directly could still have a mismatch,
    and a future relaxed codec might too). *)
let check_tier_payload_match (cert : Certificate.t) : reason option =
  let payload_tier = Certificate.payload_tier cert.payload in
  if payload_tier = cert.tier then None
  else Some (Tier_payload_mismatch {
    envelope_tier = cert.tier;
    payload_tier;
  })

(** [check_dispatch_context_hash cert ir]: the cert claims to
    address [ir]; verify it. Recomputes the hash with the same
    [Hash.sha256_of_json] / [Codec.to_json] pipeline the rewriter
    uses, so a freshly-rewritten IR will always agree with itself. *)
let check_dispatch_context_hash (cert : Certificate.t) (ir : Ir.t)
  : reason option =
  let computed = Hash.sha256_of_json (Codec.to_json ir) in
  if computed = cert.dispatch_context_hash then None
  else Some (Hash_mismatch {
    field = "dispatch_context_hash";
    expected = cert.dispatch_context_hash;
    got = computed;
  })

let check_rewrite_trace_hash (cert : Certificate.t) (trace : Trace.t)
  : reason option =
  let computed = Hash.sha256_of_json (Trace.to_json trace) in
  if computed = cert.rewrite_trace_hash then None
  else Some (Hash_mismatch {
    field = "rewrite_trace_hash";
    expected = cert.rewrite_trace_hash;
    got = computed;
  })

(** The all-zeros "no trace" sentinel R2 deleted from every mint
    path. Rejected in [envelope_check] whether or not a trace is
    supplied. *)
let zero_sentinel_hash = "sha256:" ^ String.make 64 '0'

let check_trace_hash_sentinel (cert : Certificate.t) : reason option =
  if String.equal cert.rewrite_trace_hash zero_sentinel_hash
  then Some Trace_hash_sentinel
  else None

(** [check_trace_endpoint trace ir]: the IR being verified must be
    the trace's endpoint — [trace.final_ir_hash] equals the
    computed hash of [ir]. Together with [check_dispatch_context_hash]
    this makes replaying a (cert, trace) pair against any IR other
    than the pipeline's output a hash mismatch by construction. *)
let check_trace_endpoint (trace : Trace.t) (ir : Ir.t) : reason option =
  let computed = Hash.sha256_of_json (Codec.to_json ir) in
  if computed = trace.final_ir_hash then None
  else Some (Hash_mismatch {
    field = "trace.final_ir_hash";
    expected = trace.final_ir_hash;
    got = computed;
  })

(* --- driver ---------------------------------------------------------- *)

(** Run the envelope checks in order; return the first failing
    reason or [Verified_envelope]. The [trace] argument is
    optional because some certificates address an unrewritten IR
    (no trace exists). When [trace = None], the trace-hash check
    is silently skipped — but [dispatch_context_hash] is still
    checked unconditionally, so the cert can never silently match
    a different IR. *)
let envelope_check
      ?(trace : Trace.t option = None)
      (cert : Certificate.t)
      (ir : Ir.t) : reason =
  match check_cert_version cert with
  | Some r -> r
  | None ->
    match check_trace_hash_sentinel cert with
    | Some r -> r
    | None ->
      match check_tier_payload_match cert with
      | Some r -> r
      | None ->
        match check_dispatch_context_hash cert ir with
        | Some r -> r
        | None ->
          match trace with
          | None -> Verified_envelope
          | Some tr ->
            (match check_rewrite_trace_hash cert tr with
             | Some r -> r
             | None ->
               match check_trace_endpoint tr ir with
               | Some r -> r
               | None -> Verified_envelope)

(** Map a [Farkas.verdict] to the verifier's [reason] taxonomy. The
    [Verified] case becomes [Verified_farkas] (envelope + arithmetic);
    each failure variant gets its own reason kind so callers can
    distinguish "wrong shape" from "wrong sum" from "wrong sign". *)
let reason_of_farkas (v : Farkas.verdict) : reason =
  match v with
  | Verified -> Verified_farkas
  | Unknown_hypothesis { hypothesis } ->
    Farkas_unknown_hypothesis { hypothesis }
  | Nonlinear { hypothesis; detail } ->
    Farkas_nonlinear { hypothesis; detail }
  | Bad_coefficient { hypothesis; raw } ->
    Farkas_bad_coefficient { hypothesis; raw }
  | Negative_coefficient { hypothesis; value } ->
    Farkas_negative_coefficient { hypothesis; value }
  | Not_contradictory { residual } ->
    Farkas_not_contradictory { residual }
  | Malformed_witness { detail } ->
    Farkas_malformed_witness { detail }

(* --- Tier 2: case-split Farkas --------------------------------------- *)

(** Recognize an IR shell as one of the disjuncts of [target] by
    compiled-form equality (modulo the same positive scaling
    [Alethe_farkas.match_shape] uses). Returns the matched index or
    [None]. *)
let match_disjunct_index
      ~fragment (case : Ir.shell_term) (disjuncts : Ir.shell_term list)
  : int option =
  match Farkas.compile_hypothesis ~fragment case with
  | Error _ -> None
  | Ok cc ->
    let rec find i = function
      | [] -> None
      | d :: rest ->
        (match Farkas.compile_hypothesis ~fragment d with
         | Error _ -> find (i + 1) rest
         | Ok cd ->
           let res =
             let module L = Linear_arith in
             (* Audit #18 (Q1): single source of truth for the
                scalar-multiple match — [Alethe_farkas.scale_factor].
                The former inline copy here was behaviourally
                identical (canonical [Linear_arith.t] carries no zero
                coefficients, so its guarded-inverse variant and
                [scale_factor]'s direct [rat_inv] agree on every
                reachable input); duplicating trust-critical scaling
                logic only created drift risk. *)
             match cc, cd with
             | Le c, Le d | Lt c, Lt d ->
               (match Alethe_farkas.scale_factor c d with
                | Some r when L.rat_is_pos r -> true
                | _ -> false)
             | Eq c, Eq d ->
               (match Alethe_farkas.scale_factor c d with
                | Some r when not (L.rat_is_zero r) -> true
                | _ -> false)
             | _ -> false
           in
           if res then Some i else find (i + 1) rest)
    in
    find 0 disjuncts

(** Parse one Tier 2 lemma object [{"case": ..., "witness": ...}]. *)
let parse_lemma (j : Yojson.Safe.t) : (Ir.shell_term * Yojson.Safe.t) option =
  match j with
  | `Assoc fields ->
    (match List.assoc_opt "case" fields, List.assoc_opt "witness" fields with
     | Some case_json, Some witness_json ->
       (try Some (Codec.shell_of_json case_json, witness_json)
        with _ -> None)
     | _ -> None)
  | _ -> None

(** Run case-split Tier 2 verification: each lemma's witness must
    Farkas-verify against the IR extended with the lemma's case as
    an extra hypothesis named "case", and the cases must partition
    the IR's disjunctive hypothesis named in [structural_hint]. *)
let verify_case_split
      ~(structural_hint : Yojson.Safe.t option)
      (lemmas : Yojson.Safe.t list)
      (ir : Ir.t) : reason =
  let fragment = Farkas.effective_fragment ir in
  let hyp_name =
    match structural_hint with
    | Some (`Assoc kvs) ->
      (match List.assoc_opt "disjunctive_hypothesis" kvs with
       | Some (`String s) -> Some s
       | _ -> None)
    | _ -> None
  in
  match hyp_name with
  | None ->
    Case_split_malformed {
      detail = "structural_hint must be an object with field \
                disjunctive_hypothesis"
    }
  | Some hyp_name ->
    (match List.find_opt
             (fun (h : Ir.hypothesis) -> h.name = hyp_name)
             ir.context.hypotheses
     with
     | None ->
       Case_split_malformed {
         detail = Printf.sprintf "hypothesis %s not found in IR" hyp_name
       }
     | Some hyp when (match hyp.shell with Ir.Or _ -> false | _ -> true) ->
       (* Tier-2 case-split soundness rests on the named hypothesis
          being the disjunction whose branches the lemmas close. The
          extractor (Alethe_farkas.unique_disjunctive_target) only
          ever emits case-split certs from a syntactic [Or _] hyp; the
          verifier must require the same. A non-[Or] hypothesis would
          flatten via [disjuncts_of] to the singleton [[hyp.shell]] —
          a degenerate 1-branch "split" that, while not unsound on its
          own (the hypothesis is in the context, so it reduces to a
          Tier-1 proof), is outside the Tier-2 contract and would mask
          a malformed cert as a structural proof. Reject it explicitly
          so verify- and extract-side agree on what a case-split is. *)
       Case_split_malformed {
         detail = Printf.sprintf
           "disjunctive_hypothesis '%s' is not a syntactic disjunction \
            (Or); Tier-2 case-split requires the named hypothesis to be \
            an Or of linear atoms" hyp_name
       }
     | Some hyp ->
       let disjuncts = Alethe_farkas.disjuncts_of hyp.shell in
       let parsed = List.map parse_lemma lemmas in
       if List.exists Option.is_none parsed then
         Case_split_malformed {
           detail = "every lemma must be {\"case\": shell, \
                     \"witness\": farkas-witness}"
         }
       else
         (* [filter_map] rather than [List.map (... | None -> assert
            false)]: the [exists Option.is_none] guard above already
            makes a [None] unreachable here, but [assert false] on an
            attacker-influenced list is a crash one refactor away.
            [filter_map] is total and preserves order. *)
         let lemmas_typed = List.filter_map Fun.id parsed in
         (* Partition check first: every case must match exactly one
            disjunct, and the cases must collectively cover every
            disjunct. Running this before per-branch Farkas
            verification means a malformed cert (missing case,
            duplicate, off-target) surfaces a precise
            [Case_split_partition_mismatch] without first burning
            cycles closing arithmetic for branches that can't
            satisfy the partition contract anyway. *)
         let cases = List.map fst lemmas_typed in
         let matched =
           List.map (fun c -> match_disjunct_index ~fragment c disjuncts)
             cases
         in
         if List.exists Option.is_none matched then
           Case_split_partition_mismatch {
             detail = "one or more cases do not match any disjunct"
           }
         else
           (* Total: guarded by the [exists Option.is_none] above. *)
           let indices = List.filter_map Fun.id matched in
           let n = List.length disjuncts in
           let covered = List.sort_uniq compare indices in
           if List.length covered <> n then
             Case_split_partition_mismatch {
               detail = Printf.sprintf
                 "cases cover %d of %d disjuncts (need each exactly once)"
                 (List.length covered) n
             }
           else
             (* Partition is sound; now verify each branch. *)
             let rec verify_each i = function
               | [] -> Verified_case_split
               | (case_shell, witness) :: rest ->
                 let case_hyp : Ir.hypothesis =
                   { name = "case"; shell = case_shell }
                 in
                 let extended = {
                   ir with
                   context = { ir.context with
                     hypotheses = ir.context.hypotheses @ [ case_hyp ]
                   }
                 } in
                 (match Farkas.verify extended witness with
                  | Verified -> verify_each (i + 1) rest
                  | other ->
                    Case_split_branch_failed {
                      case_index = i;
                      reason_kind =
                        (match other with
                         | Verified -> "verified"
                         | Unknown_hypothesis _ -> "unknown_hypothesis"
                         | Nonlinear _ -> "nonlinear"
                         | Bad_coefficient _ -> "bad_coefficient"
                         | Negative_coefficient _ -> "negative_coefficient"
                         | Not_contradictory _ -> "not_contradictory"
                         | Malformed_witness _ -> "malformed_witness");
                    })
             in
             verify_each 0 lemmas_typed)

(** Map a [Tier3_alethe.verify_result] to the verifier's [reason]
    taxonomy. [Verified] becomes [Verified_tier3]; per-step
    failures preserve the offending step ID + rule for diagnostics. *)
let reason_of_tier3 (v : Tier3_alethe.verify_result) : reason =
  match v with
  | Verified -> Verified_tier3
  | Unsupported_rule { rule; step_id } ->
    Tier3_unsupported_rule { rule; step_id }
  | Step_failed { step_id; rule; detail } ->
    Tier3_step_failed { step_id; rule; detail }

(** Map a [Tier3_tptp.verify_result] (Vampire TSTP) to the
    verifier reason taxonomy. [Verified_provenance] becomes the
    distinct [Verified_tier3_provenance] (honest about the weaker
    guarantee); an unrecognized rule / structural failure reuses
    the Tier-3 diagnostic variants. *)
let reason_of_tier3_tptp (v : Tier3_tptp.verify_result) : reason =
  match v with
  | Verified_provenance -> Verified_tier3_provenance
  | Unrecognized_rule { rule; node } ->
    Tier3_unsupported_rule { rule; step_id = node }
  | Structural_failure { node; detail } ->
    Tier3_step_failed { step_id = node; rule = "<tstp-structure>"; detail }

(** Full verification: envelope checks then tier-specific. Tier 1
    [farkas] dispatches to [Farkas.verify]; Tier 2 with
    [strategy_hint=case_split_farkas] dispatches to
    [verify_case_split]; Tier 3 with [trace_format="alethe-2024"]
    dispatches to [Tier3_alethe.verify], which walks the proof
    step-by-step and returns [Verified_tier3] when every step's
    rule has a registered checker and accepts. Any other tier or
    strategy without an implemented verifier surfaces as
    [Tier_check_deferred], [Unsupported_witness_kind], or
    [Tier3_unsupported_format]. *)
let verify
      ?(trace : Trace.t option = None)
      (cert : Certificate.t)
      (ir : Ir.t) : reason =
  match envelope_check ~trace cert ir with
  | Verified_envelope ->
    (match cert.payload with
     | Tier1_witness { witness_kind = Farkas; witness_data; _ } ->
       reason_of_farkas (Farkas.verify ir witness_data)
     | Tier1_witness { witness_kind; _ } ->
       Unsupported_witness_kind {
         kind = Certificate.witness_kind_to_string witness_kind;
       }
     | Tier2_lemma_list { lemmas_used; strategy_hint; structural_hint }
       when strategy_hint = "case_split_farkas" ->
       verify_case_split ~structural_hint lemmas_used ir
     | Tier3_proof_trace { trace_format = "alethe-2024";
                           trace_data = `String proof_str; _ } ->
       reason_of_tier3 (Tier3_alethe.verify ir proof_str)
     | Tier3_proof_trace { trace_format = ("tstp-fof" | "tstp-thf");
                           trace_data = `String proof_str; _ } ->
       reason_of_tier3_tptp (Tier3_tptp.verify ir proof_str)
     | Tier3_proof_trace
         { trace_format = ("lean-tactic-script" | "rocq-tactic-script")
            as trace_format; _ } ->
       (* Untrusted LLM oracle output: only the home system's
          kernel can re-check it. Envelope passed; defer the proof
          to the home-system replay (audit H1). The two formats
          correspond to the two home bridges
          [Adapter_llm.dialect_of_ir] dispatches on; both share
          this verdict because the broker's role is identical for
          either (envelope check + hand off). *)
       Tier3_replay_deferred { trace_format }
     | Tier3_proof_trace { trace_format; _ } ->
       Tier3_unsupported_format { trace_format }
     | _ -> Tier_check_deferred { tier = cert.tier })
  | r -> r

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
    against [Trace.to_json] when a trace is supplied; when
    [trace] is [None], that check is skipped (some certificates
    are produced against an unrewritten IR, in which case there
    is no trace to hash).

    Tier-specific verification implemented. Tier 1 [farkas]
    witnesses are checked by [Farkas.verify]: hypotheses (and
    the negated goal under the LIA +1 trick) are linearized,
    weighted by the cert's coefficients, and the residual is
    inspected for a strictly-positive constant. Other Tier 1
    witness kinds (sat_assignment, sat_unsat_core,
    polynomial_positivstellensatz) and Tiers 0/2/3 fall through
    to [Tier_check_deferred] / [Unsupported_witness_kind] —
    [verify] succeeds at the envelope level only for those.

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
  | Unsupported_witness_kind of { kind : string }
  | Tier_check_deferred of { tier : int }
  | Other of { kind : string; detail : string }

let kind_of_reason = function
  | Verified_envelope -> "verified_envelope"
  | Verified_farkas -> "verified_farkas"
  | Hash_mismatch _ -> "hash_mismatch"
  | Tier_payload_mismatch _ -> "tier_payload_mismatch"
  | Cert_version_mismatch _ -> "cert_version_mismatch"
  | Farkas_unknown_hypothesis _ -> "farkas_unknown_hypothesis"
  | Farkas_nonlinear _ -> "farkas_nonlinear"
  | Farkas_bad_coefficient _ -> "farkas_bad_coefficient"
  | Farkas_negative_coefficient _ -> "farkas_negative_coefficient"
  | Farkas_not_contradictory _ -> "farkas_not_contradictory"
  | Farkas_malformed_witness _ -> "farkas_malformed_witness"
  | Unsupported_witness_kind _ -> "unsupported_witness_kind"
  | Tier_check_deferred _ -> "tier_check_deferred"
  | Other { kind; _ } -> kind

let detail_of_reason = function
  | Verified_envelope -> ""
  | Verified_farkas -> ""
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
    Printf.sprintf "weighted sum is %s, not a strictly-positive constant"
      residual
  | Farkas_malformed_witness { detail } -> detail
  | Unsupported_witness_kind { kind } ->
    Printf.sprintf "tier-specific verifier not implemented for \
                    witness_kind=%s" kind
  | Tier_check_deferred { tier } ->
    Printf.sprintf "tier-%d soundness check not implemented \
                    (envelope verified)" tier
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

(** Full verification: envelope checks then tier-specific. Tier 1
    [farkas] dispatches to [Farkas.verify]; any other tier or
    witness kind without an implemented verifier surfaces as
    [Tier_check_deferred] or [Unsupported_witness_kind]. *)
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
     | _ -> Tier_check_deferred { tier = cert.tier })
  | r -> r

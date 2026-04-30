(** Pre-tier envelope verification (spec v1.0 §8.2).

    Given a [Certificate.t] and the artifacts it claims to address
    (the [Ir.t] the adapter consumed and, optionally, the
    [Trace.t] of rewrites that produced it), this module checks
    that the certificate is internally well-formed and that it
    refers to *those* artifacts. It does NOT run tier-specific
    soundness checks: the verifier returns [Verified_envelope]
    when the envelope is consistent, leaving tier-specific
    verification (Farkas arithmetic, Alethe replay, lemma-list
    reconstruction, ...) to downstream layers.

    Hash discipline. The certificate's [dispatch_context_hash]
    must equal [Hash.sha256_of_json (Codec.to_json ir)] —
    same canonicalization the rewriter uses for trace before/after
    hashes. The [rewrite_trace_hash] is checked the same way
    against [Trace.to_json] when a trace is supplied; when
    [trace] is [None], that check is skipped (some certificates
    are produced against an unrewritten IR, in which case there
    is no trace to hash).

    Soundness scope. A [Verified_envelope] result asserts that
    the certificate's structure is well-formed and that its
    dispatch identifiers match the artifacts the broker has on
    file. It does NOT assert that the goal stated in the cert
    is provable. The tier-specific verifiers (deferred:
    [verify_farkas], [verify_alethe], etc.) are responsible for
    soundness; this module is a precondition for invoking them.

    Tier 1 / Farkas note. Real Farkas verification requires
    parsing the IR's hypotheses and the goal-negation into
    rational linear forms, then summing them under the
    certificate's coefficients. That cuts across the LIA-specific
    arithmetic vocabulary in the shell calculus and is deferred to
    a follow-up milestone; for now the witness payload is
    accepted at the structural level (well-formed, coefficients
    parse as nonnegative rationals) without the arithmetic check. *)

type reason =
  | Verified_envelope
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
  | Other of { kind : string; detail : string }

let kind_of_reason = function
  | Verified_envelope -> "verified_envelope"
  | Hash_mismatch _ -> "hash_mismatch"
  | Tier_payload_mismatch _ -> "tier_payload_mismatch"
  | Cert_version_mismatch _ -> "cert_version_mismatch"
  | Other { kind; _ } -> kind

let detail_of_reason = function
  | Verified_envelope -> ""
  | Hash_mismatch { field; expected; got } ->
    Printf.sprintf "%s: expected %s, got %s" field expected got
  | Tier_payload_mismatch { envelope_tier; payload_tier } ->
    Printf.sprintf "envelope.tier=%d but payload encoding is tier %d"
      envelope_tier payload_tier
  | Cert_version_mismatch { got } ->
    Printf.sprintf "expected cert_version=1.0, got %s" got
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

(** Tier-3 TSTP-passthrough payload constructor (Phase 3 M2).

    The TSTP analogue of [Alethe_passthrough]: captures the raw
    Vampire derivation text and inventories the inference rules /
    structural features it uses, assembling a verifier-ready
    [Certificate.Tier3_proof_trace] payload.

    Format conventions.

    * [trace_format = "tstp-fof"] or ["tstp-thf"], chosen from the
      serializer dialect (a FOF problem yields an FOF/CNF
      derivation; a THF problem a THF one). The Lean re-checker
      dispatches its handling on this string.
    * [trace_data]: a JSON string carrying the verbatim TSTP
      S-expression text. Opaque so a newer Vampire revision rides
      the same envelope without a schema change.
    * [trace_dialect_features]: a sorted, deduped list. [rule:<r>]
      for every distinct inference rule; the bare tag
      [provenance_verified_only] is ALWAYS present and is the
      honest signal that this Tier-3 cert was gated by
      [Tier3_tptp]'s provenance+structure check, NOT by per-step
      re-derivation (cf. Alethe Tier 3, which IS per-step). A
      consumer that requires full step re-checking must treat the
      presence of this tag as "inference steps not individually
      re-verified".
    * [trace_annotations]: a one-line human summary that states the
      same guarantee boundary in prose, for dashboards and
      LLM-assisted reconstruction. *)

let structural_tag = "provenance_verified_only"

let dialect_features (p : Tptp_proof.proof) : string list =
  let rules =
    List.map (fun r -> "rule:" ^ r) (Tptp_proof.rule_inventory p)
  in
  List.sort_uniq String.compare (structural_tag :: rules)

let summarize (p : Tptp_proof.proof) : string =
  let n = List.length p.nodes in
  let rules = Tptp_proof.rule_inventory p in
  Printf.sprintf
    "tstp passthrough: %d formulas; rules: %s. Gated by provenance + \
     DAG-structure verification (no smuggled axioms, refutes the \
     negated goal, reaches $false); inference steps are NOT \
     individually re-derived — the home-system closer is the \
     kernel check."
    n
    (if rules = [] then "(none)" else String.concat ", " rules)

(** Build a Tier-3 [Certificate.payload]. [proof_str] is the raw
    Vampire stdout proof block; [proof] is the [Tptp_proof.parse]
    result (passed in so the caller reuses the parse it already did
    for the [Tier3_tptp] gate). [dialect] picks the [tstp-fof] /
    [tstp-thf] format id. *)
let make_payload
    ~(proof_str : string)
    ~(dialect : Tptp.dialect)
    (proof : Tptp_proof.proof)
  : Certificate.payload =
  let trace_format =
    match dialect with
    | Tptp.Fof -> "tstp-fof"
    | Tptp.Thf -> "tstp-thf"
  in
  Certificate.Tier3_proof_trace {
    trace_format;
    trace_data = `String proof_str;
    trace_dialect_features = Some (dialect_features proof);
    trace_annotations = Some (summarize proof);
  }

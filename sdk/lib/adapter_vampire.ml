(** Vampire ATP adapter (Phase 3 / spec v1.0 §7, roadmap §Phase 3
    deliverable 1).

    Wires an [Ir.t] through a Vampire subprocess and turns the SZS
    status reply into either a Tier 0 oracle [Certificate.t] or a
    typed [Adapter.failure]. Shaped like [Adapter_z3] (no-shell
    [open_process_args_full], [Adapter.drain_subprocess_streams],
    [Adapter.resolve_timeout_ms]); the differences are the binary,
    the TPTP encoding ([Tptp.emit] rather than [Smtlib.emit]), and
    the SZS-status protocol instead of [sat]/[unsat].

    Encoding. TPTP uses roles, not a refutation encoding: each
    hypothesis is an [axiom], the goal a [conjecture]. A
    [% SZS status Theorem] (or [Unsatisfiable] /
    [ContradictoryAxioms]) reply means the goal follows. Vampire
    auto-detects FOF vs THF from the file; the dialect is chosen by
    [Tptp.dialect_of_ir] (higher-order IRs → THF "Vampire-HOL").

    Tier scope (M1). Tier 0 oracle only. Vampire's resolution /
    superposition proofs have no cheap independent re-check
    analogous to a Farkas witness, so — unlike the SMT adapters —
    there is no Tier 1 upgrade here. The Tier 3 TSTP replayer
    (roadmap deliverable 2) is a separate milestone; until it
    lands, a Vampire success is a trust-tier oracle cert and the
    home-system side closes it via a verdict-gated axiom-free
    closer (never a trust axiom — audit H1), exactly as a Tier 0
    SMT cert is handled.

    Refinement record. No LIA-style [Refinement.run] (that
    specializes typeclass methods to arithmetic primitives, which
    is irrelevant to the FOL/HOL goals Vampire serves). The
    serializer's symbol-rename side-channel is recorded as
    [axiomatization] specializations (spec §7, roadmap deliverable
    1), and the cert addresses the original IR's hash. *)

let vampire_binary = "vampire"

(** Per-call timeout in milliseconds. Honors
    [ir.user_directives.budget.wall_time_ms] when set; otherwise
    defaults to 10 seconds — ATP search is less predictable than an
    SMT decision procedure, so the default is higher than the SMT
    adapters' 5s. *)
let default_timeout_ms = 10_000

let timeout_of_ir (ir : Ir.t) : int =
  Adapter.resolve_timeout_ms ~default_ms:default_timeout_ms ir

(* --- I/O ------------------------------------------------------------- *)

(** Spawn Vampire with the given timeout, write [problem] to its
    stdin, return [(stdout, stderr, exit_code)]. Vampire reads a
    TPTP problem from stdin when given no file argument. Raises any
    [Unix] error so callers can wrap.

    Vampire's [--time_limit] is in seconds and accepts a decimal,
    so the broker's millisecond budget maps through exactly as
    [%.3f] rather than being rounded to whole seconds; Vampire
    rejects a non-positive limit, so it is floored at 100 ms.
    [--proof tptp] requests a TSTP derivation on stdout — unused
    by the Tier-0 minter but kept so the M2 replayer can consume
    the same invocation. The derivation must reference input
    formulas by our hypothesis names ([file(_, NAME)] leaves), which
    the M2 provenance verifier aligns with IR hypotheses: Vampire
    >= 5.1.0 prints them by default (as single-quoted atoms, which
    [Tptp_proof] un-quotes); 5.0.x needed [--output_axiom_names on],
    an option 5.1.0 REMOVED ("User error: output_axiom_names is not
    a valid option" -> no SZS line -> no cert). Without the flag,
    5.0.x prints [file(unknown,unknown)] and Tier-3 minting falls
    through to Tier 0, so this adapter is Tier-3-capable only on the
    pinned >= 5.1.0 binary. *)
let run_solver ~timeout_ms (problem : string) : string * string * int =
  let secs = Float.max 0.1 (float_of_int timeout_ms /. 1000.) in
  let argv = [|
    vampire_binary;
    "--input_syntax"; "tptp";
    "--proof"; "tptp";
    "--time_limit"; Printf.sprintf "%.3f" secs;
  |] in
  (* No shell: [open_process_args_full] execvp's [argv] directly, so
     neither the flags nor the TPTP problem (written to stdin, never
     to argv) undergo shell word-splitting. PATH-trust: [argv.(0)]
     ("vampire") is resolved via execvp against the inherited PATH;
     the caller owns PATH trust (CI installs a pinned binary; a
     production deployment with an untrusted PATH should pass an
     absolute path here). Mirrors [Adapter_z3.run_solver]. *)
  let stdout_ch, stdin_ch, stderr_ch =
    Unix.open_process_args_full argv.(0) argv (Unix.environment ())
  in
  output_string stdin_ch problem;
  close_out stdin_ch;
  let out, err = Adapter.drain_subprocess_streams stdout_ch stderr_ch in
  let status = Unix.close_process_full (stdout_ch, stdin_ch, stderr_ch) in
  let code = match status with
    | Unix.WEXITED n -> n
    | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> -1
  in
  (out, err, code)

(* --- response parsing ------------------------------------------------ *)

(** The SZS ontology statuses we discriminate. [Proved] folds the
    several "the conjecture holds" verdicts ([Theorem] for a
    problem with a conjecture; [Unsatisfiable] /
    [ContradictoryAxioms] for the axiom-refutation framing).
    [Disproved] is a real countermodel (the goal does NOT follow);
    [Incomplete] is Vampire giving up or running out of
    time/resources without a verdict. *)
type szs =
  | Proved of string
  | Disproved of string
  | Incomplete of string
  | No_status

(** Scan stdout for the first [% SZS status <Word>] line. Vampire
    prints exactly one such line per run; anything before it is
    banner / parser noise. *)
let parse_szs (stdout : string) : szs =
  let prefix = "% SZS status " in
  let plen = String.length prefix in
  let lines = String.split_on_char '\n' stdout in
  let status =
    List.find_map
      (fun raw ->
        let l = String.trim raw in
        if String.length l > plen && String.sub l 0 plen = prefix then
          (* The status word is the token after the prefix; the rest
             ("for <name>") is commentary. *)
          let rest = String.sub l plen (String.length l - plen) in
          let word =
            match String.index_opt rest ' ' with
            | Some i -> String.sub rest 0 i
            | None -> rest
          in
          Some word
        else None)
      lines
  in
  match status with
  | None -> No_status
  | Some w ->
    (match w with
     | "Theorem" | "Unsatisfiable" | "ContradictoryAxioms" -> Proved w
     | "CounterSatisfiable" | "Satisfiable" -> Disproved w
     | "Timeout" | "ResourceOut" | "GaveUp" | "Incomplete"
     | "Unknown" | "InProgress" -> Incomplete w
     | other -> Incomplete other)

(* --- cert minting ---------------------------------------------------- *)

(** Pinned to the Vampire release installed in CI. Bump on solver
    upgrade so the manifest / [backend.version] stay synchronized
    (mirrors the [Adapter_z3.version] discipline). *)
let version = "5.1.0"

let backend ~version : Certificate.backend = {
  name = "vampire";
  version;
  config_hash = "sha256:" ^ String.make 64 '0';
}

(** Measured solver wall clock (R2). [memory_peak_kb] is absent —
    not measured, never a fabricated 0. *)
let resources_measured ~wall_ms : Certificate.resources = {
  wall_time_ms = wall_ms;
  memory_peak_kb = None;
  budget_consumed = None;
}

(** The serializer reports each [(ir_symbol, tptp_atom)] rename it
    applied. Per spec §7 / roadmap deliverable 1 the ATP path
    records these as [axiomatization] specializations: the TPTP
    encoding axiomatizes the IR's typeclass/structural vocabulary
    as uninterpreted TPTP symbols, and the witness names that
    encoding so a lifter can reverse it. *)
let mk_refinement_record
      ~adapter_version
      ~(dialect : Tptp.dialect)
      ~(ir : Ir.t)
      (specs : Tptp.specialization list)
  : Refinement_record.t =
  let fragment =
    match dialect with
    | Tptp.Thf -> "HOL"
    | Tptp.Fof ->
      let f = ir.logic_classification.first_order_fragment in
      if f = "" || f = "none" then "FOL" else f
  in
  {
    adapter = "vampire";
    adapter_version;
    specializations =
      List.map
        (fun (s : Tptp.specialization) : Refinement_record.specialization -> {
           kind = Refinement_record.Axiomatization;
           source = s.source;
           target = s.target;
           justification = Some "tptp_symbol_axiomatization";
           soundness_witness = Some "uninterpreted_tptp_encoding";
         })
        specs;
    fragment;
    auxiliary =
      Some (`Assoc [ "tptp_dialect",
                     `String (Tptp.dialect_string dialect) ]);
  }

let mint_oracle_cert
      ~adapter_version
      ~rewrite_trace_hash
      ~(original_ir : Ir.t)
      ~(dialect : Tptp.dialect)
      ~(specs : Tptp.specialization list)
      ~(szs_word : string)
      ~wall_ms
  : Certificate.t =
  let dispatch_context_hash =
    Hash.sha256_of_json (Codec.to_json original_ir)
  in
  {
    cert_version = "1.0";
    tier = 0;
    format = "oracle";
    goal = original_ir.goal;
    dispatch_context_hash;
    rewrite_trace_hash;
    backend = backend ~version:adapter_version;
    resources = resources_measured ~wall_ms;
    refinement_record =
      mk_refinement_record ~adapter_version ~dialect ~ir:original_ir specs;
    payload = Tier0_oracle {
      claim = "proved";
      backend_attestation =
        Some (Printf.sprintf
                "vampire returned SZS status %s for the conjecture"
                szs_word);
    };
  }

(** Tier-3 TSTP-passthrough cert. Minted only when [Tier3_tptp]'s
    provenance + DAG-structure gate passes (the "fail closed"
    discipline cvc5's adapter uses for its Tier-3 path): a minted
    Tier-3 cert is always re-checkable by the verifier as of mint
    time. The payload records, honestly, that the gate was
    provenance-level, not per-step (see [Tptp_passthrough]). *)
let mint_tier3_cert
      ~adapter_version
      ~rewrite_trace_hash
      ~(original_ir : Ir.t)
      ~(dialect : Tptp.dialect)
      ~(specs : Tptp.specialization list)
      ~(proof_str : string)
      ~(proof : Tptp_proof.proof)
      ~wall_ms
  : Certificate.t =
  let dispatch_context_hash =
    Hash.sha256_of_json (Codec.to_json original_ir)
  in
  {
    cert_version = "1.0";
    tier = 3;
    format = (match dialect with
              | Tptp.Fof -> "tstp-fof" | Tptp.Thf -> "tstp-thf");
    goal = original_ir.goal;
    dispatch_context_hash;
    rewrite_trace_hash;
    backend = backend ~version:adapter_version;
    resources = resources_measured ~wall_ms;
    refinement_record =
      mk_refinement_record ~adapter_version ~dialect ~ir:original_ir specs;
    payload = Tptp_passthrough.make_payload ~proof_str ~dialect proof;
  }

(* --- top-level dispatch --------------------------------------------- *)

let dispatch ~rewrite_trace_hash (ir : Ir.t) : Adapter.result =
  (* R1.8: certs stamp the probed binary version (declared constant
     as fallback). On a major.minor mismatch, emit a named
     diagnostic and skip the version-sensitive Tier-3 TSTP
     provenance passthrough — Vampire's own 5.0→5.1 CLI/output
     drift is the precedent (the [file('<stdin>','h1')] provenance
     form the verifier matches on is version-shaped). The Tier-0
     oracle path stays available. *)
  let version_drift =
    Adapter.version_mismatch ~binary:vampire_binary ~declared:version in
  if version_drift then
    Adapter.warn_version_mismatch ~adapter:"vampire"
      ~binary:vampire_binary ~declared:version
      ~skipping:"the Tier-3 TSTP provenance passthrough";
  let stamped_version =
    Adapter.probed_version ~binary:vampire_binary ~fallback:version in
  match Tptp.emit ir with
  | Error err ->
    Failed (Unsupported_ir {
      kind = Tptp.kind_of_error err;
      detail = Tptp.detail_of_error err;
    })
  | Ok script ->
    let timeout_ms = timeout_of_ir ir in
    (try
       let t_solve = Unix.gettimeofday () in
       let stdout, stderr, code = run_solver ~timeout_ms script.body in
       let wall_ms =
         int_of_float ((Unix.gettimeofday () -. t_solve) *. 1000.) in
       match parse_szs stdout with
       | Proved w ->
         let mk_oracle () =
           mint_oracle_cert
             ~adapter_version:stamped_version
             ~rewrite_trace_hash
             ~original_ir:ir
             ~dialect:script.dialect
             ~specs:script.specializations
             ~szs_word:w
             ~wall_ms
         in
         (* Tier-3 gate (fail closed): parse the TSTP derivation
            and run the provenance + structure verifier; only mint
            Tier 3 when it returns [Verified_provenance], otherwise
            fall back to the Tier-0 oracle. One parse feeds both
            the gate and the payload. *)
         let cert =
           if version_drift then mk_oracle ()
           else
           match Tptp_proof.parse stdout with
           | exception Tptp_proof.Parse_error _ -> mk_oracle ()
           | proof ->
             (match Tier3_tptp.verify_parsed ir proof with
              | Verified_provenance ->
                mint_tier3_cert
                  ~adapter_version:stamped_version
                  ~rewrite_trace_hash
                  ~original_ir:ir
                  ~dialect:script.dialect
                  ~specs:script.specializations
                  ~proof_str:stdout
                  ~proof
                  ~wall_ms
              | _ -> mk_oracle ())
         in
         Cert cert
       | Disproved _ -> Failed Sat_returned
       | Incomplete w ->
         (match w with
          | "Timeout" | "ResourceOut" -> Failed Timeout
          | _ -> Failed Unknown_returned)
       | No_status ->
         if code <> 0 then
           Failed (Solver_error {
             stderr =
               if stderr = "" then
                 Printf.sprintf "exit=%d, stdout=%s" code stdout
               else stderr;
           })
         else
           Failed (Parse_error {
             stage = "stdout";
             detail = "no '% SZS status' line in vampire output";
           })
     with
     | Unix.Unix_error (e, _, _) ->
       Failed (Solver_error {
         stderr = "could not spawn vampire: " ^ Unix.error_message e;
       })
     | Sys_error msg ->
       Failed (Solver_error { stderr = msg }))

let adapter : Adapter.t = {
  name = "vampire";
  version;
  dispatch;
}

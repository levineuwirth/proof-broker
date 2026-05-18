(** cvc4 oracle adapter (Phase 2.1 / spec v1.0 §7).

    Wires an [Ir.t] through to a cvc4 subprocess and turns the
    [sat]/[unsat]/[unknown] reply into either a Tier 0 oracle
    [Certificate.t] (on [unsat] — meaning the negated goal is
    unsatisfiable, so the goal holds) or a typed [Adapter.failure].

    Tier scope. Phase 2.1 mints Tier 0 oracle certs only. cvc4
    does support proof output (older [--proof] mode), but we don't
    parse it yet — that's Phase 2.2's job and likely targets cvc5
    and Alethe instead. The Tier 0 cert is honest about its tier:
    a downstream consumer should treat it as trust-only, and the
    broker's verifier returns [Tier_check_deferred] for it, which
    is the right answer for "envelope verified, no soundness
    check ran."

    Process spawning. We use [Unix.open_process_args_full], which
    execvp's the argv array directly — no [/bin/sh -c], so no shell
    word-splitting or metacharacter expansion on the flags or the
    SMT-LIB script. The script is written to stdin and
    stdin is closed; cvc4 reads to EOF, prints its result on
    stdout, and exits. If cvc4 isn't on PATH, [Unix] raises an
    exception which we catch and surface as
    [Adapter.Solver_error]. Stderr is captured for the same
    reason. The timeout is enforced by cvc4 itself via
    [--tlimit-per]; the OCaml side just reads to EOF.

    Refinement record. The cvc4 adapter runs [Refinement.run]
    before serialization. The refinement output supplies both the
    substituted IR (with [alpha → Int] applied for LIA goals) and
    the [Refinement_record.specialization] list the cert carries.
    Two specialization kinds end up in the record:
    [type_specialization] (one per type variable the metadata
    embeds into [Int]) and [method_specialization] (one per
    typeclass method declared in [definitional_metadata] with a
    matching fragment target). The SMT-LIB serializer's
    side-channel for renderer-recorded specs is no longer used —
    refinement is the single source of truth for the cert's
    record.

    Hash discipline. The cert's [dispatch_context_hash] addresses
    the *original* (pre-refinement) IR — what the caller handed
    in. Lifters reading the cert + record can reconstruct the
    refined IR by re-running refinement against the original; we
    don't store the refined IR's hash separately. *)

let cvc4_binary = "cvc4"

(** Per-call timeout in milliseconds (cvc4's [--tlimit-per]).
    Honors [ir.user_directives.budget.wall_time_ms] when set;
    otherwise defaults to 5 seconds — enough for any sane
    QF_LIA goal but bounded so a pathological input can't hang
    the broker. *)
let default_timeout_ms = 5000

let timeout_of_ir (ir : Ir.t) : int =
  Adapter.resolve_timeout_ms ~default_ms:default_timeout_ms ir

(* --- I/O ------------------------------------------------------------- *)

(** Spawn cvc4 with the given timeout, write [script] to its stdin,
    return [(stdout, stderr, exit_code)]. Raises any [Unix] error
    so callers can wrap. *)
let run_solver ~timeout_ms (script : string) : string * string * int =
  let argv = [|
    cvc4_binary;
    "--lang"; "smt2";
    "--tlimit-per"; string_of_int timeout_ms;
    "--no-interactive";
  |] in
  (* No shell: see the module header. argv.(0) ("cvc4") is resolved
     via execvp against the inherited PATH — caller owns PATH trust. *)
  let stdout_ch, stdin_ch, stderr_ch =
    Unix.open_process_args_full argv.(0) argv (Unix.environment ())
  in
  output_string stdin_ch script;
  close_out stdin_ch;
  let out, err = Adapter.drain_subprocess_streams stdout_ch stderr_ch in
  let status = Unix.close_process_full (stdout_ch, stdin_ch, stderr_ch) in
  let code = match status with
    | Unix.WEXITED n -> n
    | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> -1
  in
  (out, err, code)

(* --- response parsing ------------------------------------------------ *)

type response = Sat | Unsat | Unknown_resp | Other_resp of string

(** Parse cvc4's first non-empty line. cvc4 prints diagnostic
    output before the answer in some configurations; we scan for
    the first line that's literally [sat]/[unsat]/[unknown]. Any
    other content gets wrapped in [Other_resp] for the caller's
    error path. *)
let parse_response (stdout : string) : response =
  let lines = String.split_on_char '\n' stdout in
  let trimmed = List.map String.trim lines in
  let answer = List.find_opt
    (fun l -> l = "sat" || l = "unsat" || l = "unknown")
    trimmed
  in
  match answer with
  | Some "sat" -> Sat
  | Some "unsat" -> Unsat
  | Some "unknown" -> Unknown_resp
  | _ ->
    let first_real = List.find_opt (fun s -> s <> "") trimmed in
    Other_resp (Option.value first_real ~default:stdout)

(* --- cert minting ---------------------------------------------------- *)

let backend ~version : Certificate.backend = {
  name = "cvc4";
  version;
  config_hash = "sha256:" ^ String.make 64 '0';
}

let resources_now ~timeout_ms : Certificate.resources = {
  wall_time_ms = timeout_ms;
  memory_peak_kb = 0;
  budget_consumed = None;
}

(** Build the refinement record from refinement output + chosen logic.
    The SMT-LIB-flavored [logic] string flows through
    [Smtlib.fragment_of_logic] to produce the bare-fragment label
    the bridges expect ([QF_LIA] -> [LIA] etc.); see Smtlib for the
    mapping table. *)
let mk_refinement_record
      ~adapter_version
      (specs : Refinement_record.specialization list)
      ~logic
  : Refinement_record.t =
  {
    adapter = "cvc4";
    adapter_version;
    specializations = specs;
    fragment = Smtlib.fragment_of_logic logic;
    auxiliary = Some (`Assoc [ "smtlib_logic", `String logic ]);
  }

(** Mint a Tier 0 oracle cert addressing [original_ir] (pre-refinement). *)
let mint_oracle_cert
      ~adapter_version
      ~(original_ir : Ir.t)
      ~(specs : Refinement_record.specialization list)
      ~logic
      ~timeout_ms
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
    rewrite_trace_hash = "sha256:" ^ String.make 64 '0';
    backend = backend ~version:adapter_version;
    resources = resources_now ~timeout_ms;
    refinement_record =
      mk_refinement_record ~adapter_version specs ~logic;
    payload = Tier0_oracle {
      claim = "proved";
      backend_attestation = Some "cvc4 returned unsat on ¬G ∧ hypotheses";
    };
  }

(** Mint a Tier 1 Farkas cert addressing [original_ir]. The
    [witness] field carries a JSON object whose [coefficients]
    re-verify under [Farkas.verify] independent of cvc4 — so
    soundness rests on our internal closer, not on cvc4's verdict.
    cvc4's "unsat" is still the entry condition (no closer attempt
    on [sat]/[unknown]) so the backend attestation matches the
    actual subprocess outcome. *)
let mint_farkas_cert
      ~adapter_version
      ~(original_ir : Ir.t)
      ~(specs : Refinement_record.specialization list)
      ~logic
      ~timeout_ms
      ~(witness : Yojson.Safe.t)
  : Certificate.t =
  let dispatch_context_hash =
    Hash.sha256_of_json (Codec.to_json original_ir)
  in
  {
    cert_version = "1.0";
    tier = 1;
    format = "farkas";
    goal = original_ir.goal;
    dispatch_context_hash;
    rewrite_trace_hash = "sha256:" ^ String.make 64 '0';
    backend = backend ~version:adapter_version;
    resources = resources_now ~timeout_ms;
    refinement_record =
      mk_refinement_record ~adapter_version specs ~logic;
    payload = Tier1_witness {
      witness_kind = Farkas;
      witness_data = witness;
      checking_recipe = "lean.farkas_check";
    };
  }

(* --- top-level dispatch --------------------------------------------- *)

let version = "1.8"

let dispatch (ir : Ir.t) : Adapter.result =
  let fragment = Farkas.effective_fragment ir in
  match Refinement.run ~fragment ir with
  | Error err ->
    Failed (Unsupported_ir {
      kind = Refinement.kind_of_error err;
      detail = Refinement.detail_of_error err;
    })
  | Ok refinement ->
    (match Smtlib.emit refinement.refined_ir with
     | Error err ->
       Failed (Unsupported_ir {
         kind = Smtlib.kind_of_error err;
         detail = Smtlib.detail_of_error err;
       })
     | Ok script ->
       let timeout_ms = timeout_of_ir ir in
       let body = script.body ^ "(check-sat)\n(exit)\n" in
       (try
          let stdout, stderr, code = run_solver ~timeout_ms body in
          (* cvc4 exits 0 on a successful run regardless of sat/unsat;
             parse the stdout regardless of code, since some
             configurations print "unknown" + nonzero exit. *)
          match parse_response stdout, code with
          | Unsat, _ ->
            (* Try our internal Farkas closer to upgrade Tier 0 to
               Tier 1. cvc4 has no proof-trace path, so this is the
               only way for cvc4 to mint a soundness-checkable cert.
               The closer runs after cvc4's [unsat] verdict so the
               backend attestation reflects what actually executed. *)
            let cert =
              match Farkas_search.try_close ir with
              | Ok witness ->
                mint_farkas_cert
                  ~adapter_version:version
                  ~original_ir:ir
                  ~specs:refinement.specializations
                  ~logic:script.logic
                  ~timeout_ms
                  ~witness
              | Error _ ->
                mint_oracle_cert
                  ~adapter_version:version
                  ~original_ir:ir
                  ~specs:refinement.specializations
                  ~logic:script.logic
                  ~timeout_ms
            in
            Cert cert
          | Sat, _ -> Failed Sat_returned
          | Unknown_resp, _ -> Failed Unknown_returned
          | Other_resp _, n when n <> 0 ->
            Failed (Solver_error { stderr =
              if stderr = "" then Printf.sprintf "exit=%d, stdout=%s" n stdout
              else stderr })
          | Other_resp s, _ ->
            Failed (Parse_error {
              stage = "stdout";
              detail = "no sat/unsat/unknown line; first content: " ^ s;
            })
        with
        | Unix.Unix_error (e, _, _) ->
          Failed (Solver_error {
            stderr = "could not spawn cvc4: " ^ Unix.error_message e;
          })
        | Sys_error msg ->
          Failed (Solver_error { stderr = msg })))

let adapter : Adapter.t = {
  name = "cvc4";
  version;
  dispatch;
}

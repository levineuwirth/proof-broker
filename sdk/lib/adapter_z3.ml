(** z3 oracle adapter (Phase 2.2 / spec v1.0 §7).

    Wires an [Ir.t] through to a z3 subprocess and turns the
    [sat]/[unsat]/[unknown] reply into either a Tier 0 oracle
    [Certificate.t] (on [unsat]) or a typed [Adapter.failure].
    Mirrors [Adapter_cvc4] in shape; the only differences are the
    binary name, version string, and argv (z3 takes [-smt2 -in
    -t:MS] — [-t:MS] is per-query timeout in milliseconds, [-in]
    reads from stdin, [-smt2] selects SMT-LIB v2 input).

    Tier scope. Phase 2.2 mints Tier 0 / Tier 1: z3 does support
    proof output ([(set-option :produce-proofs true)] + an
    in-house proof format), but that format is markedly different
    from Alethe and we don't parse it yet. So z3's path here
    matches the cvc4 path: refinement → SMT-LIB emit → spawn →
    parse [unsat] → run the internal Farkas closer to upgrade Tier
    0 to Tier 1 when the IR is Farkas-shaped within the closer's
    bound; otherwise mint a Tier 0 oracle cert.

    Refinement and hash discipline match [Adapter_cvc4] exactly:
    refinement runs first, the cert addresses the *original*
    pre-refinement IR's hash, and the [Refinement_record] carries
    both the type and method specializations. *)

let z3_binary = "z3"

(** Per-call timeout in milliseconds (z3's [-t:N]). Honors
    [ir.user_directives.budget.wall_time_ms] when set; otherwise
    defaults to 5 seconds. *)
let default_timeout_ms = 5000

let timeout_of_ir (ir : Ir.t) : int =
  Adapter.resolve_timeout_ms ~default_ms:default_timeout_ms ir

(* --- I/O ------------------------------------------------------------- *)

(** Spawn z3 with the given timeout, write [script] to its stdin,
    return [(stdout, stderr, exit_code)]. Raises any [Unix] error
    so callers can wrap. *)
let run_solver ~timeout_ms (script : string) : string * string * int =
  let argv = [|
    z3_binary;
    "-smt2";
    "-in";
    Printf.sprintf "-t:%d" timeout_ms;
  |] in
  let cmd = String.concat " " (Array.to_list argv) in
  let stdout_ch, stdin_ch, stderr_ch =
    Unix.open_process_full cmd (Unix.environment ())
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

(** Parse z3's first non-empty answer line. z3 may print
    [unsupported] notes or [(error ...)] lines on stdout before the
    verdict; scan for the first line literally equal to
    [sat]/[unsat]/[unknown]. *)
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
  name = "z3";
  version;
  config_hash = "sha256:" ^ String.make 64 '0';
}

let resources_now ~timeout_ms : Certificate.resources = {
  wall_time_ms = timeout_ms;
  memory_peak_kb = 0;
  budget_consumed = None;
}

let fragment_of_logic = function
  | "QF_LIA" -> "LIA"
  | "QF_LRA" -> "LRA"
  | other -> other

let mk_refinement_record
      ~adapter_version
      (specs : Refinement_record.specialization list)
      ~logic
  : Refinement_record.t =
  {
    adapter = "z3";
    adapter_version;
    specializations = specs;
    fragment = fragment_of_logic logic;
    auxiliary = Some (`Assoc [ "smtlib_logic", `String logic ]);
  }

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
      backend_attestation = Some "z3 returned unsat on ¬G ∧ hypotheses";
    };
  }

(** Mint a Tier 1 Farkas cert addressing [original_ir]. The
    [witness] field carries a JSON object whose [coefficients]
    re-verify under [Farkas.verify] independent of z3 — so
    soundness rests on our internal closer, not on z3's verdict.
    z3's "unsat" is still the entry condition (no closer attempt
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

(** Pinned to the system-installed z3 release. Bump on solver
    upgrade so the manifest / backend.version stay synchronized. *)
let version = "4.16.0"

let pick_fragment (ir : Ir.t) : string =
  let has_real =
    List.exists (fun (fv : Ir.free_var) -> fv.ty = "Real")
      ir.context.free_vars
  in
  if has_real then "LRA" else "LIA"

let dispatch (ir : Ir.t) : Adapter.result =
  let fragment = pick_fragment ir in
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
          match parse_response stdout, code with
          | Unsat, _ ->
            (* Try our internal Farkas closer to upgrade Tier 0 to
               Tier 1. z3 has no proof-trace path here (Phase 2.2
               scope), so this is the only way for z3 to mint a
               soundness-checkable cert. The closer runs after z3's
               [unsat] verdict so the backend attestation reflects
               what actually executed. *)
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
            stderr = "could not spawn z3: " ^ Unix.error_message e;
          })
        | Sys_error msg ->
          Failed (Solver_error { stderr = msg })))

let adapter : Adapter.t = {
  name = "z3";
  version;
  dispatch;
}

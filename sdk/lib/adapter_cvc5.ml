(** cvc5 oracle adapter (Phase 2.1 / spec v1.0 §7).

    Wires an [Ir.t] through to a cvc5 subprocess and turns the
    [sat]/[unsat]/[unknown] reply into either a Tier 0 oracle
    [Certificate.t] (on [unsat]) or a typed [Adapter.failure].
    Mirrors [Adapter_cvc4] in shape; the only differences are the
    binary name, version string, and argv (cvc5 takes
    [--lang=smt2] / [--tlimit-per=MS] in the [=] form and reads
    from stdin without [--no-interactive]).

    Tier scope. We mint Tier 0 oracle certs only — the same scope
    as cvc4 today. cvc5 also produces Alethe proofs via
    [--produce-proofs --proof-format=alethe], which is the natural
    next step toward Tier 3, but parsing those is a separate
    milestone. The Tier 0 cert is honest about its tier: the
    broker's verifier returns [Tier_check_deferred] for it.

    Refinement and hash discipline match [Adapter_cvc4] exactly:
    refinement runs first, the cert addresses the *original*
    pre-refinement IR's hash, and the [Refinement_record] carries
    both the type and method specializations. Lifters re-run
    refinement against the original IR to reconstruct the refined
    one. *)

let cvc5_binary = "cvc5"

(** Per-call timeout in milliseconds (cvc5's [--tlimit-per]).
    Honors [ir.user_directives.budget.wall_time_ms] when set;
    otherwise defaults to 5 seconds. *)
let default_timeout_ms = 5000

let timeout_of_ir (ir : Ir.t) : int =
  match ir.user_directives with
  | Some { budget = Some { wall_time_ms = Some ms; _ }; _ } -> ms
  | _ -> default_timeout_ms

(* --- I/O ------------------------------------------------------------- *)

let read_all (ic : in_channel) : string =
  let buf = Buffer.create 256 in
  (try
     while true do
       Buffer.add_channel buf ic 4096
     done
   with End_of_file -> ());
  Buffer.contents buf

(** Spawn cvc5 with the given timeout, write [script] to its stdin,
    return [(stdout, stderr, exit_code)]. Raises any [Unix] error
    so callers can wrap. *)
let run_solver ~timeout_ms (script : string) : string * string * int =
  let argv = [|
    cvc5_binary;
    "--lang=smt2";
    Printf.sprintf "--tlimit-per=%d" timeout_ms;
  |] in
  let cmd = String.concat " " (Array.to_list argv) in
  let stdout_ch, stdin_ch, stderr_ch =
    Unix.open_process_full cmd (Unix.environment ())
  in
  output_string stdin_ch script;
  close_out stdin_ch;
  let out = read_all stdout_ch in
  let err = read_all stderr_ch in
  let status = Unix.close_process_full (stdout_ch, stdin_ch, stderr_ch) in
  let code = match status with
    | Unix.WEXITED n -> n
    | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> -1
  in
  (out, err, code)

(* --- response parsing ------------------------------------------------ *)

type response = Sat | Unsat | Unknown_resp | Other_resp of string

(** Parse cvc5's first non-empty answer line. cvc5 may print warnings
    on stderr or notes on stdout before the verdict; scan for the
    first line literally equal to [sat]/[unsat]/[unknown]. *)
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
  name = "cvc5";
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
    adapter = "cvc5";
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
      backend_attestation = Some "cvc5 returned unsat on ¬G ∧ hypotheses";
    };
  }

(* --- top-level dispatch --------------------------------------------- *)

(** Pinned to the static-release version we install at
    ~/.local/bin/cvc5. Bump on solver upgrade so the manifest /
    backend.version stay synchronized. *)
let version = "1.3.3"

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
            Cert (mint_oracle_cert
                    ~adapter_version:version
                    ~original_ir:ir
                    ~specs:refinement.specializations
                    ~logic:script.logic
                    ~timeout_ms)
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
            stderr = "could not spawn cvc5: " ^ Unix.error_message e;
          })
        | Sys_error msg ->
          Failed (Solver_error { stderr = msg })))

let adapter : Adapter.t = {
  name = "cvc5";
  version;
  dispatch;
}

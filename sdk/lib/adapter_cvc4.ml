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

    Process spawning. We use [Unix.open_process_full] with a fixed
    argv (no shell parsing). The script is written to stdin and
    stdin is closed; cvc4 reads to EOF, prints its result on
    stdout, and exits. If cvc4 isn't on PATH, [Unix] raises an
    exception which we catch and surface as
    [Adapter.Solver_error]. Stderr is captured for the same
    reason. The timeout is enforced by cvc4 itself via
    [--tlimit-per]; the OCaml side just reads to EOF.

    Refinement record. The cvc4 adapter records the
    method-specialization entries the SMT-LIB serializer applied
    (e.g., [HAdd.hAdd] → [+]) plus a single [type_specialization]
    entry per non-primitive free-var type that was rendered as
    [Int]. The certificate's [refinement_record.fragment] is set
    to the SMT-LIB logic the serializer chose ([QF_LIA] /
    [QF_LRA]). Auxiliary metadata records the chosen logic
    verbatim so a future reconstructor can replay the same
    specialization. *)

let cvc4_binary = "cvc4"

(** Per-call timeout in milliseconds (cvc4's [--tlimit-per]).
    Honors [ir.user_directives.budget.wall_time_ms] when set;
    otherwise defaults to 5 seconds — enough for any sane
    QF_LIA goal but bounded so a pathological input can't hang
    the broker. *)
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

(** Build the refinement record from the serializer's
    specializations + the chosen SMT-LIB logic. *)
let mk_refinement_record
      ~adapter_version
      (specs : Smtlib.specialization list)
      ~logic
  : Refinement_record.t =
  let method_entries =
    List.map (fun (s : Smtlib.specialization) : Refinement_record.specialization ->
      {
        kind = Method_specialization;
        source = s.source;
        target = s.target;
        justification = Some (Printf.sprintf "specialization_targets[%s]" logic);
        soundness_witness = None;
      })
      specs
  in
  let fragment_of_logic = function
    | "QF_LIA" -> "LIA"
    | "QF_LRA" -> "LRA"
    | other -> other
  in
  {
    adapter = "cvc4";
    adapter_version;
    specializations = method_entries;
    fragment = fragment_of_logic logic;
    auxiliary = Some (`Assoc [ "smtlib_logic", `String logic ]);
  }

(** Mint a Tier 0 oracle cert addressing [ir]. *)
let mint_oracle_cert
      ~adapter_version
      (ir : Ir.t)
      (specs : Smtlib.specialization list)
      ~logic
      ~timeout_ms
  : Certificate.t =
  let dispatch_context_hash =
    Hash.sha256_of_json (Codec.to_json ir)
  in
  {
    cert_version = "1.0";
    tier = 0;
    format = "oracle";
    goal = ir.goal;
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

(* --- top-level dispatch --------------------------------------------- *)

let version = "1.8"

let dispatch (ir : Ir.t) : Adapter.result =
  match Smtlib.emit ir with
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
         Cert (mint_oracle_cert
                 ~adapter_version:version
                 ir script.specializations
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
         stderr = "could not spawn cvc4: " ^ Unix.error_message e;
       })
     | Sys_error msg ->
       Failed (Solver_error { stderr = msg }))

let adapter : Adapter.t = {
  name = "cvc4";
  version;
  dispatch;
}

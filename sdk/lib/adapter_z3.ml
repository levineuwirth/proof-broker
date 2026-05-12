(** z3 oracle adapter (Phase 2.2 / spec v1.0 §7).

    Wires an [Ir.t] through to a z3 subprocess and turns the
    [sat]/[unsat]/[unknown] reply into either a [Certificate.t]
    or a typed [Adapter.failure]. Mirrors [Adapter_cvc4] in
    shape; differences are the binary name, version, and argv
    ([-smt2 -in -t:MS] — [-t:MS] is per-query timeout in
    milliseconds).

    Tier scope. The dispatch ladder for [unsat] is:
    1. Native Tier 1 — request [(get-proof)] and try to extract
       a Farkas witness from a [(_ th-lemma arith farkas C1...Cn)]
       application via [Z3_farkas.extract]. We force
       [smt.arith.solver=2] so z3 emits the [farkas] tag with
       explicit coefficients (the default new-arith-solver
       sometimes emits opaque [(_ th-lemma arith)]). The unified
       walker [Z3_proof.find_farkas] handles both surface shapes:
       the clause-introducing form
       [((_ th-lemma arith farkas ...) (or (not L1) ...))] and
       the direct-from-premises form
       [((_ th-lemma arith farkas ...) p1 ... pn false)] with
       signed coefficients (consumers take absolute values, with
       [Farkas.verify] gating the result).
    2. Internal Tier 1 — [Farkas_search.try_close] runs a bounded
       search over the IR directly, rescuing Farkas-shaped goals
       z3 closed through theory rewrites the native extractor
       can't follow.
    3. Tier 0 oracle — falls back when neither produced a
       soundness-checkable witness.

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

(** Slice the proof body out of z3's stdout. z3 prints the
    [unsat] verdict on its own line, possibly preceded by
    [unsupported] notes from logic-mismatch warnings, then emits
    the [(get-proof)] response as a single S-expression. We grab
    everything from the first [(] that follows the [unsat] line
    onward; the parser tolerates trailing whitespace. *)
let extract_proof_body (stdout : string) : string option =
  let n = String.length stdout in
  let rec find_after_unsat i =
    if i >= n then None
    else
      let line_end =
        try String.index_from stdout i '\n' with Not_found -> n
      in
      let line = String.trim (String.sub stdout i (line_end - i)) in
      if line = "unsat" then Some (line_end + 1)
      else find_after_unsat (line_end + 1)
  in
  match find_after_unsat 0 with
  | None -> None
  | Some start ->
    let rec find_paren i =
      if i >= n then None
      else if stdout.[i] = '(' then Some i
      else find_paren (i + 1)
    in
    (match find_paren start with
     | None -> None
     | Some j -> Some (String.sub stdout j (n - j)))

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

(* Fragment-name mapping ([QF_LIA] -> [LIA] etc.) lives in
   [Smtlib.fragment_of_logic] so all three adapters share one
   table — see Smtlib for the source-of-truth comment. *)

let mk_refinement_record
      ~adapter_version
      (specs : Refinement_record.specialization list)
      ~logic
  : Refinement_record.t =
  {
    adapter = "z3";
    adapter_version;
    specializations = specs;
    fragment = Smtlib.fragment_of_logic logic;
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
       (* Force the classical Simplex_LRA arith solver so z3 emits
          the [farkas] tag with explicit coefficients. The default
          new-arith-solver sometimes emits opaque [(_ th-lemma
          arith)] without coefficients, which makes native
          extraction impossible. *)
       let preamble =
         "(set-option :produce-proofs true)\n\
          (set-option :smt.arith.solver 2)\n"
       in
       let body =
         preamble ^ script.body ^ "(check-sat)\n(get-proof)\n(exit)\n"
       in
       (try
          let stdout, stderr, code = run_solver ~timeout_ms body in
          match parse_response stdout, code with
          | Unsat, _ ->
            let mk_oracle () =
              mint_oracle_cert
                ~adapter_version:version
                ~original_ir:ir
                ~specs:refinement.specializations
                ~logic:script.logic
                ~timeout_ms
            in
            let mk_farkas witness =
              mint_farkas_cert
                ~adapter_version:version
                ~original_ir:ir
                ~specs:refinement.specializations
                ~logic:script.logic
                ~timeout_ms
                ~witness
            in
            let try_internal_closer () =
              match Farkas_search.try_close ir with
              | Ok witness -> mk_farkas witness
              | Error _ -> mk_oracle ()
            in
            (* Native Tier 1: parse z3's proof and extract Farkas
               coefficients from either surface shape — the
               clause-introducing
               [(_ th-lemma arith farkas C1...Cn) (or (not L1) ...
               (not Ln))] or the direct-from-premises
               [(_ th-lemma arith farkas C1...Cn) p1 ... pn false].
               When extraction succeeds the witness is verified
               independently by the broker via [Farkas.verify], so
               the soundness chain doesn't depend on z3 — only the
               Farkas multipliers came from z3's proof.

               When extraction fails (no proof body, no
               Farkas-tagged th-lemma, or theory rewrites we can't
               follow) we fall through to the internal closer. *)
            let cert =
              match extract_proof_body stdout with
              | None -> try_internal_closer ()
              | Some proof_str ->
                (match Z3_farkas.extract ir proof_str with
                 | Ok witness -> mk_farkas witness
                 | Error _ -> try_internal_closer ())
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

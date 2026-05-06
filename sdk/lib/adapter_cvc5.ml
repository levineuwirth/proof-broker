(** cvc5 oracle adapter (Phase 2.1 / spec v1.0 §7).

    Wires an [Ir.t] through to a cvc5 subprocess and turns the
    [sat]/[unsat]/[unknown] reply into either a Tier 0 oracle
    [Certificate.t] (on [unsat]) or a typed [Adapter.failure].
    Mirrors [Adapter_cvc4] in shape; the only differences are the
    binary name, version string, and argv (cvc5 takes
    [--lang=smt2] / [--tlimit-per=MS] in the [=] form and reads
    from stdin without [--no-interactive]).

    Tier scope. cvc5 always runs with [--produce-proofs
    --proof-format-mode=alethe]; on [unsat] we ladder Tier 1 → Tier 2
    → Tier 0:
    1. Tier 1 Farkas witness from a single [la_generic] step (see
       [Alethe_farkas.extract]).
    2. If that fails, Tier 2 case-split Farkas: each subproof's
       [la_generic] becomes a per-branch Farkas witness, and the
       branch case-assumptions must partition a disjunctive IR
       hypothesis (see [Alethe_farkas.extract_case_split_payload]).
    3. If both fail, fall back to a Tier 0 oracle cert.

    So a cvc5 unsat reply always yields a cert; how much of cvc5's
    work the Lean side can independently re-check depends on the
    proof's shape.

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
    return [(stdout, stderr, exit_code)]. We always request Alethe
    proof generation: it is cheap on the small problems we dispatch
    (linear arithmetic), and the dispatch path uses the proof to
    upgrade Tier 0 [unsat] verdicts to Tier 1 Farkas witnesses when
    the proof closes via a single [la_generic] step. Raises any
    [Unix] error so callers can wrap. *)
let run_solver ~timeout_ms (script : string) : string * string * int =
  let argv = [|
    cvc5_binary;
    "--lang=smt2";
    "--produce-proofs";
    "--proof-format-mode=alethe";
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

(** Tier 1 Farkas cert built from the witness JSON extracted from
    cvc5's Alethe proof. The dispatch_context_hash addresses the
    *original* IR (same discipline as the Tier 0 cert), so the
    witness's [hypothesis] entries refer to the IR's hypothesis
    names and the verifier can look them up directly. *)
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

(** Tier 3 alethe-2024 passthrough cert. Captures the verbatim
    Alethe S-expression from cvc5's [(get-proof)] output along
    with rule/structural feature inventory; the verifier
    ([Tier3_alethe.verify]) walks the proof step-by-step and
    re-runs each rule's check. The minter only fires when every
    rule in the proof has a registered checker
    ([Tier3_alethe.supported_rules]); the cvc5 dispatch ladder's
    "fail closed" gate sends ineligible proofs down the existing
    Tier 1 / Tier 2 / Tier 0 path instead, so we never mint a
    Tier 3 cert the verifier can't re-check at mint time. *)
let mint_tier3_cert
      ~adapter_version
      ~(original_ir : Ir.t)
      ~(specs : Refinement_record.specialization list)
      ~logic
      ~timeout_ms
      ~(proof_str : string)
      ~(proof : Alethe.proof)
  : Certificate.t =
  let dispatch_context_hash =
    Hash.sha256_of_json (Codec.to_json original_ir)
  in
  {
    cert_version = "1.0";
    tier = 3;
    format = "alethe-2024";
    goal = original_ir.goal;
    dispatch_context_hash;
    rewrite_trace_hash = "sha256:" ^ String.make 64 '0';
    backend = backend ~version:adapter_version;
    resources = resources_now ~timeout_ms;
    refinement_record =
      mk_refinement_record ~adapter_version specs ~logic;
    payload = Alethe_passthrough.make_payload ~proof_str proof;
  }

(** Tier 2 case-split Farkas cert. Each lemma carries a [case]
    (one disjunct of an IR disjunctive hypothesis) and a Farkas
    [witness] valid under the IR extended with that case as an
    extra hypothesis named ["case"]. The verifier re-runs each
    Farkas check and confirms the cases partition the disjunctive
    hypothesis named in [structural_hint]. *)
let mint_case_split_cert
      ~adapter_version
      ~(original_ir : Ir.t)
      ~(specs : Refinement_record.specialization list)
      ~logic
      ~timeout_ms
      ~(lemmas : Yojson.Safe.t list)
      ~(disjunctive_hyp : string)
  : Certificate.t =
  let dispatch_context_hash =
    Hash.sha256_of_json (Codec.to_json original_ir)
  in
  {
    cert_version = "1.0";
    tier = 2;
    format = "case_split_farkas";
    goal = original_ir.goal;
    dispatch_context_hash;
    rewrite_trace_hash = "sha256:" ^ String.make 64 '0';
    backend = backend ~version:adapter_version;
    resources = resources_now ~timeout_ms;
    refinement_record =
      mk_refinement_record ~adapter_version specs ~logic;
    payload = Tier2_lemma_list {
      lemmas_used = lemmas;
      strategy_hint = "case_split_farkas";
      structural_hint = Some (`Assoc [
        "disjunctive_hypothesis", `String disjunctive_hyp;
      ]);
    };
  }

(** Slice the proof body out of cvc5's stdout. cvc5 prints the
    [sat]/[unsat]/[unknown] verdict on its own line, possibly
    preceded by warnings, then emits the [(get-proof)] response as
    a single S-expression. We grab everything from the first [(]
    that follows the [unsat] line onward — the parser is happy with
    trailing whitespace. *)
let extract_proof_body (stdout : string) : string option =
  match String.index_opt stdout '\n' with
  | _ ->
    (* find "unsat" line, then the next "(" *)
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
    (match find_after_unsat 0 with
     | None -> None
     | Some start ->
       (* Find first '(' from [start]. *)
       let rec find_paren i =
         if i >= n then None
         else if stdout.[i] = '(' then Some i
         else find_paren (i + 1)
       in
       (match find_paren start with
        | None -> None
        | Some j -> Some (String.sub stdout j (n - j))))

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
       let body = script.body ^ "(check-sat)\n(get-proof)\n(exit)\n" in
       (try
          let stdout, stderr, code = run_solver ~timeout_ms body in
          match parse_response stdout, code with
          | Unsat, _ ->
            (* Dispatch ladder:
               1. Tier 3 alethe-2024 passthrough — when every rule
                  in the proof is in [Tier3_alethe.supported_rules],
                  ship the whole proof so the verifier can re-check
                  step-by-step. "Fail closed": ineligible proofs
                  fall through rather than minting a Tier 3 cert no
                  verifier can re-check.
               2. Tier 1 (single la_generic) — extracts a Farkas
                  witness from one la_generic step in the proof.
               3. Tier 2 (multi-la_generic case split) — extracts
                  per-branch Farkas witnesses from disjunctive
                  subproofs.
               4. Tier 1 (internal closer) — runs our own bounded
                  Farkas search over the IR directly, rescuing the
                  Farkas-shaped cases cvc5 closes via theory
                  rewrites with no la_generic.
               5. Tier 0 oracle — falls back when nothing else
                  produced a soundness-checkable witness. *)
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
            (* Tier 3 gate: dry-run the full Tier 3 verifier on the
               parsed proof before minting. Only mint when the
               verifier reports [Verified] — this is the strict
               "fail closed" property: a minted Tier 3 cert is
               always re-checkable end-to-end at mint time. cvc5's
               proofs use [hole]/[rare_rewrite] for many distinct
               theory rewrites, only some of which our checker can
               currently verify; the rule-name pre-check
               [proof_rules_supported] is too coarse on its own
               since e.g. [hole] passes the name check but fails
               on a propositional rewrite like [(<= n 10) =
               (not (>= n 11))] under LIA tightening. *)
            let try_tier3 proof_str =
              match Alethe.parse proof_str with
              | exception Alethe.Parse_error _ -> None
              | proof ->
                (match Tier3_alethe.verify_parsed ir proof with
                 | Verified ->
                   Some (mint_tier3_cert
                           ~adapter_version:version
                           ~original_ir:ir
                           ~specs:refinement.specializations
                           ~logic:script.logic
                           ~timeout_ms
                           ~proof_str
                           ~proof)
                 | _ -> None)
            in
            let cert =
              match extract_proof_body stdout with
              | None -> try_internal_closer ()
              | Some proof_str ->
                (match try_tier3 proof_str with
                 | Some t3 -> t3
                 | None ->
                   (match Alethe_farkas.extract ir proof_str with
                    | Ok witness -> mk_farkas witness
                    | Error _ ->
                      (match Alethe_farkas.extract_case_split_payload ir proof_str with
                       | Ok (lemmas, disjunctive_hyp) ->
                         mint_case_split_cert
                           ~adapter_version:version
                           ~original_ir:ir
                           ~specs:refinement.specializations
                           ~logic:script.logic
                           ~timeout_ms
                           ~lemmas
                           ~disjunctive_hyp
                       | Error _ -> try_internal_closer ())))
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
            stderr = "could not spawn cvc5: " ^ Unix.error_message e;
          })
        | Sys_error msg ->
          Failed (Solver_error { stderr = msg })))

let adapter : Adapter.t = {
  name = "cvc5";
  version;
  dispatch;
}

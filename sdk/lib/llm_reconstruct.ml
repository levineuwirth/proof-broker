(** LLM-assisted Tier-3 reconstruction (Phase 3 / spec v1.0 §7,
    roadmap §Phase 3 deliverable 4).

    For Tier-3 certificates whose [trace_format] the home system
    has no symbolic replayer for, this module asks a configured
    LLM to translate the trace into a Lean tactic script the home
    kernel can then check. The script is candidate-only — the
    caller {b must} replay it through the kernel and gate the
    resulting proof term's axiom footprint (audit H1, see
    [ProofBroker.Tactic.replayLlmScriptOrFail]). Nothing this
    module returns is itself trusted.

    Reuse. Transport, response parsing, and the
    Lean-surface-syntax helpers all come from [Adapter_llm] —
    same [curl] subprocess (key via [-K -], non-secret body via
    temp file, no shell), same OpenAI chat-completions wire
    shape, same fenced-```lean response extraction. The {e only}
    thing different here is the user prompt: an IR + the original
    trace + an instruction to translate (rather than to prove
    from scratch).

    Trust model. Identical to [Adapter_llm]'s. The LLM is an
    untrusted oracle; this function may legitimately return a
    bogus / fabricated / [sorry]-laden script. Soundness is
    {e entirely} the caller's, via kernel-replay plus the
    axiom-footprint subset gate.

    Configuration. Same env vars as [Adapter_llm]:
    [PROOF_BROKER_LLM_ENDPOINT] (unset ⇒ fail-closed [Error _]),
    [PROOF_BROKER_LLM_API_KEY] (optional bearer),
    [PROOF_BROKER_LLM_MODEL] (default ["default"]). *)

let default_timeout_ms = Adapter_llm.default_timeout_ms

(** Build the user prompt: the goal as a Lean [theorem ... := by]
    skeleton (same shape [Adapter_llm.render_prompt] uses for the
    primary path), followed by the original trace as a hint with
    its declared format. Free vars and hypotheses become binders;
    the conclusion is the goal. *)
let render_prompt (ir : Ir.t) (cert : Certificate.t) : string =
  let trace_format, trace_data =
    match cert.payload with
    | Tier3_proof_trace { trace_format; trace_data; _ } ->
      trace_format, trace_data
    | _ ->
      invalid_arg
        "Llm_reconstruct.render_prompt: cert.payload is not a \
         Tier3_proof_trace (reconstruction only applies to Tier-3 \
         certificates that carry a proof trace)"
  in
  let fv =
    List.map
      (fun (v : Ir.free_var) ->
         Printf.sprintf "(%s : %s)" v.name (Adapter_llm.lean_ty v.ty))
      ir.context.free_vars
  in
  let hyps =
    List.map
      (fun (h : Ir.hypothesis) ->
         Printf.sprintf "(%s : %s)"
           h.name (Adapter_llm.lean_term h.shell))
      ir.context.hypotheses
  in
  let binders = String.concat " " (fv @ hyps) in
  let goal = Adapter_llm.lean_term ir.goal.shell in
  let trace_str = Yojson.Safe.to_string trace_data in
  Printf.sprintf
    "A theorem prover produced a `%s` proof trace for the Lean 4 \
     theorem below, but the home system has no symbolic replayer \
     for that trace format. Use the trace as a hint and reply with \
     ONLY a fenced ```lean code block containing a Lean 4 tactic \
     proof (the `by` block body), no prose. A wrong or sorry-laden \
     script will be rejected by the home system's kernel-and-axiom \
     gate; the goal is left open in that case.\n\n\
     theorem goal %s : %s := by\n  -- your tactics here\n\n\
     --- begin %s trace ---\n%s\n--- end %s trace ---\n"
    trace_format binders goal trace_format trace_str trace_format

(** Translate [cert]'s trace into a candidate Lean tactic script
    by prompting the configured LLM. Returns the script on
    success or a structured error string on every failure mode
    (no endpoint, curl error, parse error, empty response). The
    returned script is untrusted — see the audit H1 note above. *)
let translate (ir : Ir.t) (cert : Certificate.t) : (string, string) result =
  match Sys.getenv_opt "PROOF_BROKER_LLM_ENDPOINT" with
  | None | Some "" ->
    Error "LLM endpoint not configured (set PROOF_BROKER_LLM_ENDPOINT)"
  | Some url ->
    let api_key = Sys.getenv_opt "PROOF_BROKER_LLM_API_KEY" in
    let model =
      Option.value (Sys.getenv_opt "PROOF_BROKER_LLM_MODEL")
        ~default:"default"
    in
    let timeout_ms =
      Adapter.resolve_timeout_ms ~default_ms:default_timeout_ms ir
    in
    (match cert.payload with
     | Tier3_proof_trace _ -> ()
     | _ ->
       (* Defensive — the caller (FFI / fallback closer) only ever
          passes Tier-3 trace certs, but if something else slips
          through, surface it as a structured error rather than
          raising. *)
       ());
    (match cert.payload with
     | Tier3_proof_trace _ ->
       let prompt = render_prompt ir cert in
       let body = Adapter_llm.build_body ~model ~prompt in
       (try
          let stdout, stderr, code =
            Adapter_llm.curl_post ~timeout_ms ~url ~api_key ~body
          in
          if code <> 0 then
            Error (Printf.sprintf "curl exit=%d: %s" code
                     (if stderr = "" then stdout else stderr))
          else
            (match Adapter_llm.extract_content stdout with
             | None ->
               Error
                 "no choices[0].message.content in LLM response"
             | Some content ->
               let script = Adapter_llm.extract_script content in
               if String.trim script = "" then
                 Error "LLM returned an empty tactic script"
               else
                 Ok script)
        with
        | Unix.Unix_error (e, _, _) ->
          Error ("could not spawn curl: " ^ Unix.error_message e)
        | Sys_error msg -> Error msg)
     | _ ->
       Error
         "Llm_reconstruct.translate: cert payload is not a \
          Tier3_proof_trace; only Tier-3 traces are reconstructable")

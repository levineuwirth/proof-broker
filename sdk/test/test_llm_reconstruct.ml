(** Tests for [Llm_reconstruct] — the LLM-assisted Tier-3
    reconstruction translator (roadmap §Phase 3 deliverable 4).

    No real LLM is ever contacted (roadmap §11 "no LLM in CI"):
    * prompt-rendering / fail-closed / wrong-cert-shape need no
      network;
    * the end-to-end translate path uses a one-shot local mock
      HTTP server (a forked child), same pattern as
      [test_adapter_llm], gated on [curl] being on PATH. *)

open Proof_broker

let curl_available () : bool =
  Sys.command "which curl > /dev/null 2>&1" = 0

let trivial_logic : Ir.logic_classification = {
  order = "first_order"; features_used = [];
  first_order_fragment = "FOL"; decidable_theory = None;
}

let make_ir ?(free_vars = []) ?(hypotheses = [])
    (goal : Ir.shell_term) : Ir.t = {
  ir_version = "1.0";
  source_system = { name = "test"; version = "0.0" };
  tier = "goal";
  logic_classification = trivial_logic;
  goal = { shell = goal; payloads = None };
  context = { type_vars = []; free_vars; hypotheses; library_slice = None };
  type_metadata = []; definitional_metadata = [];
  library_provenance = []; user_directives = None;
}

let sample_ir () =
  make_ir
    ~free_vars:[ { name = "a"; ty = "Nat" } ]
    ~hypotheses:[
      { name = "h1";
        shell = App { symbol = "UF.p"; type_args = [];
                      args = [ Var { name = "a" } ] } } ]
    (App { symbol = "UF.p"; type_args = []; args = [ Var { name = "a" } ] })

let zero_hash = "sha256:" ^ String.make 64 '0'

(** A minimal but well-formed Tier-3 cert carrying a trace in the
    [other-format] dialect — i.e. one the symbolic verifier
    cannot replay, so reconstruction is the natural fallback. *)
let sample_cert ?(trace_format = "other-format")
    ?(trace_data : Yojson.Safe.t = `String "alleged proof steps...")
    (ir : Ir.t) : Certificate.t = {
  cert_version = "1.0";
  tier = 3;
  format = trace_format;
  goal = ir.goal;
  dispatch_context_hash = Hash.sha256_of_json (Codec.to_json ir);
  rewrite_trace_hash = Pipeline.identity_trace_hash ir;
  backend = { name = "test"; version = "0"; config_hash = zero_hash };
  resources = { wall_time_ms = 0; memory_peak_kb = 0;
                budget_consumed = None };
  refinement_record = {
    adapter = "test"; adapter_version = "0"; specializations = [];
    fragment = "FOL"; auxiliary = None;
  };
  payload = Tier3_proof_trace {
    trace_format;
    trace_data;
    trace_dialect_features = None;
    trace_annotations = None;
  };
}

(** A non-trace cert (Tier-0 oracle) — reconstruction must
    refuse it: only Tier-3 trace certs are translatable. *)
let sample_oracle_cert (ir : Ir.t) : Certificate.t = {
  cert_version = "1.0";
  tier = 0;
  format = "oracle";
  goal = ir.goal;
  dispatch_context_hash = Hash.sha256_of_json (Codec.to_json ir);
  rewrite_trace_hash = Pipeline.identity_trace_hash ir;
  backend = { name = "test"; version = "0"; config_hash = zero_hash };
  resources = { wall_time_ms = 0; memory_peak_kb = 0;
                budget_consumed = None };
  refinement_record = {
    adapter = "test"; adapter_version = "0"; specializations = [];
    fragment = "FOL"; auxiliary = None;
  };
  payload = Tier0_oracle {
    claim = "proved";
    backend_attestation = None;
  };
}

let contains hay needle =
  let nl = String.length needle and hl = String.length hay in
  let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in
  nl = 0 || go 0

(* --- rendering (no network) ------------------------------------------ *)

let test_prompt_render () =
  let ir = sample_ir () in
  let cert =
    sample_cert ~trace_format:"alethe-2024"
      ~trace_data:(`String "(step t1 :rule la_generic ...)") ir
  in
  let p = Llm_reconstruct.render_prompt ir cert in
  Alcotest.(check bool) "names the source trace format" true
    (contains p "alethe-2024");
  Alcotest.(check bool) "embeds the trace verbatim" true
    (contains p "la_generic");
  Alcotest.(check bool) "binds the free var" true
    (contains p "(a : Nat)");
  Alcotest.(check bool) "binds the hypothesis" true
    (contains p "(h1 : (p a))");
  Alcotest.(check bool) "states the goal as a theorem" true
    (contains p "theorem goal");
  Alcotest.(check bool) "asks for a fenced lean block" true
    (contains p "```lean");
  Alcotest.(check bool) "warns that the script is gated" true
    (contains p "kernel-and-axiom gate")

(* Rocq-flavored variant: [source_system.name = "rocq"] routes
   through [Adapter_llm.rocq_dialect] so the rendered theorem
   skeleton uses [Theorem ... Proof. ... Qed.] form and asks for
   a fenced ```coq block, not ```lean. *)
let sample_ir_rocq () =
  let ir = make_ir
    ~free_vars:[ { name = "a"; ty = "Int" } ]
    ~hypotheses:[
      { name = "h1";
        shell = App { symbol = "UF.p"; type_args = [];
                      args = [ Var { name = "a" } ] } } ]
    (App { symbol = "UF.p"; type_args = []; args = [ Var { name = "a" } ] })
  in
  { ir with source_system = { name = "rocq"; version = "0.0" } }

let test_prompt_render_rocq () =
  let ir = sample_ir_rocq () in
  let cert =
    sample_cert ~trace_format:"otter-resolution"
      ~trace_data:(`String "(resolved C1 C2 → C3)") ir
  in
  let p = Llm_reconstruct.render_prompt ir cert in
  Alcotest.(check bool) "names the source trace format" true
    (contains p "otter-resolution");
  Alcotest.(check bool) "embeds the trace verbatim" true
    (contains p "resolved C1 C2");
  Alcotest.(check bool) "translates Int → Z in binder" true
    (contains p "(a : Z)");
  Alcotest.(check bool) "states the goal as a Rocq theorem" true
    (contains p "Theorem goal");
  Alcotest.(check bool) "Proof. ... Qed. scaffold" true
    (contains p "Proof.");
  Alcotest.(check bool) "asks for a fenced coq block" true
    (contains p "```coq");
  Alcotest.(check bool) "does not leak Lean by-block" false
    (contains p "```lean");
  Alcotest.(check bool) "does not leak `:= by` syntax" false
    (contains p ":= by")

(** A non-Tier3 cert raises [Invalid_argument] from [render_prompt]
    — defensive, since this is a programming error not a runtime
    failure mode the caller should swallow. *)
let test_prompt_render_rejects_non_tier3 () =
  let ir = sample_ir () in
  let cert = sample_oracle_cert ir in
  match Llm_reconstruct.render_prompt ir cert with
  | exception Invalid_argument _ -> ()
  | _ ->
    Alcotest.fail "render_prompt must reject a non-Tier-3 cert"

(* --- fail-closed (no endpoint) --------------------------------------- *)

let test_fail_closed () =
  Unix.putenv "PROOF_BROKER_LLM_ENDPOINT" "";
  let ir = sample_ir () in
  match Llm_reconstruct.translate ir (sample_cert ir) with
  | Error msg ->
    Alcotest.(check bool) "names the missing config" true
      (contains msg "PROOF_BROKER_LLM_ENDPOINT")
  | Ok _ -> Alcotest.fail "unconfigured endpoint must fail closed"

(** Even with a configured endpoint, translating a non-Tier-3 cert
    is rejected at the type level (no network attempt). *)
let test_translate_rejects_non_tier3 () =
  Unix.putenv "PROOF_BROKER_LLM_ENDPOINT" "http://127.0.0.1:1/no";
  let ir = sample_ir () in
  match Llm_reconstruct.translate ir (sample_oracle_cert ir) with
  | Error msg ->
    Alcotest.(check bool) "names the cert-payload mismatch" true
      (contains msg "Tier3_proof_trace")
  | Ok _ ->
    Alcotest.fail "translating a non-Tier-3 cert must fail closed"

(* --- end-to-end via a local mock endpoint ---------------------------- *)

let mock_body =
  {|{"choices":[{"message":{"content":"```lean\nexact h1\n```"}}]}|}

let test_mock_endpoint () =
  if not (curl_available ()) then Alcotest.skip ();
  let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt sock Unix.SO_REUSEADDR true;
  Unix.bind sock (Unix.ADDR_INET (Unix.inet_addr_loopback, 0));
  Unix.listen sock 1;
  let port =
    match Unix.getsockname sock with
    | Unix.ADDR_INET (_, p) -> p
    | _ -> Alcotest.fail "no port"
  in
  match Unix.fork () with
  | 0 ->
    (* Child: one-shot HTTP responder. *)
    (try
       let c, _ = Unix.accept sock in
       let buf = Bytes.create 4096 in
       ignore (Unix.read c buf 0 (Bytes.length buf));
       let resp =
         Printf.sprintf
           "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\
            Content-Length: %d\r\nConnection: close\r\n\r\n%s"
           (String.length mock_body) mock_body
       in
       ignore (Unix.write_substring c resp 0 (String.length resp));
       Unix.close c
     with _ -> ());
    Unix._exit 0
  | child ->
    Unix.close sock;
    Unix.putenv "PROOF_BROKER_LLM_ENDPOINT"
      (Printf.sprintf "http://127.0.0.1:%d/v1/chat/completions" port);
    Unix.putenv "PROOF_BROKER_LLM_MODEL" "mock-model";
    Unix.putenv "PROOF_BROKER_LLM_API_KEY" "";
    let ir = sample_ir () in
    let result = Llm_reconstruct.translate ir (sample_cert ir) in
    ignore (Unix.waitpid [] child);
    (match result with
     | Ok script ->
       Alcotest.(check string) "extracted script" "exact h1" script
     | Error msg ->
       Alcotest.fail ("mock endpoint should yield a script; got: " ^ msg))

let () =
  Alcotest.run "llm_reconstruct"
    [
      ( "render",
        [ Alcotest.test_case "prompt (Lean)" `Quick test_prompt_render;
          Alcotest.test_case "prompt (Rocq)" `Quick test_prompt_render_rocq;
          Alcotest.test_case "reject non-tier3" `Quick
            test_prompt_render_rejects_non_tier3 ] );
      ( "transport",
        [ Alcotest.test_case "fail-closed (no endpoint)" `Quick
            test_fail_closed;
          Alcotest.test_case "non-tier3 → error" `Quick
            test_translate_rejects_non_tier3;
          Alcotest.test_case "mock endpoint → translated script"
            `Quick test_mock_endpoint ] );
    ]

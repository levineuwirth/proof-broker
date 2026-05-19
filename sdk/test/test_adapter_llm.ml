(** Tests for [Adapter_llm].

    No real LLM is ever contacted (roadmap §11 "no LLM in CI"):
    * fail-closed and prompt/script rendering need no network;
    * the end-to-end path uses a one-shot local mock HTTP server
      (a forked child) and is gated on [curl] being on PATH. *)

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

(* p(a) ⊢ p(a) — shape is irrelevant; we only exercise transport
   and cert minting, not whether the (mocked) model is "right". *)
let sample_ir () =
  make_ir
    ~free_vars:[ { name = "a"; ty = "Nat" } ]
    ~hypotheses:[
      { name = "h1";
        shell = App { symbol = "UF.p"; type_args = [];
                      args = [ Var { name = "a" } ] } } ]
    (App { symbol = "UF.p"; type_args = []; args = [ Var { name = "a" } ] })

(* --- rendering (no network) ------------------------------------------ *)

let contains hay needle =
  let nl = String.length needle and hl = String.length hay in
  let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in
  nl = 0 || go 0

let test_prompt_render () =
  let p = Adapter_llm.render_prompt (sample_ir ()) in
  Alcotest.(check bool) "binds the free var" true
    (contains p "(a : Nat)");
  Alcotest.(check bool) "binds the hypothesis" true
    (contains p "(h1 : (p a))");
  Alcotest.(check bool) "states the goal as a theorem" true
    (contains p "theorem goal");
  Alcotest.(check bool) "asks for a fenced lean block" true
    (contains p "```lean")

let test_extract_script_fenced () =
  Alcotest.(check string) "fenced lean block extracted" "subst h; simp"
    (Adapter_llm.extract_script
       "Sure!\n```lean\nsubst h; simp\n```\nDone.")

let test_extract_script_bare () =
  Alcotest.(check string) "no fence → trimmed whole content"
    "exact h1"
    (Adapter_llm.extract_script "  exact h1  ")

(* --- fail-closed (no endpoint) --------------------------------------- *)

let test_fail_closed () =
  Unix.putenv "PROOF_BROKER_LLM_ENDPOINT" "";
  match Adapter_llm.dispatch (sample_ir ()) with
  | Failed (Solver_error { stderr }) ->
    Alcotest.(check bool) "names the missing config" true
      (contains stderr "PROOF_BROKER_LLM_ENDPOINT")
  | _ -> Alcotest.fail "unconfigured LLM must fail closed"

(* --- end-to-end via a local mock endpoint ---------------------------- *)

let mock_body =
  {|{"choices":[{"message":{"content":"```lean\nsubst_eqs; rfl\n```"}}]}|}

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
    let result = Adapter_llm.dispatch (sample_ir ()) in
    ignore (Unix.waitpid [] child);
    (match result with
     | Cert c ->
       Alcotest.(check int) "tier 3" 3 c.tier;
       Alcotest.(check string) "format" "lean-tactic-script" c.format;
       Alcotest.(check string) "backend name" "llm" c.backend.name;
       Alcotest.(check string) "model in backend.version" "mock-model"
         c.backend.version;
       (match c.payload with
        | Tier3_proof_trace { trace_format; trace_data = `String s; _ } ->
          Alcotest.(check string) "trace_format" "lean-tactic-script"
            trace_format;
          Alcotest.(check string) "extracted script" "subst_eqs; rfl" s
        | _ -> Alcotest.fail "expected Tier3_proof_trace");
       (* Codec round-trip + the honest verifier verdict: envelope
          ok, NOT a soundness verdict (kernel replay is the proof). *)
       let c2 = Certificate.of_json (Certificate.to_json c) in
       Alcotest.(check int) "round-trip tier" 3 c2.tier;
       (match Verifier.verify c (sample_ir ()) with
        | Tier3_replay_deferred { trace_format } ->
          Alcotest.(check string) "replay-deferred format"
            "lean-tactic-script" trace_format
        | r ->
          Alcotest.fail ("expected tier3_replay_deferred, got "
                         ^ Verifier.kind_of_reason r))
     | Failed f ->
       Alcotest.fail ("mock endpoint should yield a cert; got "
                      ^ Adapter.kind_of_failure f))

let () =
  Alcotest.run "adapter_llm"
    [
      ( "render",
        [ Alcotest.test_case "prompt" `Quick test_prompt_render;
          Alcotest.test_case "extract fenced" `Quick
            test_extract_script_fenced;
          Alcotest.test_case "extract bare" `Quick
            test_extract_script_bare ] );
      ( "transport",
        [ Alcotest.test_case "fail-closed (no endpoint)" `Quick
            test_fail_closed;
          Alcotest.test_case "mock endpoint → Tier-3 cert" `Quick
            test_mock_endpoint ] );
    ]

(** LLM-as-backend adapter (Phase 3 / spec v1.0 §7, roadmap
    §Phase 3 deliverable 3).

    Renders the IR as Lean-4 surface syntax, prompts a configured
    chat-completions endpoint, and packages the returned tactic
    script as a Tier-3 [lean-tactic-script] certificate.

    Trust model. An LLM is an {b untrusted oracle}. This adapter
    never asserts the script is correct — the cert is explicitly
    "unverified until kernel replay": soundness rests entirely on
    the home-system replaying the script through its kernel
    (audit H1), a failed replay being a tactic failure, never an
    axiom. The OCaml verifier therefore cannot soundness-check a
    [lean-tactic-script] cert; [Verifier.verify] returns the
    envelope-only [Tier3_replay_deferred] reason for it.

    Transport. A [curl] subprocess (recorded reconsideration,
    [delta.md §2.1]): zero new OCaml deps, the same no-shell
    [open_process_args_full] pattern the solver adapters use,
    system-handled TLS, trivially mockable for the "no LLM in CI"
    policy. The API key travels via [curl -K -] (config on stdin),
    never argv, so it is not visible to [ps]; the request body
    (non-secret) goes through a temp file.

    Configuration (env, same trust model as solver PATH):
    * [PROOF_BROKER_LLM_ENDPOINT] — full chat-completions URL.
      Unset ⇒ the adapter fails closed (a recorded [Failed]
      attempt; the broker simply moves on), it never blocks or
      guesses an endpoint.
    * [PROOF_BROKER_LLM_API_KEY] — optional bearer token.
    * [PROOF_BROKER_LLM_MODEL] — model id (default ["default"]).

    OpenAI chat-completions wire shape is used because it is the
    de-facto common denominator (OpenAI, vLLM, llama.cpp,
    Together, Groq, …): [POST {model, messages:[…],
    temperature:0}] → [choices[0].message.content]. *)

let curl_binary = "curl"

let default_timeout_ms = 30_000

let timeout_of_ir (ir : Ir.t) : int =
  Adapter.resolve_timeout_ms ~default_ms:default_timeout_ms ir

(* --- IR → Lean surface syntax ---------------------------------------- *)

(** Render an IR type-ref as Lean (the IR uses [->] for arrows;
    Lean reads [→], and the parenthesization the reifier emits is
    already Lean-correct). *)
let lean_ty (t : Ir.type_ref) : string =
  let b = Buffer.create (String.length t) in
  let n = String.length t in
  let i = ref 0 in
  while !i < n do
    if !i + 1 < n && t.[!i] = '-' && t.[!i + 1] = '>' then
      (Buffer.add_string b "→"; i := !i + 2)
    else (Buffer.add_char b t.[!i]; incr i)
  done;
  Buffer.contents b

let strip_uf (s : string) : string =
  let p = "UF." in
  let pl = String.length p in
  if String.length s > pl && String.sub s 0 pl = p
  then String.sub s pl (String.length s - pl) else s

(** Infix Lean operator for the recognized arithmetic/relational
    shell symbols; [None] for a plain (prefix) application head. *)
let infix_of = function
  | "HAdd.hAdd" | "Int.add" | "Add.add" | "+" -> Some "+"
  | "HSub.hSub" | "Int.sub" | "Sub.sub" | "-" -> Some "-"
  | "HMul.hMul" | "Int.mul" | "Mul.mul" | "*" -> Some "*"
  | "LE.le" | "<=" -> Some "≤"
  | "LT.lt" | "<" -> Some "<"
  | "GE.ge" | ">=" -> Some "≥"
  | "GT.gt" | ">" -> Some ">"
  | _ -> None

let rec lean_term (t : Ir.shell_term) : string =
  match t with
  | Var { name } -> name
  | Const { name = "True" } -> "True"
  | Const { name = "False" } -> "False"
  | Const { name } -> name
  | Num_lit { value; _ } -> value
  | Not { operand } -> "¬ " ^ paren operand
  | And { left; right } ->
    Printf.sprintf "(%s ∧ %s)" (lean_term left) (lean_term right)
  | Or { left; right } ->
    Printf.sprintf "(%s ∨ %s)" (lean_term left) (lean_term right)
  | Implies { antecedent; consequent } ->
    Printf.sprintf "(%s → %s)" (lean_term antecedent) (lean_term consequent)
  | Eq { left; right; _ } ->
    Printf.sprintf "(%s = %s)" (lean_term left) (lean_term right)
  | Forall { var; ty; body } ->
    Printf.sprintf "(∀ %s : %s, %s)" var (lean_ty ty) (lean_term body)
  | Exists { var; ty; body } ->
    Printf.sprintf "(∃ %s : %s, %s)" var (lean_ty ty) (lean_term body)
  | Lambda { binders; body } ->
    let bs =
      String.concat " "
        (List.map
           (fun (b : Ir.binder) ->
              Printf.sprintf "(%s : %s)" b.var (lean_ty b.ty))
           binders)
    in
    Printf.sprintf "(fun %s => %s)" bs (lean_term body)
  | App { symbol; args; _ } ->
    let sym = strip_uf symbol in
    (match infix_of symbol, args with
     | Some op, [ a; b ] ->
       Printf.sprintf "(%s %s %s)" (lean_term a) op (lean_term b)
     | _, [] -> sym
     | _, _ ->
       Printf.sprintf "(%s %s)" sym
         (String.concat " " (List.map paren args)))
  | Opaque { payload_id } -> "(_ /- opaque:" ^ payload_id ^ " -/)"

and paren (t : Ir.shell_term) : string =
  match t with
  | Var _ | Const _ | Num_lit _ -> lean_term t
  | _ -> lean_term t  (* lean_term already parenthesizes compounds *)

(** The theorem statement + an instruction, as the user prompt.
    Free vars and hypotheses become binders; the goal is the
    conclusion. *)
let render_prompt (ir : Ir.t) : string =
  let fv =
    List.map
      (fun (v : Ir.free_var) ->
         Printf.sprintf "(%s : %s)" v.name (lean_ty v.ty))
      ir.context.free_vars
  in
  let hyps =
    List.map
      (fun (h : Ir.hypothesis) ->
         Printf.sprintf "(%s : %s)" h.name (lean_term h.shell))
      ir.context.hypotheses
  in
  let binders = String.concat " " (fv @ hyps) in
  let goal = lean_term ir.goal.shell in
  Printf.sprintf
    "Prove this Lean 4 theorem. Reply with ONLY a fenced ```lean code \
     block containing a tactic proof (the `by` block body), no prose.\n\n\
     theorem goal %s : %s := by\n  -- your tactics here\n"
    binders goal

(* --- request body ---------------------------------------------------- *)

let system_prompt =
  "You are a Lean 4 proof assistant. Output only a Lean 4 tactic \
   script inside a single ```lean fenced block. No explanations."

let build_body ~model ~(prompt : string) : string =
  Yojson.Safe.to_string
    (`Assoc [
       "model", `String model;
       "temperature", `Float 0.0;
       "messages", `List [
         `Assoc [ "role", `String "system";
                  "content", `String system_prompt ];
         `Assoc [ "role", `String "user";
                  "content", `String prompt ];
       ];
     ])

(* --- curl invocation ------------------------------------------------- *)

(** POST [body] to [url]. Returns [(stdout, stderr, exit_code)].
    The optional bearer key is written to curl's stdin config
    ([-K -]) so it never appears in argv; the body goes through a
    temp file (non-secret). Raises [Unix]/[Sys_error] for the
    caller to map. *)
let curl_post ~timeout_ms ~url ~api_key ~(body : string)
  : string * string * int =
  let secs = max 1 ((timeout_ms + 999) / 1000) in
  let body_file = Filename.temp_file "pb_llm_" ".json" in
  Fun.protect
    ~finally:(fun () -> try Sys.remove body_file with _ -> ())
    (fun () ->
       Out_channel.with_open_bin body_file
         (fun oc -> Out_channel.output_string oc body);
       let argv = [|
         curl_binary; "-sS";
         "--max-time"; string_of_int secs;
         "-X"; "POST";
         "-H"; "Content-Type: application/json";
         "--data-binary"; "@" ^ body_file;
         "-K"; "-";          (* read remaining opts (the secret) from stdin *)
         url;
       |] in
       let stdout_ch, stdin_ch, stderr_ch =
         Unix.open_process_args_full argv.(0) argv (Unix.environment ())
       in
       (* curl config syntax: one "key = value" per line. Only the
          Authorization header (the secret) goes here. *)
       (match api_key with
        | Some k when k <> "" ->
          output_string stdin_ch
            (Printf.sprintf "header = \"Authorization: Bearer %s\"\n" k)
        | _ -> ());
       close_out stdin_ch;
       let out, err =
         Adapter.drain_subprocess_streams stdout_ch stderr_ch
       in
       let status =
         Unix.close_process_full (stdout_ch, stdin_ch, stderr_ch)
       in
       let code = match status with
         | Unix.WEXITED n -> n
         | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> -1
       in
       (out, err, code))

(* --- response parsing ------------------------------------------------ *)

(** Pull [choices[0].message.content] out of an OpenAI-style
    response. [None] if the shape doesn't match. *)
let extract_content (raw : string) : string option =
  match Yojson.Safe.from_string raw with
  | exception _ -> None
  | j ->
    let ( >>= ) o f = Option.bind o f in
    let mem k = function
      | `Assoc xs -> List.assoc_opt k xs
      | _ -> None
    in
    (mem "choices" j) >>= (function
      | `List (c0 :: _) -> Some c0
      | _ -> None)
    >>= mem "message"
    >>= mem "content"
    >>= (function `String s -> Some s | _ -> None)

(** Extract the Lean tactic script from the model's reply: the
    first ```lean (or bare ```) fenced block, else the trimmed
    whole content. *)
let extract_script (content : string) : string =
  let lines = String.split_on_char '\n' content in
  let is_fence l =
    let t = String.trim l in
    String.length t >= 3 && String.sub t 0 3 = "```"
  in
  let rec collect acc inside = function
    | [] -> List.rev acc
    | l :: rest ->
      if is_fence l then
        (if inside then List.rev acc else collect acc true rest)
      else if inside then collect (l :: acc) inside rest
      else collect acc inside rest
  in
  match collect [] false lines with
  | [] -> String.trim content
  | body -> String.trim (String.concat "\n" body)

(* --- cert minting ---------------------------------------------------- *)

let mk_cert ~(ir : Ir.t) ~model ~script ~timeout_ms : Certificate.t =
  let fragment =
    let f = ir.logic_classification.first_order_fragment in
    if f = "" then "none" else f
  in
  {
    cert_version = "1.0";
    tier = 3;
    format = "lean-tactic-script";
    goal = ir.goal;
    dispatch_context_hash = Hash.sha256_of_json (Codec.to_json ir);
    rewrite_trace_hash = "sha256:" ^ String.make 64 '0';
    backend = {
      name = "llm";
      version = model;
      config_hash = "sha256:" ^ String.make 64 '0';
    };
    resources = {
      wall_time_ms = timeout_ms; memory_peak_kb = 0;
      budget_consumed = None;
    };
    refinement_record = {
      adapter = "llm";
      adapter_version = "0";
      specializations = [];
      fragment;
      auxiliary = Some (`Assoc [ "model", `String model ]);
    };
    payload = Tier3_proof_trace {
      trace_format = "lean-tactic-script";
      trace_data = `String script;
      trace_dialect_features =
        Some [ "llm_generated"; "unverified_until_kernel_replay" ];
      trace_annotations =
        Some "LLM-suggested Lean tactic script. NOT verified by the \
              broker — soundness rests entirely on the home system \
              replaying it through its kernel (audit H1); a failed \
              replay is a tactic failure, never an axiom.";
    };
  }

(* --- top-level dispatch --------------------------------------------- *)

let version = "0"

let dispatch (ir : Ir.t) : Adapter.result =
  match Sys.getenv_opt "PROOF_BROKER_LLM_ENDPOINT" with
  | None | Some "" ->
    (* Fail closed: no endpoint ⇒ this adapter does not run. The
       broker records the failed attempt and proceeds. *)
    Failed (Solver_error {
      stderr = "LLM endpoint not configured \
                (set PROOF_BROKER_LLM_ENDPOINT)";
    })
  | Some url ->
    let api_key = Sys.getenv_opt "PROOF_BROKER_LLM_API_KEY" in
    let model =
      Option.value (Sys.getenv_opt "PROOF_BROKER_LLM_MODEL")
        ~default:"default"
    in
    let timeout_ms = timeout_of_ir ir in
    let prompt = render_prompt ir in
    let body = build_body ~model ~prompt in
    (try
       let stdout, stderr, code =
         curl_post ~timeout_ms ~url ~api_key ~body
       in
       if code <> 0 then
         Failed (Solver_error {
           stderr = Printf.sprintf "curl exit=%d: %s" code
             (if stderr = "" then stdout else stderr);
         })
       else
         (match extract_content stdout with
          | None ->
            Failed (Parse_error {
              stage = "response";
              detail = "no choices[0].message.content in LLM response";
            })
          | Some content ->
            let script = extract_script content in
            if String.trim script = "" then
              Failed (Parse_error {
                stage = "response";
                detail = "LLM returned an empty tactic script";
              })
            else
              Cert (mk_cert ~ir ~model ~script ~timeout_ms))
     with
     | Unix.Unix_error (e, _, _) ->
       Failed (Solver_error {
         stderr = "could not spawn curl: " ^ Unix.error_message e;
       })
     | Sys_error msg -> Failed (Solver_error { stderr = msg }))

let adapter : Adapter.t = {
  name = "llm";
  version;
  dispatch;
}

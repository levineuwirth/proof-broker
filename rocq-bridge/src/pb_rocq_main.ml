module Cert = Proof_broker.Certificate
module Ir = Proof_broker.Ir

let adapter_registry () : (string, Proof_broker.Adapter.t) Hashtbl.t =
  let r = Hashtbl.create 8 in
  Hashtbl.replace r "cvc4"    Proof_broker.Adapter_cvc4.adapter;
  Hashtbl.replace r "cvc5"    Proof_broker.Adapter_cvc5.adapter;
  Hashtbl.replace r "z3"      Proof_broker.Adapter_z3.adapter;
  (* Phase-3 Rocq parity: bind the same adapter set as the Lean
     side's FFI registry (see sdk/ffi/proof_broker_ffi.ml). Vampire
     is required by the HOL test; Adapter_llm fail-closes when
     PROOF_BROKER_LLM_ENDPOINT is unset, so binding it costs
     nothing and the dispatch driver records the (failed) attempt
     in the audit log. *)
  Hashtbl.replace r "vampire" Proof_broker.Adapter_vampire.adapter;
  Hashtbl.replace r "llm"     Proof_broker.Adapter_llm.adapter;
  r

let attempts_summary (attempts : Proof_broker.Dispatch.attempt list) : string =
  String.concat ", "
    (List.map (fun (a : Proof_broker.Dispatch.attempt) ->
       Printf.sprintf "%s=%s"
         a.adapter (Proof_broker.Dispatch.outcome_kind a.outcome))
       attempts)

let cert_one_line (cert : Cert.t) : string =
  Printf.sprintf "tier=%d format=%s backend=%s/%s"
    cert.tier cert.format cert.backend.name cert.backend.version

(* Mirrors lean-bridge/ProofBroker/Tactic.lean's countShellNodes.
   Used in the verbose form's IR-shape line. *)
let rec count_shell_nodes : Ir.shell_term -> int = function
  | Var _ | Const _ | Num_lit _ | Opaque _ -> 1
  | Forall { body; _ } | Exists { body; _ } -> 1 + count_shell_nodes body
  | Lambda { body; _ } -> 1 + count_shell_nodes body
  | Not { operand } -> 1 + count_shell_nodes operand
  | Implies { antecedent; consequent } ->
    1 + count_shell_nodes antecedent + count_shell_nodes consequent
  | And { left; right } | Or { left; right } ->
    1 + count_shell_nodes left + count_shell_nodes right
  | Eq { left; right; _ } ->
    1 + count_shell_nodes left + count_shell_nodes right
  | App { args; _ } ->
    1 + List.fold_left (fun acc x -> acc + count_shell_nodes x) 0 args

let now_ms () = int_of_float (Unix.gettimeofday () *. 1000.)

(* --- shared dispatch + verify path --------------------------------- *)

(* Resolve the manifest list. [None] = default order sorted by tier
   descending; [Some names] = user-supplied order respected verbatim
   (mirrors Lean's [proof_broker [cvc5, z3]] discipline — the bracket
   list is a priority lever, not just a filter). *)
let resolve_manifests (names : Names.Id.t list option)
  : Proof_broker.Manifest.t list =
  match names with
  | None ->
    Proof_broker.Manifest.sort_by_max_tier_descending
      (Manifest_loading.load_default ())
  | Some ids ->
    Manifest_loading.load_named (List.map Names.Id.to_string ids)

(* Path data captured for both verbose-form rendering and plain-form
   summaries. Mirrors Lean's [ExtractionPath]. *)
type path = {
  ir : Ir.t;
  attempts : Proof_broker.Dispatch.attempt list;
  cert : Cert.t option;
  verify_reason : Proof_broker.Verifier.reason option;
  reify_ms : int;
  dispatch_ms : int;
  verify_ms : int;
}

let build_path (gl : Proofview.Goal.t)
              (names : Names.Id.t list option) : path =
  let t0 = now_ms () in
  let ir =
    try Reifier.build_ir gl
    with Reifier.Reify_error msg ->
      CErrors.user_err Pp.(str "proof_broker: " ++ str msg)
  in
  let t1 = now_ms () in
  let manifests = resolve_manifests names in
  let adapters = adapter_registry () in
  let result = Proof_broker.Dispatch.run ~manifests ~adapters ir in
  let t2 = now_ms () in
  let verify_reason = match result.cert with
    | None -> None
    | Some cert -> Some (Proof_broker.Verifier.verify ~trace:None cert ir)
  in
  let t3 = now_ms () in
  {
    ir;
    attempts = result.attempts;
    cert = result.cert;
    verify_reason;
    reify_ms = t1 - t0;
    dispatch_ms = t2 - t1;
    verify_ms = t3 - t2;
  }

(* Render the verbose multi-line summary, layout matched to Lean's
   [renderPath]. *)
let render_path (p : path) : string =
  let n_fv = List.length p.ir.context.free_vars in
  let n_hyp = List.length p.ir.context.hypotheses in
  let n_goal = count_shell_nodes p.ir.goal.shell in
  let frag = p.ir.logic_classification.first_order_fragment in
  let ir_line =
    Printf.sprintf "  ir:       %d free var(s), %d %s, %d goal node(s), \
                    fragment=%s"
      n_fv n_hyp
      (if n_hyp = 1 then "hypothesis" else "hypotheses")
      n_goal frag
  in
  let dispatch_line =
    Printf.sprintf "  dispatch: %dms, %d attempt(s)"
      p.dispatch_ms (List.length p.attempts)
  in
  let attempt_lines =
    List.map (fun (a : Proof_broker.Dispatch.attempt) ->
      Printf.sprintf "              %s → %s"
        a.adapter (Proof_broker.Dispatch.outcome_kind a.outcome))
      p.attempts
  in
  let cert_line = match p.cert with
    | None -> "  cert:     none"
    | Some c ->
      Printf.sprintf "  cert:     tier=%d, format=%s" c.tier c.format
  in
  let verify_line = match p.verify_reason with
    | None -> "  verify:   skipped"
    | Some r ->
      let kind = Proof_broker.Verifier.kind_of_reason r in
      let ok = match r with
        | Verified_envelope | Verified_farkas
        | Verified_case_split | Verified_tier3
        | Verified_tier3_provenance -> true
        | _ -> false
      in
      Printf.sprintf "  verify:   %dms, ok=%b (%s)" p.verify_ms ok kind
  in
  String.concat "\n"
    ([ "proof_broker:"; ir_line; dispatch_line ]
     @ attempt_lines @ [ cert_line; verify_line ])

(* --- closure logic (cert-gated lia / lra) -------------------------- *)

(* Invoke a registered Stdlib tactic by parsing its name through the
   Ltac entry. The string-parse round trip is the idiom for calling
   a name-resolved tactic from an OCaml plugin (see
   tacentries.ml:494 in rocq-runtime). [Goal.enter] defers the
   parse/intern so [Global.env] doesn't fire during plugin module
   init. *)
let invoke_named_tactic (name : string) : unit Proofview.tactic =
  Proofview.Goal.enter (fun _ ->
    let raw =
      Procq.parse_string Ltac_plugin.Pltac.tactic name
    in
    let glob =
      Ltac_plugin.Tacintern.intern_pure_tactic
        (Ltac_plugin.Tacintern.make_empty_glob_sign ~strict:false) raw
    in
    Ltac_plugin.Tacinterp.eval_tactic glob)

let invoke_lia = invoke_named_tactic "lia"
let invoke_lra = invoke_named_tactic "lra"

(* UF closer chain. Tries [congruence] first (handles equality goals
   like [f x = f y] from [x = y], [f a b = f a a] from [a = b],
   [f (g x) = f (g y)] from [x = y]); falls back to
   [subst; assumption] for predicate-shape modus-ponens
   ([P y] from [P x] and [x = y]). Both arms are axiom-free in Rocq
   Stdlib; the [Print Assumptions] line on UF tests should report
   "Closed under the global context". *)
let invoke_uf =
  invoke_named_tactic
    "first [ congruence | (subst; assumption) | (subst; reflexivity) ]"

(* HOL closer (roadmap §Phase 3 #1 home-side, Rocq parity slice).
   Mirrors Lean's [ReifierExt.holCloser] extension hook: the core
   plugin only knows the tactic NAME; the actual aesop-equivalent
   reach is provided by an opt-in package (rocq-bridge/hammer,
   the [ProofBrokerHammer] coq.theory, which redefines
   [proof_broker_hol_closer] to [hauto] when imported), exactly
   the way [ProofBrokerMathlib] supplies [linarith] / [aesop] on
   the Lean side. With no opt-in registered the default Ltac in
   [theories/ProofBrokerHol.v] fails with a directive to import
   the hammer package, so an un-registered HOL goal is a tactic
   failure — never an admitted axiom (audit H1). *)
let invoke_hol_closer = invoke_named_tactic "proof_broker_hol_closer"

(* Map cert fragment to a closer tactic. Mirrors the Lean side's
   [closeOrFail] dispatch. The cert-verification gate keeps these
   paths sound; [lia] / [lra] / the UF chain / the HOL closer's
   replayed proof term are themselves axiom-checkable (the trust
   gate gates the test theorem's [Print Assumptions] line), so
   closures along these paths don't introduce a trust axiom. *)
let closer_for_fragment fragment : unit Proofview.tactic =
  match fragment with
  | "LIA" -> invoke_lia
  | "LRA" -> invoke_lra
  | "UF" -> invoke_uf
  | "HOL" | "FOL" -> invoke_hol_closer
  | other ->
    CErrors.user_err Pp.(
      str (Printf.sprintf
             "proof_broker: closer for fragment %s not yet wired \
              (LIA, LRA, UF, HOL, FOL are the fragments with a \
              cert-gated closer in the core plugin)"
             other))

(* Alethe walker (Rocq parity R-9, mirror of Lean's
   [tryAletheWalkerLIA]). For an [alethe-2024] Tier-3 trace, try
   walking the cert's trace into a kernel proof term ("cert IS the
   proof") before the goal is re-proven by [lia]. Returns a tactic
   that FAILS — so the caller's [tclORELSE] falls through to [lia]
   — when there is no alethe-2024 string trace or the parse fails;
   otherwise delegates to [Alethe_walker.walk_proof_into_goal],
   whose own failures (unsupported rule, type mismatch) are already
   tactic-level. Audit H1: a walker failure is a tactic failure
   that falls through to [lia], never an admitted theorem. *)
let try_alethe_walker_lia (cert : Cert.t) : unit Proofview.tactic =
  match cert.payload with
  | Tier3_proof_trace { trace_format = "alethe-2024";
                        trace_data = `String trace; _ } ->
    (match Alethe_walker.parse_trace trace with
     | Ok proof -> Alethe_walker.walk_proof_into_goal proof
     | Error msg ->
       Tacticals.tclZEROMSG
         (Pp.str ("proof_broker: alethe walker parse failed: " ^ msg)))
  | _ ->
    Tacticals.tclZEROMSG
      (Pp.str "proof_broker: cert is not an alethe-2024 string trace")

(* LIA-arm closer that prefers the Alethe walker, falling back to
   [lia] on any walker failure (no alethe trace / parse error /
   unsupported rule / walked-term type mismatch). All other
   fragments are unchanged — the walker only ever ADDS an attempt
   ahead of the existing [lia], never replaces a closer. *)
let closer_for_fragment_with_walker (cert : Cert.t) (fragment : string)
    : unit Proofview.tactic =
  match fragment with
  | "LIA" ->
    Proofview.tclORELSE
      (try_alethe_walker_lia cert)
      (fun _ -> invoke_lia)
  | _ -> closer_for_fragment fragment

(* Primary closer chain: fragment-keyed dispatch for verified
   reasons, plus the LLM-replay arm for [rocq-tactic-script]
   certs. Renamed from [close_or_fail] in M3.c — the public
   [close_or_fail] (below) is now a wrapper that catches a
   primary failure and tries LLM-assisted Tier-3 reconstruction
   before re-raising the error. *)
let close_or_fail_primary (p : path) : unit Proofview.tactic =
  match p.cert, p.verify_reason with
  | None, _ ->
    CErrors.user_err Pp.(
      str "proof_broker: no cert minted; attempts: " ++
      str (attempts_summary p.attempts))
  | Some cert, Some r ->
    let kind = Proof_broker.Verifier.kind_of_reason r in
    (match r with
     (* LLM-as-backend home-side (roadmap §Phase 3 #3, Rocq
        parity M2). The cert is an untrusted oracle the OCaml
        verifier deliberately leaves soundness-unchecked
        ([Tier3_replay_deferred], envelope-ok only). Route the
        trace through [Llm_replay.replay_script]: kernel replay
        + an axiom-footprint subset check against the classical
        Rocq Stdlib allowlist. Audit H1: a hallucinated [admit]
        or [Axiom Foo] is a tactic failure, never an admitted
        theorem. *)
     | Tier3_replay_deferred { trace_format = "rocq-tactic-script" } ->
       (* M3.b: tightened to only accept the Rocq-flavored cert.
          A [lean-tactic-script] cert reaching the Rocq closer is
          a configuration error (LLM adapter saw this bridge as
          Lean-flavored), not a tactic-soundness issue — surface
          it as a clear user error rather than silently trying to
          parse Lean tactics as Ltac. *)
       (match cert.payload with
        | Tier3_proof_trace { trace_data = `String script; _ } ->
          Llm_replay.replay_script script
        | _ ->
          CErrors.user_err Pp.(
            str "proof_broker: Tier-3 replay-deferred cert payload \
                 is not a string trace; cannot replay"))
     | Tier3_replay_deferred { trace_format } ->
       CErrors.user_err Pp.(
         str (Printf.sprintf
                "proof_broker: LLM cert has trace_format=%S but the \
                 Rocq home-system replayer only accepts \
                 'rocq-tactic-script'. The LLM adapter likely saw \
                 this IR as a Lean source_system; ensure the Rocq \
                 reifier sets ir.source_system.name = \"rocq\" so \
                 [Adapter_llm.dialect_of_ir] picks the Rocq dialect."
                trace_format))
     | Verified_envelope | Verified_farkas
     | Verified_case_split | Verified_tier3
     (* Verified_tier3_provenance gates the home-system closer
        (kernel check, audit H1) exactly as Verified_farkas gates
        lia: the OCaml-side TSTP verifier accepted the cert's
        envelope + provenance (no smuggled axioms, refutes the
        negated goal, reaches $false), so the registered
        proof_broker_hol_closer (hauto, opted-in via
        ProofBrokerHammer) can produce a kernel-checked proof
        term. Same arm the Lean closer added when M2 (TSTP
        verifier) shipped — Verified_tier3_provenance is the
        gate for the Vampire HOL path. *)
     | Verified_tier3_provenance ->
       closer_for_fragment_with_walker cert cert.refinement_record.fragment
     | Tier_check_deferred _ ->
       (* Tier 0 oracle path: no soundness verifier ran but the
          envelope checked out and the solver returned [unsat]. The
          fragment-keyed closer is the actual proof emitter
          (congruence / decide / etc.); the cert's role is gating
          (we know the goal is provable) rather than carrying the
          proof. Mirror lean-bridge's [closeOrFail] envelope-only
          acceptance — the trust footprint is identical. *)
       closer_for_fragment_with_walker cert cert.refinement_record.fragment
     | _ ->
       CErrors.user_err Pp.(
         str (Printf.sprintf
                "proof_broker: cert minted but verifier rejected (reason=%s, %s)"
                kind (cert_one_line cert))))
  | Some _, None ->
    (* Should not happen: cert present => verify ran. *)
    CErrors.user_err Pp.(
      str "proof_broker: internal — cert present but verify outcome missing")

(* --- M3.c: LLM-assisted Tier-3 reconstruction fallback ----------- *)

(* Run [Llm_replay.replay_script] on a candidate the LLM produced
   via reconstruction (rather than the primary LLM-as-backend
   path). On success, emit a [Feedback.msg_info] line naming the
   source trace format so the audit trail of how the goal closed
   is visible in the build output. Mirror of Lean's
   [replayReconstructedScript]. *)
let replay_reconstructed_script (trace_format : string)
    (script : string) : unit Proofview.tactic =
  let announce =
    Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
      Feedback.msg_info (Pp.str (Printf.sprintf
        "proof_broker: closed via LLM Tier-3 reconstruction \
         (%s trace → Rocq Ltac script, kernel-checked, audit H1)."
        trace_format))))
  in
  Proofview.tclBIND (Llm_replay.replay_script script) (fun () -> announce)

(* Decide whether to invoke LLM-assisted reconstruction on the
   current cert + return a fallback tactic if so. Gates (no-op
   unless all hold):
   * a cert is in hand,
   * tier is 3 with a [Tier3_proof_trace] payload,
   * [trace_format] is not already [rocq-tactic-script] (which the
     primary LLM-replay arm at the top of [close_or_fail_primary]
     handles),
   * the SDK's [Llm_reconstruct.translate] returns a non-empty
     script (so this is silent when no endpoint is configured —
     the primary failure is re-raised).

   The translate call runs immediately when this function is
   invoked; callers should only invoke it from the [tclORELSE]
   handler so the HTTP request is lazy (fires only on primary
   failure). *)
let try_llm_reconstruct (ir : Ir.t) (cert_opt : Cert.t option)
  : unit Proofview.tactic option =
  match cert_opt with
  | None -> None
  | Some (cert : Cert.t) ->
    if cert.tier <> 3 then None
    else match cert.payload with
    | Tier3_proof_trace { trace_format = "rocq-tactic-script"; _ } ->
      None
    | Tier3_proof_trace { trace_format; _ } ->
      (match Proof_broker.Llm_reconstruct.translate ir cert with
       | Error _ -> None
       | Ok script ->
         Some (replay_reconstructed_script trace_format script))
    | _ -> None

(* Public closer: try the primary fragment-keyed chain; on any
   failure, try LLM-assisted Tier-3 reconstruction before
   re-raising the primary error. Mirror of Lean's [closeOrFail]
   try/catch wrap. Audit H1: the reconstruction path goes
   through the SAME audit gate [replay_reconstructed_script] →
   [Llm_replay.replay_script] uses for primary
   [rocq-tactic-script] certs — kernel replay + axiom-footprint
   subset check — so the LLM never widens the trust base. *)
let close_or_fail (p : path) : unit Proofview.tactic =
  Proofview.tclORELSE
    (close_or_fail_primary p)
    (fun (primary_exn, primary_info) ->
      match try_llm_reconstruct p.ir p.cert with
      | None -> Proofview.tclZERO ~info:primary_info primary_exn
      | Some fallback -> fallback)

(* --- public entry points ------------------------------------------- *)

let run_close (names : Names.Id.t list option) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let path = build_path gl names in
    close_or_fail path)

(* Walker-STRICT closer: like [run_close], but closes the goal ONLY
   via the Alethe walker on the dispatched cert — no [lia] fallback,
   no LLM reconstruction. End-to-end coverage for the production
   cvc5 -> walker -> kernel path: a live solve must mint a Tier-3
   alethe-2024 cert AND the walker must reconstruct it into a kernel
   term, or the tactic FAILS. The production [proof_broker] wraps the
   walker in [tclORELSE _ lia], so a regression in the live walker
   path (cert-envelope shape, trace extraction, walk) is silently
   masked by the fallback there; this entry point removes the mask so
   that path is guarded. Test-only — production goals should use
   [proof_broker], which degrades gracefully. *)
let run_close_walker (names : Names.Id.t list option) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let path = build_path gl names in
    match path.cert, path.verify_reason with
    | None, _ ->
      CErrors.user_err Pp.(
        str "proof_broker_walker: no cert minted; attempts: " ++
        str (attempts_summary path.attempts))
    | Some _, None ->
      CErrors.user_err Pp.(
        str "proof_broker_walker: internal — cert without verify")
    | Some cert, Some _ ->
      try_alethe_walker_lia cert)

let run_test (names : Names.Id.t list option) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let path = build_path gl names in
    let line = match path.cert, path.verify_reason with
      | Some cert, Some r ->
        Printf.sprintf "[proof_broker] %s verify=%s"
          (cert_one_line cert) (Proof_broker.Verifier.kind_of_reason r)
      | None, _ ->
        Printf.sprintf "[proof_broker] no cert; attempts: %s"
          (attempts_summary path.attempts)
      | Some _, None ->
        "[proof_broker] internal — cert without verify"
    in
    Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
      Feedback.msg_notice (Pp.str line))))

let run_verbose (names : Names.Id.t list option) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let path = build_path gl names in
    let summary = render_path path in
    let print_then_close =
      Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
        Feedback.msg_notice (Pp.str summary)))
    in
    Proofview.tclTHEN print_then_close (close_or_fail path))

(* --- term-mode entry point ---------------------------------------- *)

(* Single-goal term-mode pipeline: build IR + dispatch + verify +
   close. Extracted as a separate function so the recursive dispatch
   in [run_close_term] can call it after applying a goal-normalization
   tactic (Z.le_ge / Z.lt_gt / Z.le_antisymm), letting each post-
   normalization subgoal trigger its own fresh solver dispatch.
   Mirrors lean-bridge's [runTermModeOnGoal]. *)
let run_close_term_single (gl : Proofview.Goal.t)
    (names : Names.Id.t list option) : unit Proofview.tactic =
  let path = build_path gl names in
  let wrap_unsupported tac =
    try tac
    with Term_mode.Unsupported msg ->
      CErrors.user_err Pp.(
        str (Printf.sprintf
               "proof_broker_term: %s — fall back to plain \
                proof_broker if you want lia-based closure"
               msg))
  in
  match path.cert, path.verify_reason with
  | None, _ ->
    CErrors.user_err Pp.(
      str "proof_broker_term: no cert minted; attempts: " ++
      str (attempts_summary path.attempts))
  | Some cert, Some Verified_farkas ->
    (match cert.payload with
     | Tier1_witness { witness_kind = Farkas; witness_data; _ } ->
       wrap_unsupported (Term_mode.close_term path.ir witness_data)
     | _ ->
       CErrors.user_err Pp.(
         str "proof_broker_term: cert payload is not a Tier 1 Farkas \
              witness for a verified_farkas reason"))
  | Some cert, Some Verified_case_split ->
    (* Tier 2 case-split: cert payload is a [Tier2_lemma_list] with
       [strategy_hint = "case_split_farkas"]. Closer destructs the
       disjunctive IR hypothesis and applies the matching lemma's
       Tier 1 Farkas witness per branch via the existing term-mode
       machinery. The verifier has already re-checked every per-
       branch witness against the IR extended with the case
       hypothesis, so we trust the partition + arithmetic; the
       term-mode reconstruction makes the trust footprint
       proof-term-visible (no [lra] / [lia] on the per-branch
       arithmetic). *)
    (match cert.payload with
     | Tier2_lemma_list { lemmas_used; strategy_hint = "case_split_farkas";
                          structural_hint } ->
       wrap_unsupported
         (Term_mode.close_term_case_split path.ir lemmas_used structural_hint)
     | _ ->
       CErrors.user_err Pp.(
         str "proof_broker_term: cert is verified_case_split but payload \
              isn't a Tier 2 case_split_farkas lemma list"))
  | Some _, Some r ->
    let kind = Proof_broker.Verifier.kind_of_reason r in
    CErrors.user_err Pp.(
      str (Printf.sprintf
             "proof_broker_term: verify reason %s — term-mode closer \
              requires verified_farkas or verified_case_split (try \
              [proof_broker_term [z3]] / [proof_broker_term [cvc5]] to \
              force a structurally-extractable adapter)"
             kind))
  | Some _, None ->
    CErrors.user_err Pp.(
      str "proof_broker_term: internal — cert present without verify")

(* Term-mode entry point with goal-shape dispatch. For [>=] / [>] /
   [=] goals we normalize first and recurse — each post-normalization
   subgoal triggers a fresh solver dispatch via [run_close_term_single].

   Universe-aware: [Z.le_ge] / [Z.lt_gt] / [Z.le_antisymm] for [Z];
   [Rle_ge] / [Rlt_gt] / [Rle_antisym] for [R]. The universe tag is
   the discriminator embedded in [goal_kind]'s comparator variants.

   Equality goals split into two [<=] subgoals (one per direction of
   the antisymmetry lemma); both are closed by separate Tier 1 Farkas
   certs, matching lean-bridge's [evalProofBrokerTerm] equality path.
   The two-dispatch cost is the price of staying inside single-
   witness Farkas scope — [~(a = b)] is the disjunction
   [a < b \/ b < a] and would need Tier 2 case-split to handle in
   one shot. *)
let rec run_close_term (names : Names.Id.t list option) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let goal_ty = Proofview.Goal.concl gl in
    let antisym_tac = function
      | Term_mode.U_Z -> "apply Z.le_antisymm"
      | Term_mode.U_R -> "apply Rle_antisym"
    and ge_tac = function
      | Term_mode.U_Z -> "apply Z.le_ge"
      | Term_mode.U_R -> "apply Rle_ge"
    and gt_tac = function
      | Term_mode.U_Z -> "apply Z.lt_gt"
      | Term_mode.U_R -> "apply Rlt_gt"
    in
    match Term_mode.goal_kind sigma goal_ty with
    | Some (Term_mode.Goal_eq (_, _, tag)) ->
      Proofview.tclTHEN
        (invoke_named_tactic (antisym_tac tag))
        (run_close_term names)
    | Some (Term_mode.Goal_ge (_, _, tag)) ->
      Proofview.tclTHEN
        (invoke_named_tactic (ge_tac tag))
        (run_close_term names)
    | Some (Term_mode.Goal_gt (_, _, tag)) ->
      Proofview.tclTHEN
        (invoke_named_tactic (gt_tac tag))
        (run_close_term names)
    | _ ->
      run_close_term_single gl names)

(** Unit tests for [Dispatch].

    Coverage:
    * Empty manifest list → no cert, no attempts.
    * Single matching manifest with bound adapter → cert minted on a
      provable IR; attempt log is one [Succeeded] entry.
    * Capability mismatch → adapter not invoked; attempt is
      [Skipped capability-reason].
    * Bound adapter returns Failed (sat) → attempt records the
      failure; no cert.
    * Unbound adapter (manifest matches but no implementation in the
      registry) → [No_implementation] attempt.
    * Multiple manifests in priority order: the first non-matching
      one is skipped; the matching one runs. Order-of-attempts
      matches input order.
    * stop_on_success: when a cert is minted, subsequent manifests
      are not exercised. *)

open Proof_broker

let cvc4_available () : bool =
  Sys.command "which cvc4 > /dev/null 2>&1" = 0

let with_cvc4 f =
  if not (cvc4_available ()) then
    Printf.printf "[skip] cvc4 not on PATH\n"
  else f ()

(* --- IR builders ----------------------------------------------------- *)

let trivial_logic ~fragment : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = fragment;
  decidable_theory = None;
}

let make_ir
      ?(fragment = "LIA")
      ?(free_vars = []) ?(hypotheses = [])
      (goal_shell : Ir.shell_term) : Ir.t = {
  ir_version = "1.0";
  source_system = { name = "test"; version = "0.0" };
  tier = "goal";
  logic_classification = trivial_logic ~fragment;
  goal = { shell = goal_shell; payloads = None };
  context = { type_vars = []; free_vars; hypotheses; library_slice = None };
  type_metadata = [];
  definitional_metadata = [];
  library_provenance = [];
  user_directives = None;
}

(** IR: n + m = 10, 0 <= m, ⊢ n <= 10  — provable in LIA. *)
let provable_lia_ir () =
  let n = Ir.Var { name = "n" } in
  let m = Ir.Var { name = "m" } in
  let ten = Ir.Num_lit { value = "10"; ty = "Int" } in
  let zero = Ir.Num_lit { value = "0"; ty = "Int" } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = Eq {
      ty = "Int";
      left = App { symbol = "Int.add"; type_args = []; args = [ n; m ] };
      right = ten;
    };
  } in
  let h3 : Ir.hypothesis = {
    name = "h3";
    shell = App { symbol = "LE.le"; type_args = []; args = [ zero; m ] };
  } in
  make_ir
    ~free_vars:[ { name = "n"; ty = "Int" }; { name = "m"; ty = "Int" } ]
    ~hypotheses:[ h1; h3 ]
    (App { symbol = "LE.le"; type_args = []; args = [ n; ten ] })

let unprovable_lia_ir () =
  (* No hypotheses, ⊢ n <= 10. n unconstrained ⇒ sat. *)
  let n = Ir.Var { name = "n" } in
  let ten = Ir.Num_lit { value = "10"; ty = "Int" } in
  make_ir
    ~free_vars:[ { name = "n"; ty = "Int" } ]
    (App { symbol = "LE.le"; type_args = []; args = [ n; ten ] })

(* --- Manifest builders ----------------------------------------------- *)

let cvc4_manifest () : Manifest.t = {
  manifest_version = "1.0";
  adapter = "cvc4";
  adapter_version = "1.8";
  backends_supported = Some [ "cvc4" ];
  logic_fragments = [ "LIA"; "LRA" ];
  type_constructions = [ "primitive"; "type_variable_via_specialization" ];
  max_order = "first_order";
  tiers_produced = [ 0 ];
  trace_formats_produced = None;
  witness_kinds_produced = None;
  preferred_rewrite_pipeline = None;
  concurrency = None;
}

(** A manifest for an adapter that only accepts BV; LIA goals will
    be skipped via [Logic_out_of_fragment]. *)
let bv_only_manifest () : Manifest.t = {
  (cvc4_manifest ()) with
  adapter = "bv-fake";
  adapter_version = "0.0";
  logic_fragments = [ "BV" ];
}

(** A higher-tier manifest stand-in for sort-helper tests.
    Doesn't need a real adapter binding since we never run it. *)
let high_tier_manifest ?(adapter = "synthetic-tier2") () : Manifest.t = {
  (cvc4_manifest ()) with
  adapter;
  adapter_version = "0.0";
  tiers_produced = [ 0; 1; 2 ];
}

(* --- Adapter registry helpers ---------------------------------------- *)

let registry_with_cvc4 () : (string, Adapter.t) Hashtbl.t =
  let h = Hashtbl.create 4 in
  Hashtbl.replace h "cvc4" Adapter_cvc4.adapter;
  h

let empty_registry () : (string, Adapter.t) Hashtbl.t =
  Hashtbl.create 4

(* --- tests ---------------------------------------------------------- *)

let test_empty_manifests () =
  let r = Dispatch.run
    ~manifests:[] ~adapters:(empty_registry ())
    (provable_lia_ir ())
  in
  Alcotest.(check bool) "no cert" true (Option.is_none r.cert);
  Alcotest.(check int) "no attempts" 0 (List.length r.attempts)

let test_capability_skip () =
  (* IR is LIA; manifest only does BV; no cvc4 spawn even if cvc4 binding
     present. *)
  let r = Dispatch.run
    ~manifests:[ bv_only_manifest () ]
    ~adapters:(empty_registry ())
    (provable_lia_ir ())
  in
  Alcotest.(check bool) "no cert" true (Option.is_none r.cert);
  Alcotest.(check int) "1 attempt" 1 (List.length r.attempts);
  let a = List.hd r.attempts in
  Alcotest.(check string) "skipped adapter is bv-fake" "bv-fake" a.adapter;
  match a.outcome with
  | Skipped (Logic_out_of_fragment _) -> ()
  | _ -> Alcotest.fail "expected Skipped Logic_out_of_fragment"

let test_no_implementation () =
  (* Manifest matches but no adapter binding. *)
  let r = Dispatch.run
    ~manifests:[ cvc4_manifest () ]
    ~adapters:(empty_registry ())
    (provable_lia_ir ())
  in
  Alcotest.(check bool) "no cert" true (Option.is_none r.cert);
  Alcotest.(check int) "1 attempt" 1 (List.length r.attempts);
  match (List.hd r.attempts).outcome with
  | No_implementation -> ()
  | _ -> Alcotest.fail "expected No_implementation"

let test_succeeded () =
  with_cvc4 @@ fun () ->
  let r = Dispatch.run
    ~manifests:[ cvc4_manifest () ]
    ~adapters:(registry_with_cvc4 ())
    (provable_lia_ir ())
  in
  Alcotest.(check bool) "cert minted" true (Option.is_some r.cert);
  Alcotest.(check int) "1 attempt" 1 (List.length r.attempts);
  match (List.hd r.attempts).outcome with
  | Succeeded _ -> ()
  | _ -> Alcotest.fail "expected Succeeded"

let test_failed () =
  with_cvc4 @@ fun () ->
  let r = Dispatch.run
    ~manifests:[ cvc4_manifest () ]
    ~adapters:(registry_with_cvc4 ())
    (unprovable_lia_ir ())
  in
  Alcotest.(check bool) "no cert" true (Option.is_none r.cert);
  Alcotest.(check int) "1 attempt" 1 (List.length r.attempts);
  match (List.hd r.attempts).outcome with
  | Failed Sat_returned -> ()
  | _ -> Alcotest.fail "expected Failed Sat_returned"

let test_two_manifests_first_skipped_second_succeeds () =
  with_cvc4 @@ fun () ->
  let r = Dispatch.run
    ~manifests:[ bv_only_manifest (); cvc4_manifest () ]
    ~adapters:(registry_with_cvc4 ())
    (provable_lia_ir ())
  in
  Alcotest.(check bool) "cert minted" true (Option.is_some r.cert);
  Alcotest.(check int) "2 attempts" 2 (List.length r.attempts);
  let a0 = List.nth r.attempts 0 in
  let a1 = List.nth r.attempts 1 in
  Alcotest.(check string) "first attempt adapter" "bv-fake" a0.adapter;
  Alcotest.(check string) "second attempt adapter" "cvc4" a1.adapter;
  (match a0.outcome with
   | Skipped (Logic_out_of_fragment _) -> ()
   | _ -> Alcotest.fail "expected first attempt Skipped");
  match a1.outcome with
  | Succeeded _ -> ()
  | _ -> Alcotest.fail "expected second attempt Succeeded"

let test_stop_on_success () =
  with_cvc4 @@ fun () ->
  (* Two cvc4-shaped manifests; stop_on_success means only the first
     is exercised. We rename the second so they don't violate
     uniqueness, but the registry maps both names to the cvc4
     adapter. *)
  let m1 = cvc4_manifest () in
  let m2 = { (cvc4_manifest ()) with adapter = "cvc4-twin" } in
  let registry = Hashtbl.create 4 in
  Hashtbl.replace registry "cvc4" Adapter_cvc4.adapter;
  Hashtbl.replace registry "cvc4-twin" Adapter_cvc4.adapter;
  let r = Dispatch.run
    ~manifests:[ m1; m2 ]
    ~adapters:registry
    (provable_lia_ir ())
  in
  Alcotest.(check bool) "cert minted" true (Option.is_some r.cert);
  Alcotest.(check int) "stop after first success: 1 attempt" 1
    (List.length r.attempts);
  Alcotest.(check string) "first manifest used" "cvc4"
    (List.hd r.attempts).adapter

let test_continue_past_success () =
  with_cvc4 @@ fun () ->
  let m1 = cvc4_manifest () in
  let m2 = { (cvc4_manifest ()) with adapter = "cvc4-twin" } in
  let registry = Hashtbl.create 4 in
  Hashtbl.replace registry "cvc4" Adapter_cvc4.adapter;
  Hashtbl.replace registry "cvc4-twin" Adapter_cvc4.adapter;
  let r = Dispatch.run
    ~stop_on_success:false
    ~manifests:[ m1; m2 ]
    ~adapters:registry
    (provable_lia_ir ())
  in
  Alcotest.(check int) "all attempts exercised" 2
    (List.length r.attempts);
  Alcotest.(check bool) "cert minted from one of them" true
    (Option.is_some r.cert)

(** [Manifest.sort_by_max_tier_descending] floats higher-tier
    manifests to the front and is stable on ties. *)
let test_sort_by_max_tier_descending () =
  let cvc4 = cvc4_manifest () in
  let cvc5 = high_tier_manifest ~adapter:"cvc5-like" () in
  let other_tier0 = { (cvc4_manifest ()) with adapter = "other-tier0" } in
  (* Mixed input: tier-0 then tier-2 then tier-0. *)
  let sorted = Manifest.sort_by_max_tier_descending
    [ cvc4; cvc5; other_tier0 ]
  in
  let names = List.map (fun (m : Manifest.t) -> m.adapter) sorted in
  Alcotest.(check (list string)) "tier-2 first, ties keep input order"
    [ "cvc5-like"; "cvc4"; "other-tier0" ] names;
  (* Stability check: two same-tier manifests preserve their input order. *)
  let sorted2 = Manifest.sort_by_max_tier_descending [ cvc4; other_tier0 ] in
  let names2 = List.map (fun (m : Manifest.t) -> m.adapter) sorted2 in
  Alcotest.(check (list string)) "stable on ties"
    [ "cvc4"; "other-tier0" ] names2

(* --- concurrent driver (run_parallel) -------------------------------- *)

(* Synthetic in-process adapters: no subprocess, a controllable
   delay, and a fixed result. They let the grace-window / tier-
   selection / ordering logic be tested deterministically without
   a solver. Generous timing margins keep them robust on CI. *)

let mk_cert ~tier : Certificate.t =
  let payload : Certificate.payload =
    if tier = 3 then
      Tier3_proof_trace {
        trace_format = "tstp-fof"; trace_data = `String "synthetic";
        trace_dialect_features = None; trace_annotations = None }
    else
      Tier0_oracle { claim = "proved"; backend_attestation = None }
  in
  {
    cert_version = "1.0";
    tier;
    format = (if tier = 3 then "tstp-fof" else "oracle");
    goal = { shell = Ir.Const { name = "True" }; payloads = None };
    dispatch_context_hash = "sha256:" ^ String.make 64 '0';
    rewrite_trace_hash = "sha256:" ^ String.make 64 '1';
    backend = { name = "synthetic"; version = "0";
                config_hash = "sha256:" ^ String.make 64 '0' };
    resources = { wall_time_ms = 0; memory_peak_kb = 0;
                  budget_consumed = None };
    refinement_record = { adapter = "synthetic"; adapter_version = "0";
                          specializations = []; fragment = "LIA";
                          auxiliary = None };
    payload;
  }

let mk_adapter name ~delay_ms ~(result : Adapter.result) : Adapter.t = {
  name;
  version = "0";
  dispatch = (fun ~rewrite_trace_hash:_ _ir ->
    if delay_ms > 0 then Unix.sleepf (float_of_int delay_ms /. 1000.);
    result);
}

let synthetic_manifest name : Manifest.t =
  { (cvc4_manifest ()) with adapter = name; adapter_version = "0" }

let registry_of (xs : Adapter.t list) : (string, Adapter.t) Hashtbl.t =
  let h = Hashtbl.create 8 in
  List.iter (fun (a : Adapter.t) -> Hashtbl.replace h a.name a) xs;
  h

let succeeded (a : Dispatch.attempt) = match a.outcome with
  | Dispatch.Succeeded _ -> true | _ -> false

let test_par_single_success () =
  let a = mk_adapter "s1" ~delay_ms:0 ~result:(Cert (mk_cert ~tier:0)) in
  let r = Dispatch.run_parallel
    ~manifests:[ synthetic_manifest "s1" ] ~adapters:(registry_of [a])
    (provable_lia_ir ()) in
  Alcotest.(check bool) "cert minted" true (Option.is_some r.cert);
  Alcotest.(check int) "one attempt" 1 (List.length r.attempts);
  Alcotest.(check bool) "attempt succeeded" true
    (succeeded (List.hd r.attempts))

let test_par_grace_prefers_higher_tier () =
  (* Fast Tier-0 + slightly slower Tier-3, both finish well within
     a 2 s grace window ⇒ the Tier-3 cert is selected. *)
  let a0 = mk_adapter "fast0" ~delay_ms:0 ~result:(Cert (mk_cert ~tier:0)) in
  let a3 = mk_adapter "slow3" ~delay_ms:60 ~result:(Cert (mk_cert ~tier:3)) in
  let r = Dispatch.run_parallel ~grace_window_ms:2000
    ~manifests:[ synthetic_manifest "fast0"; synthetic_manifest "slow3" ]
    ~adapters:(registry_of [a0; a3]) (provable_lia_ir ()) in
  match r.cert with
  | Some c -> Alcotest.(check int) "higher tier wins" 3 c.tier
  | None -> Alcotest.fail "expected a cert"

let test_par_grace_is_bounded () =
  (* Fast Tier-0, very slow Tier-3, tiny grace window ⇒ decision
     fires after the window with only the Tier-0 cert in hand. *)
  let a0 = mk_adapter "fast0" ~delay_ms:0 ~result:(Cert (mk_cert ~tier:0)) in
  let a3 = mk_adapter "slow3" ~delay_ms:400 ~result:(Cert (mk_cert ~tier:3)) in
  let r = Dispatch.run_parallel ~grace_window_ms:50
    ~manifests:[ synthetic_manifest "fast0"; synthetic_manifest "slow3" ]
    ~adapters:(registry_of [a0; a3]) (provable_lia_ir ()) in
  (match r.cert with
   | Some c -> Alcotest.(check int) "grace-bounded: Tier 0 returned" 0 c.tier
   | None -> Alcotest.fail "expected a cert");
  (* The superseded still-running runner is recorded, in input
     order, as a Timeout — not dropped. *)
  Alcotest.(check int) "both attempts present" 2 (List.length r.attempts);
  (match (List.nth r.attempts 1).outcome with
   | Dispatch.Failed Adapter.Timeout -> ()
   | _ -> Alcotest.fail "slow runner should be Failed Timeout")

let test_par_latency_first () =
  (* grace 0 ⇒ first cert wins even if a higher tier is in flight. *)
  let a0 = mk_adapter "fast0" ~delay_ms:0 ~result:(Cert (mk_cert ~tier:0)) in
  let a3 = mk_adapter "slow3" ~delay_ms:200 ~result:(Cert (mk_cert ~tier:3)) in
  let r = Dispatch.run_parallel ~grace_window_ms:0
    ~manifests:[ synthetic_manifest "fast0"; synthetic_manifest "slow3" ]
    ~adapters:(registry_of [a0; a3]) (provable_lia_ir ()) in
  match r.cert with
  | Some c -> Alcotest.(check int) "latency-first: Tier 0" 0 c.tier
  | None -> Alcotest.fail "expected a cert"

let test_par_attempts_input_order () =
  (* Completion order (b fast, a slow) must not affect the
     attempts order, which is always input/manifest order. *)
  let a = mk_adapter "a" ~delay_ms:80
            ~result:(Failed Adapter.Sat_returned) in
  let b = mk_adapter "b" ~delay_ms:0 ~result:(Cert (mk_cert ~tier:0)) in
  let r = Dispatch.run_parallel ~grace_window_ms:2000
    ~manifests:[ synthetic_manifest "a"; synthetic_manifest "b" ]
    ~adapters:(registry_of [a; b]) (provable_lia_ir ()) in
  Alcotest.(check (list string)) "attempts in input order"
    [ "a"; "b" ] (List.map (fun x -> x.Dispatch.adapter) r.attempts);
  Alcotest.(check bool) "cert from b" true (Option.is_some r.cert)

let test_par_all_skipped () =
  (* A BV-only manifest is skipped on a LIA goal; no runner, no
     cert, the skip is recorded. *)
  let r = Dispatch.run_parallel
    ~manifests:[ bv_only_manifest () ] ~adapters:(empty_registry ())
    (provable_lia_ir ()) in
  Alcotest.(check bool) "no cert" true (Option.is_none r.cert);
  Alcotest.(check int) "one attempt" 1 (List.length r.attempts);
  (match (List.hd r.attempts).outcome with
   | Dispatch.Skipped _ -> ()
   | _ -> Alcotest.fail "expected Skipped")

let test_par_all_fail () =
  let a = mk_adapter "a" ~delay_ms:0 ~result:(Failed Adapter.Sat_returned) in
  let b = mk_adapter "b" ~delay_ms:0
            ~result:(Failed Adapter.Unknown_returned) in
  let r = Dispatch.run_parallel
    ~manifests:[ synthetic_manifest "a"; synthetic_manifest "b" ]
    ~adapters:(registry_of [a; b]) (provable_lia_ir ()) in
  Alcotest.(check bool) "no cert" true (Option.is_none r.cert);
  Alcotest.(check int) "both attempts" 2 (List.length r.attempts);
  Alcotest.(check bool) "none succeeded" true
    (not (List.exists succeeded r.attempts))

(* --- R2: rewrite pipeline inside the dispatch driver ----------------- *)

(** Echo adapter: mints a cert stamping exactly what the driver hands
    it — the [rewrite_trace_hash] argument and the hash of the IR it
    was dispatched on. The trace-plumbing tests below assert on the
    minted cert, so they prove the driver→adapter handoff rather
    than trusting a fixed synthetic result. *)
let echo_adapter name : Adapter.t = {
  name;
  version = "0";
  dispatch = (fun ~rewrite_trace_hash ir ->
    let c = mk_cert ~tier:0 in
    Cert { c with
      goal = ir.Ir.goal;
      dispatch_context_hash = Hash.sha256_of_json (Codec.to_json ir);
      rewrite_trace_hash });
}

(** [provable_lia_ir] with a propositional redex: the [0 <= m]
    hypothesis is wrapped as [True ∧ (0 <= m)], which the default
    dispatch pipeline's prop-simp pass rewrites (And_True_left) —
    so dispatching it produces a non-identity trace. *)
let redex_lia_ir () =
  let ir = provable_lia_ir () in
  let hyps =
    List.map (fun (h : Ir.hypothesis) ->
      if h.name = "h3" then
        { h with shell = Ir.And {
            left = Const { name = "True" }; right = h.shell } }
      else h)
      ir.context.hypotheses
  in
  { ir with context = { ir.context with hypotheses = hyps } }

let trace_hash (tr : Trace.t) : string =
  Hash.canonical_sha256 (Trace.to_json tr)

let ir_hash (ir : Ir.t) : string =
  Hash.sha256_of_json (Codec.to_json ir)

let test_run_identity_trace () =
  let input = provable_lia_ir () in
  let r = Dispatch.run
    ~manifests:[ synthetic_manifest "echo" ]
    ~adapters:(registry_of [ echo_adapter "echo" ]) input in
  Alcotest.(check bool) "trace is identity" true (Trace.is_identity r.trace);
  Alcotest.(check int) "both default passes traced" 2
    (List.length r.trace.entries);
  Alcotest.(check string) "trace starts at the input IR"
    (ir_hash input) r.trace.initial_ir_hash;
  Alcotest.(check string) "final_ir is the input IR"
    (ir_hash input) (ir_hash r.final_ir);
  match r.cert with
  | None -> Alcotest.fail "expected a cert"
  | Some c ->
    Alcotest.(check string) "cert stamps the trace's canonical hash"
      (trace_hash r.trace) c.rewrite_trace_hash;
    Alcotest.(check bool) "no zero-sentinel trace hash" false
      (c.rewrite_trace_hash = "sha256:" ^ String.make 64 '0');
    Alcotest.(check string) "cert addresses final_ir"
      (ir_hash r.final_ir) c.dispatch_context_hash

let test_run_non_identity_trace () =
  let input = redex_lia_ir () in
  let r = Dispatch.run
    ~manifests:[ synthetic_manifest "echo" ]
    ~adapters:(registry_of [ echo_adapter "echo" ]) input in
  Alcotest.(check bool) "trace is NOT identity" false
    (Trace.is_identity r.trace);
  Alcotest.(check bool) "final_ir differs from input" false
    (ir_hash r.final_ir = ir_hash input);
  Alcotest.(check string) "trace endpoints bracket the rewrite"
    (ir_hash r.final_ir) r.trace.final_ir_hash;
  Alcotest.(check string) "trace starts at the input IR"
    (ir_hash input) r.trace.initial_ir_hash;
  match r.cert with
  | None -> Alcotest.fail "expected a cert"
  | Some c ->
    Alcotest.(check string) "cert stamps the trace's canonical hash"
      (trace_hash r.trace) c.rewrite_trace_hash;
    Alcotest.(check string) "cert addresses final_ir, not the input"
      (ir_hash r.final_ir) c.dispatch_context_hash;
    (* Attack surface (R2 gate): a cert minted on final_ir can NOT
       be replayed against the original IR — the envelope check
       fails by hash mismatch, with or without the trace. *)
    (match Verifier.verify ~trace:(Some r.trace) c input with
     | Hash_mismatch { field = "dispatch_context_hash"; _ } -> ()
     | other ->
       Alcotest.failf "replay against original IR must hash-mismatch, got %s"
         (Verifier.kind_of_reason other));
    (* Against final_ir with the true trace the envelope passes
       (Tier 0 ⇒ deferred tier check). *)
    (match Verifier.verify ~trace:(Some r.trace) c r.final_ir with
     | Tier_check_deferred _ -> ()
     | other ->
       Alcotest.failf "expected tier_check_deferred, got %s"
         (Verifier.kind_of_reason other));
    (* A tampered trace (entry dropped) is rejected. *)
    let tampered = { r.trace with entries = [] } in
    (match Verifier.verify ~trace:(Some tampered) c r.final_ir with
     | Hash_mismatch { field = "rewrite_trace_hash"; _ } -> ()
     | other ->
       Alcotest.failf "tampered trace must hash-mismatch, got %s"
         (Verifier.kind_of_reason other))

let test_par_trace_plumbing () =
  let input = redex_lia_ir () in
  let r = Dispatch.run_parallel
    ~manifests:[ synthetic_manifest "echo" ]
    ~adapters:(registry_of [ echo_adapter "echo" ]) input in
  Alcotest.(check bool) "trace is NOT identity" false
    (Trace.is_identity r.trace);
  Alcotest.(check string) "trace endpoints bracket the rewrite"
    (ir_hash r.final_ir) r.trace.final_ir_hash;
  match r.cert with
  | None -> Alcotest.fail "expected a cert"
  | Some c ->
    Alcotest.(check string) "cert stamps the trace's canonical hash"
      (trace_hash r.trace) c.rewrite_trace_hash;
    Alcotest.(check string) "cert addresses final_ir"
      (ir_hash r.final_ir) c.dispatch_context_hash

let () =
  Alcotest.run "dispatch" [
    "driver", [
      Alcotest.test_case "empty manifests" `Quick test_empty_manifests;
      Alcotest.test_case "capability skip" `Quick test_capability_skip;
      Alcotest.test_case "no implementation" `Quick test_no_implementation;
      Alcotest.test_case "succeeded" `Quick test_succeeded;
      Alcotest.test_case "failed (sat)" `Quick test_failed;
      Alcotest.test_case "first skipped, second succeeds"
        `Quick test_two_manifests_first_skipped_second_succeeds;
      Alcotest.test_case "stop_on_success default" `Quick test_stop_on_success;
      Alcotest.test_case "continue past success"
        `Quick test_continue_past_success;
    ];
    "preference", [
      Alcotest.test_case "sort_by_max_tier_descending"
        `Quick test_sort_by_max_tier_descending;
    ];
    "concurrent", [
      Alcotest.test_case "single success" `Quick test_par_single_success;
      Alcotest.test_case "grace prefers higher tier" `Quick
        test_par_grace_prefers_higher_tier;
      Alcotest.test_case "grace is bounded" `Quick
        test_par_grace_is_bounded;
      Alcotest.test_case "latency-first (grace 0)" `Quick
        test_par_latency_first;
      Alcotest.test_case "attempts in input order" `Quick
        test_par_attempts_input_order;
      Alcotest.test_case "all skipped" `Quick test_par_all_skipped;
      Alcotest.test_case "all fail" `Quick test_par_all_fail;
    ];
    "pipeline-in-dispatch", [
      Alcotest.test_case "identity trace through run"
        `Quick test_run_identity_trace;
      Alcotest.test_case "non-identity trace through run"
        `Quick test_run_non_identity_trace;
      Alcotest.test_case "trace plumbing through run_parallel"
        `Quick test_par_trace_plumbing;
    ];
  ]

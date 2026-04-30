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
  ]

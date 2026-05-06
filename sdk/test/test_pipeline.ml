(** Unit tests for the pipeline driver.

    Coverage:
    * Empty pipeline produces no entries; initial_ir_hash equals
      final_ir_hash.
    * Single-pass run is structurally equivalent to invoking the pass
      directly: same IR, same single trace entry.
    * Two-pass run chains: entries[0].after_hash equals
      entries[1].before_hash, and the trace's initial/final hashes
      bracket the chain.
    * Unknown-pass entries are synthesized as [Failed] without
      blowing up the pipeline.
    * [stop_on_failure = true] halts the chain after a failed entry;
      [stop_on_failure = false] continues on the pre-failure IR.
    * Pass that raises an OCaml exception is caught and surfaces as
      [Failed] with [diagnostics] populated.
    * Codec round-trip: [Pipeline.config_of_json] composed with
      [config_to_json] is identity on a non-trivial config.
    * Trace document codec round-trip preserves all fields.
*)

open Proof_broker

(* --- IR scaffolding (mirrors test_propositional_simplify) ------------ *)

let trivial_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "FOL";
  decidable_theory = None;
}

let trivial_source : Ir.source_system = { name = "test"; version = "0.0" }

let make_ir (shell : Ir.shell_term) : Ir.t =
  {
    ir_version = "1.0";
    source_system = trivial_source;
    tier = "goal";
    logic_classification = trivial_logic;
    goal = { shell; payloads = None };
    context = {
      type_vars = [];
      free_vars = [];
      hypotheses = [];
      library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

let v name : Ir.shell_term = Var { name }
let c_true : Ir.shell_term = Const { name = "True" }
let mk_and l r : Ir.shell_term = And { left = l; right = r }

(* --- Tests ------------------------------------------------------------ *)

let test_empty_pipeline () =
  let ir = make_ir (v "p") in
  let config : Pipeline.config = {
    pipeline = [];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let _ir', trace = Pipeline.run config ir in
  Alcotest.(check int) "no entries" 0 (List.length trace.entries);
  Alcotest.(check string) "initial == final hash"
    trace.initial_ir_hash trace.final_ir_hash;
  Alcotest.(check string) "trace_version" "1.0" trace.trace_version

let test_single_pass_matches_direct () =
  (* Single-pass pipeline run should be observationally equivalent to
     invoking the pass directly. *)
  let ir = make_ir (mk_and c_true (v "p")) in
  let direct = Propositional_simplify.run ir in
  let config : Pipeline.config = {
    pipeline = [ { pass = "propositional_simplification"; config = None } ];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let pipe_ir, trace = Pipeline.run config ir in
  Alcotest.(check int) "one entry" 1 (List.length trace.entries);
  let entry = List.hd trace.entries in
  Alcotest.(check string) "same pass name"
    direct.trace.pass entry.pass;
  Alcotest.(check string) "same before_hash"
    direct.trace.before_hash entry.before_hash;
  Alcotest.(check string) "same after_hash"
    direct.trace.after_hash entry.after_hash;
  Alcotest.(check bool) "same IR shape"
    true (direct.ir.goal.shell = pipe_ir.goal.shell);
  Alcotest.(check string) "trace.initial_ir_hash = entry.before_hash"
    entry.before_hash trace.initial_ir_hash;
  Alcotest.(check string) "trace.final_ir_hash = entry.after_hash"
    entry.after_hash trace.final_ir_hash

let test_two_pass_chain () =
  (* Two passes back-to-back: the second pass must see the first
     pass's output, and the trace's hash chain must be locally
     consistent (entries[0].after_hash == entries[1].before_hash). *)
  let ir = make_ir (mk_and c_true (v "p")) in
  let config : Pipeline.config = {
    pipeline = [
      { pass = "propositional_simplification"; config = None };
      { pass = "definition_unfolding"; config = None };
    ];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let _ir', trace = Pipeline.run config ir in
  Alcotest.(check int) "two entries" 2 (List.length trace.entries);
  let e0 = List.nth trace.entries 0 in
  let e1 = List.nth trace.entries 1 in
  Alcotest.(check string) "first entry is propositional_simplification"
    "propositional_simplification" e0.pass;
  Alcotest.(check string) "second entry is definition_unfolding"
    "definition_unfolding" e1.pass;
  Alcotest.(check string) "hash chain: e0.after_hash == e1.before_hash"
    e0.after_hash e1.before_hash;
  Alcotest.(check string) "initial_ir_hash = e0.before_hash"
    e0.before_hash trace.initial_ir_hash;
  Alcotest.(check string) "final_ir_hash = e1.after_hash"
    e1.after_hash trace.final_ir_hash

let test_unknown_pass_is_failed () =
  let ir = make_ir (v "p") in
  let config : Pipeline.config = {
    pipeline = [ { pass = "no_such_pass"; config = None } ];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let _ir', trace = Pipeline.run config ir in
  Alcotest.(check int) "one entry" 1 (List.length trace.entries);
  let e = List.hd trace.entries in
  Alcotest.(check bool) "outcome=Failed"
    true (e.outcome = Some Failed);
  Alcotest.(check string) "pass name preserved"
    "no_such_pass" e.pass;
  Alcotest.(check bool) "diagnostics mentions unknown pass"
    true (match e.diagnostics with
          | Some s -> String.length s > 0
          | None -> false);
  Alcotest.(check string) "Failed leaves IR untouched: hashes equal"
    e.before_hash e.after_hash

let test_stop_on_failure_halts () =
  (* With stop_on_failure=true, an unknown pass at position 0 should
     prevent the second pass from running. *)
  let ir = make_ir (v "p") in
  let config : Pipeline.config = {
    pipeline = [
      { pass = "no_such_pass"; config = None };
      { pass = "propositional_simplification"; config = None };
    ];
    stop_on_failure = true;
    timeout_per_pass_ms = None;
  } in
  let _ir', trace = Pipeline.run config ir in
  Alcotest.(check int) "halts after failure: one entry"
    1 (List.length trace.entries);
  Alcotest.(check string) "halted pass name"
    "no_such_pass" (List.hd trace.entries).pass

let test_continue_on_failure () =
  (* With stop_on_failure=false, a failed pass should not block the
     second pass; both entries must appear. *)
  let ir = make_ir (v "p") in
  let config : Pipeline.config = {
    pipeline = [
      { pass = "no_such_pass"; config = None };
      { pass = "propositional_simplification"; config = None };
    ];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let _ir', trace = Pipeline.run config ir in
  Alcotest.(check int) "both entries recorded" 2 (List.length trace.entries);
  Alcotest.(check string) "second entry ran"
    "propositional_simplification" (List.nth trace.entries 1).pass

let test_exception_capture () =
  (* Register a pass that raises; verify the pipeline catches the
     exception and synthesizes a Failed entry with diagnostics. *)
  Pipeline.register_pass "always_raises"
    (fun _ -> failwith "boom");
  let ir = make_ir (v "p") in
  let config : Pipeline.config = {
    pipeline = [ { pass = "always_raises"; config = None } ];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let _ir', trace = Pipeline.run config ir in
  let e = List.hd trace.entries in
  Alcotest.(check bool) "outcome=Failed" true (e.outcome = Some Failed);
  Alcotest.(check bool) "diagnostics carries 'boom'"
    true (match e.diagnostics with
          | Some s -> String.length s > 0
                      && (try ignore (Str.search_forward
                                        (Str.regexp_string "boom") s 0); true
                          with Not_found -> false)
          | None -> false);
  Alcotest.(check string) "after_hash = before_hash on failure"
    e.before_hash e.after_hash

let test_lying_pass_before_hash () =
  (* A pass that reports a fabricated before_hash should be caught
     and replaced with a Failed entry. The IR going into the next
     step is the pre-pass IR (failure leaves IR untouched). *)
  Pipeline.register_pass "liar_before"
    (fun ir ->
       let dummy_after = Hash.sha256_of_json (Codec.to_json ir) in
       { ir;
         entry = {
           pass = "liar_before";
           version = "1.0";
           before_hash = "sha256:" ^ String.make 64 'd';
           after_hash = dummy_after;
           configuration = None;
           outcome = None;
           inversion_data = None;
           diagnostics = None;
         } });
  let ir = make_ir (v "p") in
  let config : Pipeline.config = {
    pipeline = [ { pass = "liar_before"; config = None } ];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let _ir', trace = Pipeline.run config ir in
  let e = List.hd trace.entries in
  Alcotest.(check bool) "outcome=Failed" true (e.outcome = Some Failed);
  Alcotest.(check string) "before_hash matches initial"
    trace.initial_ir_hash e.before_hash;
  Alcotest.(check string) "after_hash unchanged on rejection"
    e.before_hash e.after_hash;
  Alcotest.(check bool) "diagnostics mentions hash mismatch"
    true (match e.diagnostics with
          | Some s ->
            (try ignore (Str.search_forward
                           (Str.regexp_string "hash mismatch") s 0); true
             with Not_found -> false)
          | None -> false)

let test_lying_pass_after_hash () =
  (* A pass that reports an after_hash that doesn't match its
     actual returned IR should also be flagged. *)
  Pipeline.register_pass "liar_after"
    (fun ir ->
       let real_before = Hash.sha256_of_json (Codec.to_json ir) in
       { ir;
         entry = {
           pass = "liar_after";
           version = "1.0";
           before_hash = real_before;
           after_hash = "sha256:" ^ String.make 64 'e';
           configuration = None;
           outcome = None;
           inversion_data = None;
           diagnostics = None;
         } });
  let ir = make_ir (v "p") in
  let config : Pipeline.config = {
    pipeline = [ { pass = "liar_after"; config = None } ];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let _ir', trace = Pipeline.run config ir in
  let e = List.hd trace.entries in
  Alcotest.(check bool) "outcome=Failed" true (e.outcome = Some Failed);
  Alcotest.(check string) "after_hash unchanged on rejection"
    e.before_hash e.after_hash

let test_lying_pass_breaks_chain_caught () =
  (* A lying pass in the middle of a chain must not corrupt the
     downstream IR. The next pass should see the pre-failure IR. *)
  Pipeline.register_pass "liar_mid"
    (fun _ir ->
       (* Returns an IR different from the input, with a fabricated
          after_hash that matches neither input nor output. *)
       let bogus_ir = make_ir (v "ghost") in
       { ir = bogus_ir;
         entry = {
           pass = "liar_mid";
           version = "1.0";
           before_hash = "sha256:" ^ String.make 64 'a';
           after_hash = "sha256:" ^ String.make 64 'b';
           configuration = None;
           outcome = None;
           inversion_data = None;
           diagnostics = None;
         } });
  let ir = make_ir (v "real") in
  let config : Pipeline.config = {
    pipeline = [
      { pass = "liar_mid"; config = None };
      { pass = "propositional_simplification"; config = None };
    ];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let _ir', trace = Pipeline.run config ir in
  let e0 = List.nth trace.entries 0 in
  let e1 = List.nth trace.entries 1 in
  Alcotest.(check bool) "first pass Failed" true (e0.outcome = Some Failed);
  Alcotest.(check string) "chain remains consistent: e0.after = e1.before"
    e0.after_hash e1.before_hash;
  Alcotest.(check string) "downstream pass saw the original IR"
    trace.initial_ir_hash e1.before_hash

let test_config_codec_round_trip () =
  let config : Pipeline.config = {
    pipeline = [
      { pass = "definition_unfolding";
        config = Some (`Assoc [ "concepts", `List [ `String "fc" ] ]) };
      { pass = "propositional_simplification"; config = None };
    ];
    stop_on_failure = true;
    timeout_per_pass_ms = Some 5000;
  } in
  let j = Pipeline.config_to_json config in
  let config' = Pipeline.config_of_json j in
  let j' = Pipeline.config_to_json config' in
  Alcotest.(check string) "config json round-trip is stable"
    (Yojson.Safe.to_string (Codec.normalize j))
    (Yojson.Safe.to_string (Codec.normalize j'))

let test_trace_codec_round_trip () =
  let ir = make_ir (mk_and c_true (v "p")) in
  let config : Pipeline.config = {
    pipeline = [
      { pass = "propositional_simplification"; config = None };
      { pass = "definition_unfolding"; config = None };
    ];
    stop_on_failure = false;
    timeout_per_pass_ms = None;
  } in
  let _ir', trace = Pipeline.run config ir in
  let j = Trace.to_json trace in
  let trace' = Trace.of_json j in
  let j' = Trace.to_json trace' in
  Alcotest.(check string) "trace json round-trip stable"
    (Yojson.Safe.to_string (Codec.normalize j))
    (Yojson.Safe.to_string (Codec.normalize j'));
  Alcotest.(check int) "entries preserved"
    (List.length trace.entries) (List.length trace'.entries);
  Alcotest.(check string) "initial_ir_hash preserved"
    trace.initial_ir_hash trace'.initial_ir_hash

let () =
  Alcotest.run "pipeline" [
    "driver", [
      Alcotest.test_case "empty pipeline" `Quick test_empty_pipeline;
      Alcotest.test_case "single pass matches direct invocation"
        `Quick test_single_pass_matches_direct;
      Alcotest.test_case "two-pass chain" `Quick test_two_pass_chain;
      Alcotest.test_case "unknown pass yields Failed entry"
        `Quick test_unknown_pass_is_failed;
      Alcotest.test_case "stop_on_failure halts the chain"
        `Quick test_stop_on_failure_halts;
      Alcotest.test_case "continue past failed pass"
        `Quick test_continue_on_failure;
      Alcotest.test_case "exception is captured as Failed"
        `Quick test_exception_capture;
      Alcotest.test_case "pass lying about before_hash flagged"
        `Quick test_lying_pass_before_hash;
      Alcotest.test_case "pass lying about after_hash flagged"
        `Quick test_lying_pass_after_hash;
      Alcotest.test_case "lying mid-pass doesn't corrupt downstream"
        `Quick test_lying_pass_breaks_chain_caught;
    ];
    "codec", [
      Alcotest.test_case "config round-trip"
        `Quick test_config_codec_round_trip;
      Alcotest.test_case "trace document round-trip"
        `Quick test_trace_codec_round_trip;
    ];
  ]

(* R6-001: deterministic preparation and certificate assembly, never search.
   The untrusted proposer supplies witness data; the SDK owns the envelope.
   Arithmetic verification is deliberately a separate process/boundary. *)
open Proof_broker
open Yojson.Safe.Util

let row (input : Farkas_search.input) =
  let relation, (form : Linear_arith.t) = match input.compiled with
    | Farkas.Le p -> "le", p | Farkas.Lt p -> "lt", p | Farkas.Eq p -> "eq", p in
  `Assoc ["name", `String input.name; "relation", `String relation;
    "constant", `String (Linear_arith.rat_to_string form.const);
    "terms", `List (List.map (fun (variable, coefficient) ->
      `Assoc ["variable", `String variable;
              "coefficient", `String (Linear_arith.rat_to_string coefficient)]) form.coeffs)]

let prepare input =
  let ir = Codec.of_json input in
  let final, trace = Pipeline.run Pipeline.default_dispatch_config ir in
  let rows = Farkas_search.compile_inputs final in
  let names = List.map (fun (r : Farkas_search.input) -> r.name) rows in
  let omitted = List.filter_map (fun (h : Ir.hypothesis) ->
    if List.mem h.name names then None else Some (`String h.name)) final.context.hypotheses in
  if not (List.mem "neg_goal" names) then failwith "negated goal is outside the Farkas fragment";
  `Assoc ["input_ir", Codec.to_json ir; "final_ir", Codec.to_json final;
    "trace", Trace.to_json trace; "rows", `List (List.map row rows);
    "farkas_omissions", `List omitted; "fragment", `String (Farkas.effective_fragment final)]

let assemble prepared response config_hash =
  let started = Unix.gettimeofday () in
  let final = Codec.of_json (member "final_ir" prepared) in
  let trace = Trace.of_json (member "trace" prepared) in
  let fragment = Farkas.effective_fragment final in
  let refinement = match Refinement.run ~fragment final with
    | Ok r -> r | Error e -> failwith (Refinement.detail_of_error e) in
  let cert : Certificate.t = {
    cert_version = "1.0"; tier = 1; format = "farkas"; goal = final.goal;
    dispatch_context_hash = Hash.sha256_of_json (Codec.to_json final);
    rewrite_trace_hash = Hash.canonical_sha256 (Trace.to_json trace);
    backend = {name = "r6_fixture_witness"; version = "1"; config_hash};
    resources = {wall_time_ms = int_of_float ((Unix.gettimeofday () -. started) *. 1000.);
                 memory_peak_kb = None; budget_consumed = None};
    refinement_record = {adapter = "r6_fixture_witness"; adapter_version = "1";
      specializations = refinement.specializations; fragment; auxiliary = None};
    payload = Tier1_witness {witness_kind = Farkas; witness_data = member "witness" response;
                            checking_recipe = "lean.farkas_check"};
  } in
  `Assoc ["input_ir", member "input_ir" prepared; "final_ir", Codec.to_json final;
          "trace", Trace.to_json trace; "certificate", Certificate.to_json cert]

let () =
  try
    let result = match Sys.argv.(1) with
      | "prepare" -> prepare (Yojson.Safe.from_file Sys.argv.(2))
      | "assemble" -> assemble (Yojson.Safe.from_file Sys.argv.(2))
          (Yojson.Safe.from_file Sys.argv.(3)) Sys.argv.(4)
      | _ -> failwith "expected prepare or assemble" in
    Yojson.Safe.to_file Sys.argv.(Array.length Sys.argv - 1) result
  with exn -> prerr_endline (Printexc.to_string exn); exit 1

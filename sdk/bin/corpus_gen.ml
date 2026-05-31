(** Walker replay-corpus trace generator.

    Reads hand-authored corpus goals from [<root>/goals/*.json], runs each
    through cvc5 with Alethe proof output, and captures the VERBATIM
    alethe-2024 trace plus the inventory of rules it uses. Outputs:

      <root>/traces/<id>.alethe   the verbatim S-expression trace
      <root>/index.json           { "<id>": {result, rules, steps, ...}, ... }

    The trace fixtures + index are committed so the static coverage gate
    (tools/check_walker_coverage.py) and the dynamic replay (CorpusReplay.v)
    run without a live solver. This generator is re-run to refresh the
    corpus against a new cvc5 (the live-drift job); a stable cvc5 produces a
    stable trace, so a re-run that changes a fixture is a reviewable diff.

    Each goal file is { id, description, coq_goal, ir } where [ir] is a
    full IR document (same schema as examples/, decoded by [Codec.of_json]).
    Only [id] and [ir] are read here; [coq_goal]/[description] are consumed
    downstream by the replay generator. We deliberately bypass
    [Adapter_cvc5.dispatch]'s Tier-1/2/3 ladder and capture the raw proof
    for EVERY unsat: the point is to measure the walker against whatever
    cvc5 emits, including traces using rules no tier (and no walker) yet
    supports.

    Exit 0 if every goal was processed (regardless of per-goal result), 1
    on a usage error or an unreadable goal file. cvc5 must be on PATH. *)

open Proof_broker
module J = Yojson.Safe
module U = Yojson.Safe.Util

let timeout_ms = 10000

type outcome =
  | Unsat of { rules : string list; steps : int; assumes : int; trace : string }
  | Sat
  | Unknown
  | No_proof
  | Error of string

(** Run one IR through cvc5 and classify the result. Mirrors the
    Ir -> SMT-LIB -> solve -> extract-proof prefix of
    [Adapter_cvc5.dispatch], minus the tier ladder. *)
let solve (ir : Ir.t) : outcome =
  let fragment = Farkas.effective_fragment ir in
  match Refinement.run ~fragment ir with
  | Result.Error e ->
    Error (Printf.sprintf "refinement: %s" (Refinement.detail_of_error e))
  | Result.Ok refinement ->
    match Smtlib.emit refinement.refined_ir with
    | Result.Error e ->
      Error (Printf.sprintf "smtlib: %s" (Smtlib.detail_of_error e))
    | Result.Ok script ->
      let body = script.body ^ "(check-sat)\n(get-proof)\n(exit)\n" in
      let stdout, _stderr, _code = Adapter_cvc5.run_solver ~timeout_ms body in
      match Adapter_cvc5.parse_response stdout with
      | Adapter_cvc5.Sat -> Sat
      | Adapter_cvc5.Unknown_resp -> Unknown
      | Adapter_cvc5.Other_resp s -> Error (Printf.sprintf "cvc5: %s" s)
      | Adapter_cvc5.Unsat ->
        match Adapter_cvc5.extract_proof_body stdout with
        | None -> No_proof
        | Some trace ->
          let proof = Alethe.parse trace in
          Unsat {
            rules = Alethe_passthrough.rule_inventory proof;
            steps = List.length proof.steps;
            assumes = List.length proof.assumes;
            trace;
          }

let write_file path contents =
  let oc = open_out path in
  output_string oc contents;
  close_out oc

(** Index entry as JSON, mirroring the [outcome] taxonomy. *)
let entry_json = function
  | Unsat { rules; steps; assumes; _ } ->
    `Assoc [
      "result", `String "unsat";
      "rules", `List (List.map (fun r -> `String r) rules);
      "steps", `Int steps;
      "assumes", `Int assumes;
    ]
  | Sat -> `Assoc [ "result", `String "sat" ]
  | Unknown -> `Assoc [ "result", `String "unknown" ]
  | No_proof -> `Assoc [ "result", `String "no_proof" ]
  | Error detail -> `Assoc [ "result", `String "error"; "detail", `String detail ]

let process_goal ~goals_dir ~traces_dir file =
  let path = Filename.concat goals_dir file in
  let j = J.from_file path in
  let id = j |> U.member "id" |> U.to_string in
  let outcome =
    try solve (Codec.of_json (j |> U.member "ir")) with
    | Codec.Decode_error (msg, _) -> Error (Printf.sprintf "decode: %s" msg)
    | e -> Error (Printexc.to_string e)
  in
  (match outcome with
   | Unsat { trace; _ } ->
     write_file (Filename.concat traces_dir (id ^ ".alethe")) trace
   | _ -> ());
  let summary = match outcome with
    | Unsat { rules; steps; _ } ->
      Printf.sprintf "unsat (%d steps, rules: %s)" steps
        (String.concat ", " rules)
    | Sat -> "sat" | Unknown -> "unknown" | No_proof -> "no_proof"
    | Error d -> "error: " ^ d
  in
  Printf.printf "  %-28s %s\n%!" id summary;
  (id, entry_json outcome)

let () =
  match Sys.argv with
  | [| _; root |] ->
    let goals_dir = Filename.concat root "goals" in
    let traces_dir = Filename.concat root "traces" in
    if not (Sys.file_exists goals_dir) then begin
      Printf.eprintf "no goals dir: %s\n" goals_dir; exit 1
    end;
    if not (Sys.file_exists traces_dir) then Unix.mkdir traces_dir 0o755;
    let files =
      Sys.readdir goals_dir |> Array.to_list
      |> List.filter (fun f -> Filename.check_suffix f ".json")
      |> List.sort compare
    in
    Printf.printf "corpus_gen: %d goal(s)\n%!" (List.length files);
    let entries = List.map (process_goal ~goals_dir ~traces_dir) files in
    write_file (Filename.concat root "index.json")
      (J.pretty_to_string (`Assoc entries) ^ "\n");
    Printf.printf "wrote %s/index.json\n" root
  | _ ->
    Printf.eprintf "usage: corpus_gen <corpus-root>\n"; exit 2

(* Fresh verifier process: reads saved evidence only, never dispatches search. *)
open Proof_broker
let () =
  let stage = ref "certificate_decode" in
  let result = try
    let j = Yojson.Safe.from_file Sys.argv.(1) in
    let get name = Yojson.Safe.Util.member name j in
    let cert = Certificate.of_json (get "certificate") in
    let ir = Codec.of_json (get "final_ir") in
    let trace = Trace.of_json (get "trace") in
    let input = Codec.of_json (get "input_ir") in
    stage := "input_trace_binding";
    if trace.Trace.initial_ir_hash <> Hash.canonical_sha256 (Codec.to_json input) then
      failwith "Rewrite trace does not start at the captured dispatch input";
    stage := "certificate_verification";
    let reason = Verifier.verify ~trace:(Some trace) cert ir in
    let ok = reason = Verifier.Verified_farkas in
    `Assoc ["accepted", `Bool ok; "stage", `String "certificate_verification";
      "reason", Verifier.reason_to_json reason;
      "certificate_hash", `String (Hash.canonical_sha256 (Certificate.to_json cert))]
  with exn ->
    `Assoc ["accepted", `Bool false; "stage", `String !stage;
      "error", `String (Printexc.to_string exn)]
  in
  Yojson.Safe.to_file Sys.argv.(2) result;
  exit (if Yojson.Safe.Util.(result |> member "accepted" |> to_bool) then 0 else 1)

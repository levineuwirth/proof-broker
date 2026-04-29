(** Round-trip a JSON IR document through the OCaml IR types and back.

    Reads from a file path or stdin (when path is "-"); writes the
    re-serialized JSON to stdout. Used by the cross-tool agreement test
    in [tools/test_cross_tool.py] and as a debugging entry point.

    Exit codes: 0 on success, 1 on decode error, 2 on usage error. *)

let read_input = function
  | "-" -> Yojson.Safe.from_channel stdin
  | path -> Yojson.Safe.from_file path

let () =
  match Sys.argv with
  | [| _; src |] ->
    (try
       let input = read_input src in
       let ir = Proof_broker.Codec.of_json input in
       let out = Proof_broker.Codec.to_json ir in
       print_string (Yojson.Safe.pretty_to_string out);
       print_newline ()
     with
     | Proof_broker.Codec.Decode_error (msg, j) ->
       Printf.eprintf "decode_error: %s\nat: %s\n" msg
         (Yojson.Safe.pretty_to_string j);
       exit 1
     | Yojson.Json_error msg ->
       Printf.eprintf "json_parse_error: %s\n" msg;
       exit 1)
  | _ ->
    prerr_endline "usage: round_trip_cli <path|->";
    exit 2

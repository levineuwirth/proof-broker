(** Unit tests for the shared [Adapter] helpers — the R1.8 lazy
    backend-version probe. Uses stub binaries (tiny shell scripts
    written to a temp dir and invoked by absolute path) so no real
    solver is needed. *)

open Proof_broker

let write_stub ~(dir : string) ~(name : string) ~(body : string) : string =
  let path = Filename.concat dir name in
  let oc = open_out path in
  output_string oc ("#!/bin/sh\n" ^ body);
  close_out oc;
  Unix.chmod path 0o755;
  path

let with_temp_dir (f : string -> unit) : unit =
  let dir = Filename.temp_file "pb_probe_test" "" in
  Sys.remove dir;
  Unix.mkdir dir 0o755;
  Fun.protect ~finally:(fun () ->
    Array.iter (fun n -> Sys.remove (Filename.concat dir n))
      (Sys.readdir dir);
    Unix.rmdir dir)
    (fun () -> f dir)

let test_parse_version_token () =
  Alcotest.(check (option string)) "cvc5-style line"
    (Some "1.3.0")
    (Adapter.parse_version_token
       "This is cvc5 version 1.3.0 [git tag 1.3.0 branch HEAD]");
  Alcotest.(check (option string)) "vampire-style line"
    (Some "5.1.0")
    (Adapter.parse_version_token
       "Vampire 5.1.0 (Release build, commit abc on 2026-01-01)");
  Alcotest.(check (option string)) "z3-style line"
    (Some "4.16.0")
    (Adapter.parse_version_token "Z3 version 4.16.0 - 64 bit");
  Alcotest.(check (option string)) "no version token"
    None
    (Adapter.parse_version_token "no digits dot here")

let test_major_minor () =
  Alcotest.(check string) "three components" "1.3"
    (Adapter.major_minor "1.3.0");
  Alcotest.(check string) "two components" "5.1"
    (Adapter.major_minor "5.1");
  Alcotest.(check string) "one component passthrough" "7"
    (Adapter.major_minor "7")

let test_probe_stub_binary () =
  with_temp_dir (fun dir ->
    let stub = write_stub ~dir ~name:"fake-solver"
      ~body:"echo \"FakeSolver version 9.9.9 [stub]\"\n" in
    Alcotest.(check (option string)) "probe reads stub version"
      (Some "9.9.9") (Adapter.probe_version ~binary:stub);
    Alcotest.(check string) "probed_version prefers probe"
      "9.9.9" (Adapter.probed_version ~binary:stub ~fallback:"1.0.0");
    Alcotest.(check bool) "major.minor mismatch vs 1.0" true
      (Adapter.version_mismatch ~binary:stub ~declared:"1.0.0");
    Alcotest.(check bool) "no mismatch vs 9.9.1" false
      (Adapter.version_mismatch ~binary:stub ~declared:"9.9.1"))

let test_probe_memoizes () =
  with_temp_dir (fun dir ->
    (* The stub records each invocation; a second probe of the same
       binary path must not re-run it. *)
    let marker = Filename.concat dir "calls" in
    let stub = write_stub ~dir ~name:"counting-solver"
      ~body:(Printf.sprintf
        "echo run >> %s\necho \"Counting 2.2.2\"\n" marker) in
    ignore (Adapter.probe_version ~binary:stub);
    ignore (Adapter.probe_version ~binary:stub);
    ignore (Adapter.probed_version ~binary:stub ~fallback:"0.0.0");
    let calls =
      let ic = open_in marker in
      let rec count n = match input_line ic with
        | _ -> count (n + 1)
        | exception End_of_file -> close_in ic; n
      in
      count 0
    in
    Alcotest.(check int) "stub spawned exactly once" 1 calls)

let test_probe_missing_binary () =
  Alcotest.(check (option string)) "missing binary probes None"
    None
    (Adapter.probe_version ~binary:"/nonexistent/pb-no-such-solver");
  Alcotest.(check string) "probed_version falls back"
    "3.1.4"
    (Adapter.probed_version ~binary:"/nonexistent/pb-no-such-solver"
       ~fallback:"3.1.4");
  Alcotest.(check bool) "failed probe is never a mismatch"
    false
    (Adapter.version_mismatch ~binary:"/nonexistent/pb-no-such-solver"
       ~declared:"1.2.3")

let test_probe_unparseable_output () =
  with_temp_dir (fun dir ->
    let stub = write_stub ~dir ~name:"mute-solver"
      ~body:"echo \"no version here\"\n" in
    Alcotest.(check (option string)) "unparseable output probes None"
      None (Adapter.probe_version ~binary:stub);
    Alcotest.(check string) "falls back to declared"
      "2.7.1" (Adapter.probed_version ~binary:stub ~fallback:"2.7.1"))

let () =
  Alcotest.run "adapter" [
    "probe", [
      Alcotest.test_case "parse_version_token recognizes solver banners"
        `Quick test_parse_version_token;
      Alcotest.test_case "major_minor prefix"
        `Quick test_major_minor;
      Alcotest.test_case "stub binary probed and compared"
        `Quick test_probe_stub_binary;
      Alcotest.test_case "probe memoized per binary"
        `Quick test_probe_memoizes;
      Alcotest.test_case "missing binary -> None + fallback"
        `Quick test_probe_missing_binary;
      Alcotest.test_case "unparseable banner -> None + fallback"
        `Quick test_probe_unparseable_output;
    ];
  ]

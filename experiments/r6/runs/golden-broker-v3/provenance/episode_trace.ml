(* Process observations, received and sealed by the external supervisor.
   These are not computation attestations. Disabled outside the R6 overlay. *)
let lock = Mutex.create ()
let emit event fields =
  if Sys.getenv_opt "PROOF_BROKER_EPISODE_TRACE" = Some "1" then begin
    let j = `Assoc ["component", `String "sdk"; "event", `String event;
                    "data", `Assoc fields] in
    Mutex.lock lock;
    Fun.protect ~finally:(fun () -> Mutex.unlock lock) (fun () ->
      Printf.eprintf "R6_EVENT %s\n%!" (Yojson.Safe.to_string j))
  end

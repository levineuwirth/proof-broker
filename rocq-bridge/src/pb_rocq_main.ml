(* Phase 2 stub: confirm the plugin loaded and the tactic entry
   point dispatches into OCaml. Real reification + broker call
   land in Phase 3 / Phase 4. *)
let run_default : unit Proofview.tactic =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
    Feedback.msg_notice (Pp.str "[proof_broker] plugin alive (Phase 2 stub)")))

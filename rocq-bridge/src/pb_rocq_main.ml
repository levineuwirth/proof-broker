(* Phase 3: reify the goal + locals into [Ir.t] and print a one-line
   summary (free-var count, hypothesis count, fragment, JSON-encoded
   shell). No broker call yet — that's Phase 4. *)

let summary (ir : Proof_broker.Ir.t) : string =
  Printf.sprintf
    "[proof_broker] reified: %d free var(s), %d hypothesis/es, fragment=%s\n%s"
    (List.length ir.context.free_vars)
    (List.length ir.context.hypotheses)
    ir.logic_classification.first_order_fragment
    (Yojson.Safe.pretty_to_string (Proof_broker.Codec.to_json ir))

let run_default : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let ir =
      try Reifier.build_ir gl
      with Reifier.Reify_error msg ->
        CErrors.user_err Pp.(str "proof_broker: " ++ str msg)
    in
    Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
      Feedback.msg_notice (Pp.str (summary ir)))))

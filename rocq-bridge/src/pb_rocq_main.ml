module Cert = Proof_broker.Certificate

let adapter_registry () : (string, Proof_broker.Adapter.t) Hashtbl.t =
  let r = Hashtbl.create 4 in
  Hashtbl.replace r "cvc4" Proof_broker.Adapter_cvc4.adapter;
  Hashtbl.replace r "cvc5" Proof_broker.Adapter_cvc5.adapter;
  Hashtbl.replace r "z3"   Proof_broker.Adapter_z3.adapter;
  r

let attempts_summary (attempts : Proof_broker.Dispatch.attempt list) : string =
  String.concat ", "
    (List.map (fun (a : Proof_broker.Dispatch.attempt) ->
       Printf.sprintf "%s=%s"
         a.adapter (Proof_broker.Dispatch.outcome_kind a.outcome))
       attempts)

let cert_one_line (cert : Cert.t) : string =
  Printf.sprintf "tier=%d format=%s backend=%s/%s"
    cert.tier cert.format cert.backend.name cert.backend.version

let run_default : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let ir =
      try Reifier.build_ir gl
      with Reifier.Reify_error msg ->
        CErrors.user_err Pp.(str "proof_broker: " ++ str msg)
    in
    let manifests =
      Proof_broker.Manifest.sort_by_max_tier_descending
        (Manifest_loading.load_default ())
    in
    let adapters = adapter_registry () in
    let result = Proof_broker.Dispatch.run ~manifests ~adapters ir in
    (match result.cert with
     | None ->
       CErrors.user_err Pp.(
         str "proof_broker: no cert minted; attempts: " ++
         str (attempts_summary result.attempts))
     | Some cert ->
       let reason =
         Proof_broker.Verifier.verify ~trace:None cert ir
       in
       let kind = Proof_broker.Verifier.kind_of_reason reason in
       let line = Printf.sprintf
         "[proof_broker] %s verify=%s attempts: %s"
         (cert_one_line cert) kind (attempts_summary result.attempts)
       in
       (* Fail loudly on a non-Verified_* reason: the test [.v] files
          treat build success as the gate, so a bad verify must
          surface as a [user_err]. *)
       (match reason with
        | Verified_envelope | Verified_farkas
        | Verified_case_split | Verified_tier3 ->
          Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
            Feedback.msg_notice (Pp.str line)))
        | _ ->
          CErrors.user_err Pp.(str line))))

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

(* --- shared dispatch + verify path --------------------------------- *)

(* Runs the broker against the current goal; returns the cert + the
   verifier's reason on success. Raises [CErrors.user_err] on any
   failure mode the .v test author needs to see (no cert, verify
   rejected, etc.). The two public tactics share this entry point;
   they diverge only on what to do after success. *)
let dispatch_and_verify gl : Cert.t * Proof_broker.Verifier.reason * string =
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
  match result.cert with
  | None ->
    CErrors.user_err Pp.(
      str "proof_broker: no cert minted; attempts: " ++
      str (attempts_summary result.attempts))
  | Some cert ->
    let reason =
      Proof_broker.Verifier.verify ~trace:None cert ir
    in
    let kind = Proof_broker.Verifier.kind_of_reason reason in
    (match reason with
     | Verified_envelope | Verified_farkas
     | Verified_case_split | Verified_tier3 ->
       (cert, reason, kind)
     | _ ->
       CErrors.user_err Pp.(
         str (Printf.sprintf
                "proof_broker: cert minted but verifier rejected (reason=%s, %s)"
                kind (cert_one_line cert))))

(* --- non-closing form: print and return --------------------------- *)

let run_test : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let cert, _reason, kind = dispatch_and_verify gl in
    let line = Printf.sprintf
      "[proof_broker] %s verify=%s" (cert_one_line cert) kind
    in
    Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
      Feedback.msg_notice (Pp.str line))))

(* --- closing form: dispatch + verify + lia ------------------------ *)

(* Invokes Stdlib's [lia] tactic by parsing "lia" through the Ltac
   entry. The string-parse round trip is the idiom for calling a
   registered Ltac tactic from an OCaml plugin (see
   tacentries.ml:494 in rocq-runtime). [Ltac_plugin.Pltac.tactic] is
   the parser entry; [Tacintern.intern_pure_tactic] resolves the
   name in the current environment, and [Tacinterp.eval_tactic]
   runs the resulting glob expression. *)
let invoke_lia : unit Proofview.tactic =
  (* [Goal.enter] defers the body to tactic-run time; without this
     wrapper [parse_string] / [intern_pure_tactic] / [Global.env]
     fire at module-init, which Rocq rejects with "the global
     environment cannot be accessed during the syntactic
     interpretation phase". *)
  Proofview.Goal.enter (fun _ ->
    let raw =
      Procq.parse_string Ltac_plugin.Pltac.tactic "lia"
    in
    let glob =
      Ltac_plugin.Tacintern.intern_pure_tactic
        (Ltac_plugin.Tacintern.make_empty_glob_sign ~strict:false) raw
    in
    Ltac_plugin.Tacinterp.eval_tactic glob)

(* Cert.refinement_record.fragment is "LIA" / "LRA" / etc. Mirrors
   Lean's [closeOrFail]: the cert fragment determines the closer. *)
let close_via_fragment (cert : Cert.t) : unit Proofview.tactic =
  let fragment = cert.refinement_record.fragment in
  if fragment = "LIA" then
    invoke_lia
  else
    CErrors.user_err Pp.(
      str (Printf.sprintf
             "proof_broker: closer for fragment %s not yet wired (LIA only \
              in the core plugin; LRA is a future opt-in symmetric to Lean's \
              ProofBrokerMathlib)"
             fragment))

let run_close : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let cert, _reason, _kind = dispatch_and_verify gl in
    close_via_fragment cert)

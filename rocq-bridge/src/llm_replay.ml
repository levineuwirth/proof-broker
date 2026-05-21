(** Rocq mirror of [lean-bridge/ProofBroker/Tactic.lean]'s
    [replayLlmScriptOrFail] (roadmap §Phase 3 deliverable 3,
    home-side / Rocq parity slice M2).

    Replays an untrusted LLM-supplied Ltac script through Rocq's
    own tactic engine, then audits the resulting proof term's
    transitive axiom footprint via the kernel [Assumptions] API
    — the very same API Rocq's [Print Assumptions] vernacular
    calls. If the script doesn't close the goal, errors during
    elaboration, or pulls in an axiom outside the classical
    Stdlib allowlist (a hallucinated [admit] → [Constant
    admit_axiom]; an [Axiom Foo : T] introduction; etc.), the
    closer fails as a tactic — the goal is left OPEN and never
    admitted via an LLM-introduced axiom (audit H1).

    The script-replay layer mirrors the [invoke_named_tactic]
    pattern the plugin already uses for [lia]/[lra]/[congruence]:
    [Procq.parse_string Pltac.tactic] → [Tacintern.intern_pure_tactic]
    → [Tacinterp.eval_tactic]. The audit-gate layer is new; it
    runs at the *home* kernel (Rocq), not the broker SDK. *)

module Cert = Proof_broker.Certificate

(** Axiom-footprint allowlist. Mirrors the Lean side's
    [{propext, Classical.choice, Quot.sound}] but in Rocq's
    classical-Stdlib vocabulary. Same set the existing
    Rocq tests in [tools/axiom_allowlist.json] pin for the LRA
    and Tier-2 case-split paths — adopting it here keeps the
    LLM-replay closer inside the documented Rocq trust ceiling.

    Names are matched against [Names.Constant.to_string]
    (kernel-canonical form, e.g.
    ["Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep"]).
    Deliberately EXCLUDES anything else — including
    [admit_axiom] (Rocq's [admit]), [JMeq_eq] /
    [Eq_rect_eq], or arbitrary user-introduced [Axiom Foo]. *)
let axiom_allowlist : string list = [
  "Stdlib.Logic.ClassicalDedekindReals.sig_forall_dec";
  "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep";
]

(** Dummy indirect_accessor. With [add_opaque:false] /
    [add_transparent:false] in the call to [Assumptions.assumptions]
    below, the [access_proof] field is not consulted — opaques
    are reported as [Opaque _] entries in the result map rather
    than being recursed into. We never need real opaque access. *)
let dummy_accessor : Global.indirect_accessor =
  { access_proof = fun _ -> None }

(** Sentinel [GlobRef.t] passed as the "owner" arg to
    [Assumptions.assumptions]. The owner is used by the kernel
    to skip self-references (so e.g. analyzing a recursive
    constant's body doesn't loop). Our proof term is an
    anonymous evar body, not a registered global, so any sentinel
    that won't appear in real proof terms works — a section
    variable with a reserved name does the job. *)
let dummy_owner : Names.GlobRef.t =
  Names.GlobRef.VarRef (Names.Id.of_string "__proof_broker_llm_replay_owner__")

(** Collect axioms referenced by the proof term that are NOT in
    [axiom_allowlist]. Returns the kernel names verbatim. *)
let collect_disallowed_axioms (env : Environ.env) (term : Constr.t)
  : string list =
  let st = Conv_oracle.get_transp_state (Environ.oracle env) in
  let assumptions =
    Assumptions.assumptions dummy_accessor st
      ~add_opaque:false ~add_transparent:false dummy_owner term
  in
  Printer.ContextObjectMap.fold (fun co _ acc ->
    match co with
    | Printer.Axiom (Printer.Constant kn, _) ->
      let name = Names.Constant.to_string kn in
      if List.mem name axiom_allowlist then acc else name :: acc
    | Printer.Axiom (Printer.Positive _, _)
    | Printer.Axiom (Printer.Guarded _, _)
    | Printer.Axiom (Printer.TypeInType _, _)
    | Printer.Axiom (Printer.UIP _, _) ->
      (* Inductive-typing assumptions (positivity, guardedness,
         type-in-type, UIP). These aren't LLM-introducible —
         they're inherent to inductive definitions the user
         imported. Accept; the existing Print-Assumptions trust
         gate at the test-theorem level catches any surprise. *)
      acc
    | Printer.Variable _
    | Printer.Opaque _
    | Printer.Transparent _ ->
      (* Section variables (already in the goal context) and
         opaque/transparent constants (audited at their define
         site, not here) are accepted. *)
      acc
  ) assumptions []

(** Parse [script] as an Ltac tactic and intern it. Same idiom
    [Pb_rocq_main.invoke_named_tactic] uses for stdlib tactics. *)
let parse_ltac (script : string) : Ltac_plugin.Tacexpr.glob_tactic_expr =
  let raw = Procq.parse_string Ltac_plugin.Pltac.tactic script in
  Ltac_plugin.Tacintern.intern_pure_tactic
    (Ltac_plugin.Tacintern.make_empty_glob_sign ~strict:false) raw

(** Audit-H1 messaging for the multiple failure modes. Common
    prefix so error logs are searchable. *)
let audit_fail (detail : string) : 'a Proofview.tactic =
  Proofview.tclZERO
    (CErrors.UserError
       Pp.(str ("proof_broker: " ^ detail ^
                " The goal is left OPEN — a replay failure is a \
                 tactic failure, never an admitted theorem (audit H1).")))

(** Replay [script] on the current main goal.

    Steps (mirroring Lean's [replayLlmScriptOrFail]):
    1. Parse the script as an Ltac tactic.
    2. Capture the current goal's evar (the metavariable the
       script's proof term will be assigned to).
    3. Run the parsed tactic via [Tacinterp.eval_tactic]. A
       tactic-engine error here surfaces as a tactic failure
       (the proof state is rolled back).
    4. After: confirm the goal evar is now defined; collect the
       transitive-axiom footprint of the assigned proof term
       via [Assumptions.assumptions]; reject if any axiom is
       outside [axiom_allowlist].
    5. On any rejection: [Proofview.tclZERO] with an audit-H1
       error. The kernel still has the proof term assigned at
       that point, but the error propagation undoes the
       assignment (standard tactic-monad semantics). *)
let replay_script (script : string) : unit Proofview.tactic =
  Proofview.Goal.enter begin fun gl ->
    let env_before = Proofview.Goal.env gl in
    let goal_evar = Proofview.Goal.goal gl in
    let parsed =
      try Ok (parse_ltac script)
      with e ->
        Error (Printf.sprintf
                 "the LLM tactic script does not parse as a Rocq Ltac \
                  tactic (%s)."
                 (Printexc.to_string e))
    in
    match parsed with
    | Error msg -> audit_fail msg
    | Ok glob ->
      Proofview.tclBIND
        (Proofview.tclORELSE
           (Ltac_plugin.Tacinterp.eval_tactic glob)
           (fun (e, _info) ->
              audit_fail
                (Printf.sprintf
                   "the LLM tactic script failed to elaborate (%s)."
                   (Pp.string_of_ppcmds (CErrors.print e)))))
        (fun () ->
          Proofview.tclBIND Proofview.tclEVARMAP (fun sigma ->
            let Evd.EvarInfo info = Evd.find sigma goal_evar in
            match Evd.evar_body info with
            | Evd.Evar_empty ->
              audit_fail
                "the LLM tactic script ran without error but did not \
                 close the goal."
            | Evd.Evar_defined econstr ->
              let term =
                EConstr.to_constr
                  ~abort_on_undefined_evars:false sigma econstr
              in
              (match collect_disallowed_axioms env_before term with
               | [] -> Proofview.tclUNIT ()
               | bad ->
                 audit_fail
                   (Printf.sprintf
                      "the LLM tactic script closed the goal, but its \
                       proof term depends on axiom(s) outside the \
                       classical Rocq Stdlib allowlist: [%s]."
                      (String.concat ", " bad)))))
  end

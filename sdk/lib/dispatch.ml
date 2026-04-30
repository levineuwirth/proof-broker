(** Multi-adapter dispatch driver (spec v1.0 §7).

    Walks an ordered list of [Manifest.t] entries against an IR,
    consulting [Capability_match.check] to decide eligibility, and
    invoking the adapter implementation registered under each
    matching manifest's [adapter] name. Returns the first
    successful certificate plus a per-manifest attempt log so a
    caller can audit (or surface in a dashboard) what was tried,
    what was skipped and why, and what the broker eventually
    landed on.

    Order. The driver iterates manifests in the order they're
    handed in. Callers can sort by adapter preference (latency,
    tier capability, user-supplied priority) before passing the
    list. The driver itself is preference-agnostic.

    Stop condition. The driver stops at the first [Cert _] from
    an adapter, leaving the rest of the manifests un-attempted. A
    [stop_on_success] flag exists for the rare audit case where a
    caller wants every manifest exercised regardless; the default
    is [true].

    Adapter binding. Manifests describe capabilities; they don't
    carry the runnable adapter code. Adapter implementations live
    in OCaml modules ([Adapter_cvc4.adapter], future [Adapter_cvc5],
    ...) and are passed in via the [adapters] table keyed on
    adapter name. A manifest whose adapter has no entry in the
    table surfaces as [No_implementation] — the broker has the
    capability description but no way to invoke it.

    Failure semantics. The driver itself doesn't fail. Every
    eventuality lands in the [attempts] list:
    * [Skipped reason] — capability mismatch.
    * [No_implementation] — manifest matched but no adapter is
      bound to the name.
    * [Failed failure] — adapter ran but didn't produce a cert.
    * [Succeeded cert] — adapter returned a cert (driver stops
      here unless [stop_on_success = false]). *)

type attempt_outcome =
  | Skipped of Capability_match.reason
  | No_implementation
  | Failed of Adapter.failure
  | Succeeded of Certificate.t

type attempt = {
  adapter : string;
  outcome : attempt_outcome;
}

type result = {
  cert : Certificate.t option;
  attempts : attempt list;
}

(** Helper: lift a single attempt outcome to its serialized form for
    the FFI envelope and downstream dashboards. The kind labels are
    intentionally distinct from [Adapter.failure] kinds so a
    consumer can tell "adapter ran and failed" from "adapter
    didn't run." *)
let outcome_kind = function
  | Skipped _ -> "skipped"
  | No_implementation -> "no_implementation"
  | Failed _ -> "failed"
  | Succeeded _ -> "succeeded"

let attempt_to_json (a : attempt) : Yojson.Safe.t =
  let outcome_field =
    match a.outcome with
    | Skipped reason ->
      [ "reason", Capability_match.reason_to_json reason ]
    | No_implementation -> []
    | Failed failure ->
      [ "failure", Adapter.failure_to_json failure ]
    | Succeeded _ ->
      [] (* the cert lives at the top level, not duplicated here *)
  in
  `Assoc ([
    "adapter", `String a.adapter;
    "outcome", `String (outcome_kind a.outcome);
  ] @ outcome_field)

(** Run the driver. [manifests] is the ordered candidate list;
    [adapters] binds adapter names to implementations.
    [stop_on_success = true] (default) returns at the first cert
    minted; [false] exercises every matched adapter. *)
let run
      ?(stop_on_success = true)
      ~(manifests : Manifest.t list)
      ~(adapters : (string, Adapter.t) Hashtbl.t)
      (ir : Ir.t) : result =
  let attempts = ref [] in
  let cert = ref None in
  List.iter (fun (m : Manifest.t) ->
    if Option.is_some !cert && stop_on_success then ()
    else begin
      let outcome =
        match Capability_match.check ir m with
        | (Order_too_high _ | Logic_out_of_fragment _
          | Type_construction_not_supported _) as r ->
          Skipped r
        | Match ->
          (match Hashtbl.find_opt adapters m.adapter with
           | None -> No_implementation
           | Some adapter ->
             (match adapter.dispatch ir with
              | Cert c -> Succeeded c
              | Failed f -> Failed f))
      in
      (match outcome with
       | Succeeded c -> cert := Some c
       | _ -> ());
      attempts := !attempts @ [ { adapter = m.adapter; outcome } ]
    end)
    manifests;
  { cert = !cert; attempts = !attempts }

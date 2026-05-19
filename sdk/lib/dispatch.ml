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
    list — see [Manifest.sort_by_max_tier_descending] for the
    "prefer higher-tier capability" policy the FFI broker uses by
    default. The driver itself is preference-agnostic.

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
      (* Audit #18: prepend then reverse once — O(n) total, vs the
         former [!attempts @ [..]] which is O(n²) over the manifest
         list. Final order is unchanged (input/dispatch order). *)
      attempts := { adapter = m.adapter; outcome } :: !attempts
    end)
    manifests;
  { cert = !cert; attempts = List.rev !attempts }

(** Concurrent dispatch driver (spec v1.0 §7; roadmap §Phase 3 #5).

    Races every capability-eligible adapter in parallel —
    first-valid-wins, with a grace window that prefers the
    highest-tier cert among those received by the decision point.
    The concurrency primitive is the stdlib [Thread] library, not
    [lwt] (recorded reconsideration in [delta.md §2.1]): the
    adapters' [run_solver] is blocking subprocess I/O and OCaml's
    [Unix] blocking calls release the runtime lock, so one thread
    per adapter gives real parallelism with the adapter code
    reused verbatim.

    Selection. Capability matching runs sequentially first (cheap,
    no subprocess) and records [Skipped] / [No_implementation]
    immediately. Each remaining eligible adapter runs on its own
    thread, posting its outcome into a mutex-guarded mailbox; the
    {e calling} thread is the collector and polls that mailbox on a
    short interval (no extra timer/condition thread — see "no
    escaping threads" below). It {e decides} as soon as either
    (a) every runner has finished, or (b) at least one cert has
    arrived and the grace window has elapsed since the first cert.
    Among the certs in hand at the decision point it picks the
    highest [cert.tier] (ties broken by input order — lowest
    manifest index — for determinism). [grace_window_ms <= 0] means
    latency-first: decide as soon as any cert arrives.

    No escaping threads (why this matters). The driver runs inside
    the OCaml runtime embedded in the home-system process via the
    C-FFI shim. An OCaml thread that outlives the synchronous
    dispatch call corrupts that embedded runtime's exit path (a
    short-lived FFI consumer then exits nonzero — observed as the
    [roundtripTest] CI regression). So {b every thread this
    function spawns is joined before it returns}, and there is no
    long-sleeping timer thread to leak: the grace window is a
    wall-clock deadline the polling collector checks itself.

    Cancellation (honest v1 semantics). The {e decision} (which
    cert wins, and the [attempts] snapshot) is taken the instant
    the grace/first-valid condition holds and never changes
    afterwards — a later or higher-tier cert arriving during the
    join wait is ignored, and a runner still in flight at the
    decision is recorded [Failed Timeout]. But because no thread
    may escape, the call only {e returns} once the laggard runner
    threads have themselves terminated; every adapter caps its
    solver with a per-call wall clock limit
    ([Adapter.resolve_timeout_ms]) so that is bounded by the
    slowest eligible solver's own budget. True mid-flight SIGKILL
    would need a cancellation token threaded through [Adapter.t];
    deferred and documented rather than silently approximated
    (cf. the pipeline-timeout known-limitation note).

    The [attempts] list is always in input (manifest) order so the
    result is reproducible regardless of completion order. *)
let run_parallel
      ?(grace_window_ms = 2000)
      ~(manifests : Manifest.t list)
      ~(adapters : (string, Adapter.t) Hashtbl.t)
      (ir : Ir.t) : result =
  let names = Array.of_list (List.map (fun (m : Manifest.t) -> m.adapter) manifests) in
  let n = Array.length names in
  let outcomes : attempt_outcome option array = Array.make n None in
  let runners = ref [] in
  List.iteri (fun i (m : Manifest.t) ->
    match Capability_match.check ir m with
    | (Order_too_high _ | Logic_out_of_fragment _
      | Type_construction_not_supported _) as r ->
      outcomes.(i) <- Some (Skipped r)
    | Match ->
      (match Hashtbl.find_opt adapters m.adapter with
       | None -> outcomes.(i) <- Some No_implementation
       | Some a -> runners := (i, a) :: !runners))
    manifests;
  let runners = List.rev !runners in
  let total = List.length runners in
  let mtx = Mutex.create () in
  let finished = ref 0 in
  let now_ms () = int_of_float (Unix.gettimeofday () *. 1000.) in
  (* Best cert by (max tier, min index). Caller holds [mtx]. *)
  let best_cert () =
    let b = ref None in
    Array.iteri (fun i o ->
      match o with
      | Some (Succeeded c) ->
        (match !b with
         | None -> b := Some (i, c)
         | Some (_, c') -> if c.Certificate.tier > c'.Certificate.tier
                           then b := Some (i, c))
      | _ -> ())
      outcomes;
    !b
  in
  (* Snapshot the result under [mtx]: the winning cert and the
     attempts in input order, runners not yet finished recorded as
     [Failed Timeout] (superseded). *)
  let snapshot () =
    Mutex.lock mtx;
    let chosen = best_cert () in
    let attempts =
      Array.to_list (Array.mapi (fun i o ->
        let outcome = match o with
          | Some ov -> ov
          | None -> Failed Adapter.Timeout
        in
        { adapter = names.(i); outcome })
        outcomes)
    in
    Mutex.unlock mtx;
    { cert = Option.map snd chosen; attempts }
  in
  if total = 0 then snapshot ()
  else begin
    let handles =
      List.map (fun (i, (a : Adapter.t)) ->
        Thread.create (fun () ->
          let o =
            try (match a.dispatch ir with
                 | Cert c -> Succeeded c
                 | Failed f -> Failed f)
            with e ->
              Failed (Adapter.Solver_error {
                stderr = "adapter raised: " ^ Printexc.to_string e })
          in
          Mutex.lock mtx;
          outcomes.(i) <- Some o;
          incr finished;
          Mutex.unlock mtx)
          ())
        runners
    in
    (* Collector = this thread. Poll the mailbox; decide on
       all-finished, or first-valid (grace<=0), or grace-deadline
       elapsed since the first cert. No timer/condition thread. *)
    let decided = ref false in
    let deadline = ref None in
    while not !decided do
      Mutex.lock mtx;
      let have_cert = best_cert () <> None in
      if !finished >= total then decided := true
      else if have_cert && grace_window_ms <= 0 then decided := true
      else begin
        (match !deadline with
         | None -> if have_cert then
             deadline := Some (now_ms () + grace_window_ms)
         | Some d -> if have_cert && now_ms () >= d then decided := true)
      end;
      Mutex.unlock mtx;
      if not !decided then Thread.delay 0.01
    done;
    (* Decision is fixed here; later/lagging certs do not change
       it. *)
    let result = snapshot () in
    (* No OCaml thread may outlive this call (embedded-runtime
       safety): join every runner. Bounded by each solver's own
       per-call wall-clock limit. *)
    List.iter Thread.join handles;
    result
  end

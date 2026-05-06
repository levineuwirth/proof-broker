(** Adapter interface (spec v1.0 §7).

    An adapter takes an [Ir.t] and either returns a [Certificate.t]
    or a typed failure describing why dispatch didn't produce one.
    The interface is intentionally narrow: the broker doesn't need
    to know how the adapter works, only that it can be invoked.

    [name]/[version] identify the adapter and the version of its
    backend (e.g., [name = "cvc4"], [version = "1.8"]). The same
    pair appears verbatim in any [Certificate.backend] this adapter
    mints, so a downstream consumer can correlate cert provenance
    with manifest metadata.

    Failure taxonomy. The dispatch result is either [Cert _] or
    [Failed _], where the failure is one of:
    * [Sat_returned] — solver said the negated goal is satisfiable;
      the home-system goal is not provable (counterexample exists).
    * [Unknown_returned] — solver returned [unknown] (timeout or
      incompleteness on the fragment); broker may try another
      adapter.
    * [Timeout] — broker-imposed timeout fired before the solver
      replied.
    * [Solver_error { stderr }] — solver process emitted to stderr,
      exited nonzero, or crashed.
    * [Parse_error { stage; detail }] — solver output didn't match
      the expected protocol (sat/unsat/unknown).
    * [Unsupported_ir { kind; detail }] — the adapter could not
      serialize the input IR (e.g., quantifier in a QF adapter,
      unknown shell symbol). [kind] is the [Smtlib.error] kind name
      for adapters that go through SMT-LIB. *)

type failure =
  | Sat_returned
  | Unknown_returned
  | Timeout
  | Solver_error of { stderr : string }
  | Parse_error of { stage : string; detail : string }
  | Unsupported_ir of { kind : string; detail : string }

let kind_of_failure = function
  | Sat_returned -> "sat_returned"
  | Unknown_returned -> "unknown_returned"
  | Timeout -> "timeout"
  | Solver_error _ -> "solver_error"
  | Parse_error _ -> "parse_error"
  | Unsupported_ir _ -> "unsupported_ir"

let detail_of_failure = function
  | Sat_returned -> "solver returned sat: home-system goal is not provable"
  | Unknown_returned -> "solver returned unknown"
  | Timeout -> "broker timeout fired before solver replied"
  | Solver_error { stderr } -> stderr
  | Parse_error { stage; detail } -> Printf.sprintf "%s: %s" stage detail
  | Unsupported_ir { kind; detail } -> Printf.sprintf "%s: %s" kind detail

let failure_to_json (f : failure) : Yojson.Safe.t =
  let kind = kind_of_failure f in
  let detail = detail_of_failure f in
  if detail = "" then `Assoc [ "kind", `String kind ]
  else `Assoc [ "kind", `String kind; "detail", `String detail ]

(** Outcome of a dispatch call. *)
type result =
  | Cert of Certificate.t
  | Failed of failure

(** Adapter as a record of name/version metadata + a dispatch
    closure. The [dispatch] closure does the work; the broker only
    cares about the result. *)
type t = {
  name : string;
  version : string;
  dispatch : Ir.t -> result;
}

(** Hard upper bound on a single solver subprocess's wall time.
    The broker can be configured with smaller per-call defaults,
    but this cap is enforced regardless: an in-process caller
    requesting [wall_time_ms = 1_000_000_000] still gets capped to
    five minutes so a pathological input can't pin a thread. *)
let max_solver_wall_time_ms = 300_000  (* 5 minutes *)

(** Resolve a per-call solver timeout from an IR's user_directives,
    clamped into [[1, max_solver_wall_time_ms]]. The schema decoder
    already rejects negatives, but a [Some 0] still has to be
    handled — sending [0] to a solver's [--tlimit] flag is a
    pathological non-budget that some configurations interpret as
    "no limit", which is not what the IR's author meant. *)
let resolve_timeout_ms ~(default_ms : int) (ir : Ir.t) : int =
  let raw = match ir.user_directives with
    | Some { budget = Some { wall_time_ms = Some ms; _ }; _ } -> ms
    | _ -> default_ms
  in
  let lo = 1 in
  let hi = max_solver_wall_time_ms in
  if raw < lo then lo
  else if raw > hi then hi
  else raw

(** Drain a child process's stdout and stderr concurrently into
    strings. The naive "read stdout, then read stderr" pattern
    deadlocks when the child fills its stderr pipe buffer (~64KB
    on Linux) before closing stdout: the child blocks writing to
    stderr, and the parent blocks waiting for stdout EOF that the
    child can never reach. We multiplex via [Unix.select] on the
    underlying fds so neither pipe is left undrained.

    Both channels are read until EOF and then closed by the
    caller. The returned tuple is [(stdout_text, stderr_text)]. *)
let drain_subprocess_streams
    (stdout_ch : in_channel) (stderr_ch : in_channel)
  : string * string =
  let buf_out = Buffer.create 4096 in
  let buf_err = Buffer.create 1024 in
  let fd_out = Unix.descr_of_in_channel stdout_ch in
  let fd_err = Unix.descr_of_in_channel stderr_ch in
  let chunk = Bytes.create 4096 in
  let active = ref [ fd_out; fd_err ] in
  while !active <> [] do
    match Unix.select !active [] [] (-1.0) with
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> ()
    | ready, _, _ ->
      List.iter (fun fd ->
        let n =
          try Unix.read fd chunk 0 (Bytes.length chunk)
          with Unix.Unix_error (Unix.EINTR, _, _) -> -1
        in
        if n < 0 then ()
        else if n = 0 then
          active := List.filter (fun f -> f <> fd) !active
        else
          let buf = if fd = fd_out then buf_out else buf_err in
          Buffer.add_subbytes buf chunk 0 n) ready
  done;
  (Buffer.contents buf_out, Buffer.contents buf_err)

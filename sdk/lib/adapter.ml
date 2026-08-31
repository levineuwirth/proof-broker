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

(** Hard ceiling on bytes retained from a child's stdout/stderr.
    A hostile or buggy solver build can emit unbounded output (a
    pathological proof, an infinite print loop); without a cap
    [drain_subprocess_streams] would grow a [Buffer] until the
    process OOMs — and through the FFI that takes the host (Lean)
    process down with it. 256 MiB is far above any legitimate
    Alethe/SMT-LIB proof in v1 scope; past it we keep reading (to
    avoid a pipe-buffer deadlock) but stop storing, so the result
    is truncated. Truncated output fails downstream parsing, which
    is the intended fail-closed outcome (Tier-0 / sat fallback)
    rather than memory exhaustion. *)
let max_solver_output_bytes = 256 * 1024 * 1024

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

(* --- lazy backend-version probe (R1.8) ------------------------------ *)

(** Extract a dotted version number from a solver's [--version]
    first line (e.g. ["This is cvc5 version 1.3.0 [git ...]"] →
    ["1.3.0"]). First whitespace-separated token that starts with
    a digit and contains a dot; [None] when nothing matches. *)
let parse_version_token (line : string) : string option =
  let toks = String.split_on_char ' ' line in
  List.find_opt
    (fun t ->
      String.length t > 0
      && t.[0] >= '0' && t.[0] <= '9'
      && String.contains t '.')
    toks

(** [major.minor] prefix of a dotted version ("1.3.0" → "1.3";
    "1.3" → "1.3"). *)
let major_minor (v : string) : string =
  match String.split_on_char '.' v with
  | maj :: min :: _ -> maj ^ "." ^ min
  | _ -> v

(** Lazy one-time [--version] probe of a backend binary, memoized
    per binary name for the process lifetime. Returns [None] when
    the binary can't be spawned, exits non-zero-ish weirdly, or
    prints nothing parseable — callers fall back to their declared
    constant (a probe failure must never fail dispatch; the solver
    call itself will surface a missing binary). *)
let probe_table : (string, string option) Hashtbl.t = Hashtbl.create 4

let probe_version ~(binary : string) : string option =
  match Hashtbl.find_opt probe_table binary with
  | Some cached -> cached
  | None ->
    let result =
      try
        let argv = [| binary; "--version" |] in
        let stdout_ch, stdin_ch, stderr_ch =
          Unix.open_process_args_full argv.(0) argv (Unix.environment ())
        in
        close_out stdin_ch;
        let line = try input_line stdout_ch with End_of_file -> "" in
        (* Drain remaining output so the child never blocks. *)
        (try while true do ignore (input_line stdout_ch) done
         with End_of_file -> ());
        (try while true do ignore (input_line stderr_ch) done
         with End_of_file -> ());
        ignore (Unix.close_process_full (stdout_ch, stdin_ch, stderr_ch));
        parse_version_token line
      with _ -> None
    in
    Hashtbl.replace probe_table binary result;
    result

(** The version an adapter should stamp into certs: the probed
    binary version when the probe succeeds, else the declared
    [fallback] constant. *)
let probed_version ~(binary : string) ~(fallback : string) : string =
  match probe_version ~binary with
  | Some v -> v
  | None -> fallback

(** True iff the probed binary's major.minor differs from the
    adapter's declared version — the signal that version-sensitive
    output formats (cvc5's Alethe emission, Vampire's TSTP
    provenance shapes) may have drifted from what the adapter's
    parsers were validated against. A failed probe is NOT a
    mismatch (fallback to declared behavior). *)
let version_mismatch ~(binary : string) ~(declared : string) : bool =
  match probe_version ~binary with
  | Some v -> not (String.equal (major_minor v) (major_minor declared))
  | None -> false

(** Named diagnostic for a version mismatch, emitted once per
    dispatch on stderr (never a failure by itself — the adapter
    skips only its version-sensitive tier attempt). *)
let warn_version_mismatch ~(adapter : string) ~(binary : string)
    ~(declared : string) ~(skipping : string) : unit =
  match probe_version ~binary with
  | Some v ->
    Printf.eprintf
      "proof_broker: %s binary on PATH reports %s but the adapter \
       declares %s (major.minor mismatch) — skipping %s\n%!"
      adapter v declared skipping
  | None -> ()

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
          (* Bounded append: fill up to the cap, then keep draining
             (discarding) so the child never blocks on a full pipe —
             deadlock-safety must survive the cap. See
             [max_solver_output_bytes]. *)
          let room = max_solver_output_bytes - Buffer.length buf in
          if room > 0 then
            Buffer.add_subbytes buf chunk 0 (min n room)) ready
  done;
  (Buffer.contents buf_out, Buffer.contents buf_err)

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

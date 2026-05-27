(** Rocq-side Alethe walker. R-1: foundation only — the parse
    wrapper that surfaces the SDK's already-shared
    [Proof_broker.Alethe.parse] in a [Result] form for the Rocq
    plugin. Walker elaborators arrive starting R-2.

    See [.mli] for the multi-PR plan and audit-H1 contract. *)

module Alethe = Proof_broker.Alethe

type proof = Alethe.proof

let parse_trace (s : string) : (proof, string) result =
  try Ok (Alethe.parse s)
  with
  | Alethe.Parse_error msg ->
    Error ("alethe parse: " ^ msg)
  | exn ->
    (* Defensive: any other exception (e.g. an unexpected stack
       overflow not caught by [parse]'s own backstop) becomes an
       Error so the caller falls through to [lia] cleanly,
       rather than propagating and crashing the tactic. *)
    Error ("alethe parse: unexpected exception: " ^ Printexc.to_string exn)

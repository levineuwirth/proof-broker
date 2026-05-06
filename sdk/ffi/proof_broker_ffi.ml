(** OCaml entry point for the C shim — generic dispatcher.

    Registers a single callback ["pb_dispatch_call"] that the C shim looks
    up via [caml_named_value]. Method-specific handlers live in a private
    registry populated at module-load; new ops land by adding a
    [register_method] call at the bottom of this file. The C ABI
    (one [pb_ffi_call] entry point) does not grow with the OCaml API.

    Wire format and envelope shape are locked in [sdk/FFI_CONVENTIONS.md]:
    every dispatch returns a JSON object of one of two shapes,
      {"status": "ok",    "payload": ...}
      {"status": "error", "error":   {"kind": ..., "message": ..., ...}}
    even when the underlying OCaml type is single-valued. Per-method
    handlers own their own success and error envelopes; the dispatcher
    only synthesizes the [unknown_method] envelope. *)

open Yojson.Safe

let envelope_ok payload =
  to_string (`Assoc [ "status", `String "ok"; "payload", payload ])

let envelope_error ~kind ~message extra =
  to_string
    (`Assoc
      [
        "status", `String "error";
        "error", `Assoc ([ "kind", `String kind; "message", `String message ] @ extra);
      ])

(* Read-only after module init: the registry is populated once at the
   bottom of this file and then only read by the dispatcher. No
   concurrency hazards; re-loading on every dispatch would be silly. *)
let registry : (string, string -> string) Hashtbl.t = Hashtbl.create 16

let register_method (name : string) (handler : string -> string) : unit =
  Hashtbl.replace registry name handler

(* ---- handlers ---------------------------------------------------- *)

let roundtrip_ir (input : string) : string =
  try
    let j = from_string input in
    let ir = Proof_broker.Codec.of_json j in
    envelope_ok (Proof_broker.Codec.to_json ir)
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* Multi-return envelope: [propositional_simplify : Ir.t -> Ir.t *
   trace_entry] carries both results in [payload] under named keys
   per [sdk/FFI_CONVENTIONS.md] §Multi-return envelope. *)
let propositional_simplify (input : string) : string =
  try
    let j = from_string input in
    let ir = Proof_broker.Codec.of_json j in
    let result = Proof_broker.Propositional_simplify.run ir in
    let payload = `Assoc [
      "ir", Proof_broker.Codec.to_json result.ir;
      "trace_entry", Proof_broker.Trace.entry_to_json result.trace;
    ] in
    envelope_ok payload
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* Same multi-return envelope shape as [propositional_simplify].
   Configuration is read from
   [user_directives.rewriter_preferences.enable_quotient_elimination]
   (a bool); when missing or false the pass runs but reports
   [Skipped_preconditions]. *)
let quotient_elimination (input : string) : string =
  try
    let j = from_string input in
    let ir = Proof_broker.Codec.of_json j in
    let result = Proof_broker.Quotient_elimination.run ir in
    let payload = `Assoc [
      "ir", Proof_broker.Codec.to_json result.ir;
      "trace_entry", Proof_broker.Trace.entry_to_json result.trace;
    ] in
    envelope_ok payload
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* Same multi-return envelope shape as [propositional_simplify].
   Configuration is read from the IR's [user_directives.
   rewriter_preferences.enable_definition_unfolding] field rather
   than passed as a separate dispatcher arg. *)
let definition_unfolding (input : string) : string =
  try
    let j = from_string input in
    let ir = Proof_broker.Codec.of_json j in
    let result = Proof_broker.Definition_unfolding.run ir in
    let payload = `Assoc [
      "ir", Proof_broker.Codec.to_json result.ir;
      "trace_entry", Proof_broker.Trace.entry_to_json result.trace;
    ] in
    envelope_ok payload
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* [verify_certificate] takes
     {"cert": <Certificate>, "ir": <Ir>, "trace": <Trace.t>?}
   and returns
     {"ok": <bool>, "reason": {"kind": "...", "detail": "..."}}.

   [ok] is true iff [Verifier.verify] returns a verified reason
   ([Verified_envelope], [Verified_farkas], or [Verified_case_split]);
   the structured [reason] always tells the caller what was checked
   (or what failed). When envelope verification passes but no
   tier-specific verifier exists for the cert's tier/witness_kind,
   [ok] is true and [reason] is [tier_check_deferred] /
   [unsupported_witness_kind] so callers can decide whether to trust
   the cert at envelope level alone. *)
let verify_certificate (input : string) : string =
  try
    let j = from_string input in
    let pairs = match j with
      | `Assoc p -> p
      | _ -> raise (Proof_broker.Codec.Decode_error
                      ("expected object", j))
    in
    let cert_json = match List.assoc_opt "cert" pairs with
      | Some v -> v
      | None ->
        raise (Proof_broker.Codec.Decode_error
                 ("missing field: cert", j))
    in
    let ir_json = match List.assoc_opt "ir" pairs with
      | Some v -> v
      | None ->
        raise (Proof_broker.Codec.Decode_error
                 ("missing field: ir", j))
    in
    let cert = Proof_broker.Certificate.of_json cert_json in
    let ir = Proof_broker.Codec.of_json ir_json in
    let trace = match List.assoc_opt "trace" pairs with
      | None -> None
      | Some t -> Some (Proof_broker.Trace.of_json t)
    in
    let reason =
      Proof_broker.Verifier.verify ~trace cert ir
    in
    (* [ok] is the soundness flag: only true when the verifier
       has actually checked the proof's arithmetic / structural
       claim end-to-end. [envelope_ok] is the looser claim that
       envelope checks (hashes, tier/payload match, dispatch
       context) all passed but no tier-specific soundness
       check applied — this is the right gate for callers that
       trust their oracle and just want to confirm the cert is
       addressed to the right IR. Splitting the two keeps a
       caller from accidentally treating a Tier 0 oracle cert
       (Tier_check_deferred) or a Tier 1 cert with a witness
       shape we don't understand (Unsupported_witness_kind) as
       proof of soundness. *)
    let soundness_ok = match reason with
      | Verified_farkas | Verified_case_split | Verified_tier3 -> true
      | _ -> false
    in
    let env_ok = match reason with
      | Verified_envelope | Verified_farkas | Verified_case_split
      | Verified_tier3
      | Tier_check_deferred _ | Unsupported_witness_kind _
      | Tier3_unsupported_format _ -> true
      | _ -> false
    in
    let payload = `Assoc [
      "ok", `Bool soundness_ok;
      "envelope_ok", `Bool env_ok;
      "reason", Proof_broker.Verifier.reason_to_json reason;
    ] in
    envelope_ok payload
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* [match_adapters] takes a wrapped input of shape
     {"ir": <IR>, "manifests": [<Manifest>, ...]}
   and returns
     {"matches":    [{"adapter": ...}, ...],
      "rejections": [{"adapter": ..., "reason": {"kind":..., "detail":...}}, ...]}
   under [payload]. Order is preserved within each list relative
   to the input. The full manifest is not echoed back; callers
   already have it. *)
let match_adapters (input : string) : string =
  try
    let j = from_string input in
    let pairs = match j with
      | `Assoc p -> p
      | _ -> raise (Proof_broker.Codec.Decode_error
                      ("expected object", j))
    in
    let ir_json = match List.assoc_opt "ir" pairs with
      | Some v -> v
      | None ->
        raise (Proof_broker.Codec.Decode_error
                 ("missing field: ir", j))
    in
    let manifests_json = match List.assoc_opt "manifests" pairs with
      | Some (`List xs) -> xs
      | Some other ->
        raise (Proof_broker.Codec.Decode_error
                 ("expected array at manifests", other))
      | None ->
        raise (Proof_broker.Codec.Decode_error
                 ("missing field: manifests", j))
    in
    let ir = Proof_broker.Codec.of_json ir_json in
    let manifests = List.map Proof_broker.Manifest.of_json manifests_json in
    let matches, rejections =
      Proof_broker.Capability_match.select manifests ir
    in
    let payload = `Assoc [
      "matches",
      `List (List.map
               (fun (m : Proof_broker.Manifest.t) ->
                 `Assoc [ "adapter", `String m.adapter ])
               matches);
      "rejections",
      `List (List.map
               (fun ((m : Proof_broker.Manifest.t), reason) ->
                 `Assoc [
                   "adapter", `String m.adapter;
                   "reason",
                   Proof_broker.Capability_match.reason_to_json reason;
                 ])
               rejections);
    ] in
    envelope_ok payload
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* [run_pipeline] takes a wrapped input of shape
     {"ir": <IR>, "config": <PipelineConfig>?}
   so the IR and the pipeline config travel together through the
   single string slot the dispatcher exposes. Missing [config] falls
   back to [Pipeline.default_config] (spec §5.4). The payload mirrors
   the multi-return shape of the per-pass methods, with the
   single-entry [trace_entry] replaced by the pipeline-level
   [Trace.t] document under key [trace]. *)
let run_pipeline (input : string) : string =
  try
    let j = from_string input in
    let pairs = match j with
      | `Assoc p -> p
      | _ -> raise (Proof_broker.Codec.Decode_error ("expected object", j))
    in
    let ir_json = match List.assoc_opt "ir" pairs with
      | Some v -> v
      | None ->
        raise (Proof_broker.Codec.Decode_error ("missing field: ir", j))
    in
    let ir = Proof_broker.Codec.of_json ir_json in
    let config = match List.assoc_opt "config" pairs with
      | None -> Proof_broker.Pipeline.default_config
      | Some c -> Proof_broker.Pipeline.config_of_json c
    in
    let final_ir, trace = Proof_broker.Pipeline.run config ir in
    let payload = `Assoc [
      "ir", Proof_broker.Codec.to_json final_ir;
      "trace", Proof_broker.Trace.to_json trace;
    ] in
    envelope_ok payload
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* [dispatch_to_adapter] takes a wrapped input of shape
     {"adapter": "cvc4", "ir": <IR>}
   and returns
     {"ok": true,  "cert": <Certificate>}              on success, or
     {"ok": false, "failure": {"kind": ..., "detail": ...}}  on adapter failure.

   The ok=false case is used when the adapter itself ran but didn't
   produce a cert (sat returned, unknown returned, solver crashed,
   IR couldn't be serialized to SMT-LIB). Genuine plumbing errors
   (input couldn't be parsed) still go through the error envelope.

   Adapter registry. Phase 2.1 ships cvc4 and cvc5 (both as Tier 0
   oracle adapters); the registry is built-in (no manifest-driven
   loading yet). Adding adapters is a one-line change. *)
let adapter_registry : (string, Proof_broker.Adapter.t) Hashtbl.t =
  let r = Hashtbl.create 4 in
  Hashtbl.replace r "cvc4" Proof_broker.Adapter_cvc4.adapter;
  Hashtbl.replace r "cvc5" Proof_broker.Adapter_cvc5.adapter;
  r

let dispatch_to_adapter (input : string) : string =
  try
    let j = from_string input in
    let pairs = match j with
      | `Assoc p -> p
      | _ -> raise (Proof_broker.Codec.Decode_error
                      ("expected object", j))
    in
    let adapter_name = match List.assoc_opt "adapter" pairs with
      | Some (`String s) -> s
      | _ ->
        raise (Proof_broker.Codec.Decode_error
                 ("missing or non-string field: adapter", j))
    in
    let ir_json = match List.assoc_opt "ir" pairs with
      | Some v -> v
      | None ->
        raise (Proof_broker.Codec.Decode_error
                 ("missing field: ir", j))
    in
    let ir = Proof_broker.Codec.of_json ir_json in
    match Hashtbl.find_opt adapter_registry adapter_name with
    | None ->
      let payload = `Assoc [
        "ok", `Bool false;
        "failure", `Assoc [
          "kind", `String "adapter_not_found";
          "detail", `String adapter_name;
        ];
      ] in
      envelope_ok payload
    | Some adapter ->
      (match adapter.dispatch ir with
       | Cert cert ->
         envelope_ok (`Assoc [
           "ok", `Bool true;
           "cert", Proof_broker.Certificate.to_json cert;
         ])
       | Failed failure ->
         envelope_ok (`Assoc [
           "ok", `Bool false;
           "failure", Proof_broker.Adapter.failure_to_json failure;
         ]))
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* [dispatch_broker] takes a wrapped input of shape
     {"ir": <IR>, "manifests": [<Manifest>, ...],
      "prefer_higher_tier": <bool>?}
   and returns
     {"cert": <Certificate>?, "attempts": [<attempt>, ...]}
   under [payload]. The [cert] field is omitted when no adapter
   succeeded. [attempts] lists the per-manifest outcomes in the
   order they were exercised (after any reordering), with kind
   ∈ {skipped, no_implementation, failed, succeeded}; the rich
   detail is under [reason] (skipped) or [failure] (failed). The
   cert is at the top level (not duplicated inside [attempts]).

   Ordering. When [prefer_higher_tier] is [true] (the default),
   the broker stable-sorts manifests by max declared tier
   capability descending before iterating, so a Tier 1/2-capable
   adapter wins over a Tier 0 fallback regardless of input order.
   Stability preserves caller-supplied order within a tier. Set
   [prefer_higher_tier=false] to opt out and respect input order
   verbatim — useful for latency-first policies where a fast
   Tier 0 cert is preferred to waiting on a higher-tier adapter. *)
let dispatch_broker (input : string) : string =
  try
    let j = from_string input in
    let pairs = match j with
      | `Assoc p -> p
      | _ -> raise (Proof_broker.Codec.Decode_error
                      ("expected object", j))
    in
    let ir_json = match List.assoc_opt "ir" pairs with
      | Some v -> v
      | None ->
        raise (Proof_broker.Codec.Decode_error
                 ("missing field: ir", j))
    in
    let manifests_json = match List.assoc_opt "manifests" pairs with
      | Some (`List xs) -> xs
      | Some other ->
        raise (Proof_broker.Codec.Decode_error
                 ("expected array at manifests", other))
      | None ->
        raise (Proof_broker.Codec.Decode_error
                 ("missing field: manifests", j))
    in
    let prefer_higher_tier =
      match List.assoc_opt "prefer_higher_tier" pairs with
      | Some (`Bool b) -> b
      | None -> true
      | Some other ->
        raise (Proof_broker.Codec.Decode_error
                 ("expected bool at prefer_higher_tier", other))
    in
    let ir = Proof_broker.Codec.of_json ir_json in
    let manifests =
      List.map Proof_broker.Manifest.of_json manifests_json
    in
    let manifests =
      if prefer_higher_tier
      then Proof_broker.Manifest.sort_by_max_tier_descending manifests
      else manifests
    in
    let result =
      Proof_broker.Dispatch.run
        ~manifests ~adapters:adapter_registry ir
    in
    let cert_field = match result.cert with
      | None -> []
      | Some c -> [ "cert", Proof_broker.Certificate.to_json c ]
    in
    let payload = `Assoc (cert_field @ [
      "attempts",
      `List (List.map Proof_broker.Dispatch.attempt_to_json
               result.attempts);
    ]) in
    envelope_ok payload
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* [check_alethe_step] is the rule-specific check entry point used
   by the Lean Tier 3 walker (direction 2 of the Tier 3 plan). The
   Lean side parses the Alethe proof and ships one step at a time;
   OCaml dispatches by [step.rule] to a checker that re-derives
   the step's soundness. Currently registered: [la_generic] (via
   [Alethe_farkas] + [Farkas.verify]). Unsupported rules return
   [step_unsupported_rule] so the walker can surface the bailout
   reason cleanly.

   Input shape:
     {"ir": <IR>, "step": {id, rule, clause, args?, premises?, discharge?}}
   where each entry of [clause]/[args] is a [Sexp] JSON value
   (string = atom, array = list).

   Output payload (under [envelope_ok]):
     {ok: <bool>, kind: <step_verified | step_unsupported_rule
                          | step_failed>,
      [rule]: ..., [detail]: ...}. *)
let check_alethe_step (input : string) : string =
  try
    let j = from_string input in
    let pairs = match j with
      | `Assoc p -> p
      | _ -> raise (Proof_broker.Codec.Decode_error
                      ("expected object", j))
    in
    let ir_json = match List.assoc_opt "ir" pairs with
      | Some v -> v
      | None ->
        raise (Proof_broker.Codec.Decode_error
                 ("missing field: ir", j))
    in
    let step_json = match List.assoc_opt "step" pairs with
      | Some v -> v
      | None ->
        raise (Proof_broker.Codec.Decode_error
                 ("missing field: step", j))
    in
    let ir = Proof_broker.Codec.of_json ir_json in
    let step = Proof_broker.Alethe.step_of_json step_json in
    (* The FFI per-step interface ships no premise context yet —
       it's a direction-2 hook for a future Lean walker. With an
       empty [env.proven], stateless rules ([la_generic], [refl],
       [false]) work; stateful rules ([trans], [cong], [resolution])
       will surface "unknown premise" until the FFI grows an env
       parameter. *)
    let env : Proof_broker.Tier3_alethe.env = {
      ir;
      proven = Hashtbl.create 0;
      assumes = Hashtbl.create 0;
      deps = Hashtbl.create 0;
      last_step_clause = None;
      last_step_id = None;
      last_la_generic_consumed = None;
    } in
    let result = Proof_broker.Tier3_alethe.check_step env step in
    envelope_ok (Proof_broker.Tier3_alethe.step_result_to_json result)
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* ---- dispatcher -------------------------------------------------- *)

let dispatch (method_name : string) (input : string) : string =
  match Hashtbl.find_opt registry method_name with
  | Some handler -> handler input
  | None ->
    envelope_error ~kind:"unknown_method" ~message:method_name []

let () =
  register_method "roundtrip_ir" roundtrip_ir;
  register_method "propositional_simplify" propositional_simplify;
  register_method "definition_unfolding" definition_unfolding;
  register_method "quotient_elimination" quotient_elimination;
  register_method "run_pipeline" run_pipeline;
  register_method "match_adapters" match_adapters;
  register_method "verify_certificate" verify_certificate;
  register_method "dispatch_to_adapter" dispatch_to_adapter;
  register_method "dispatch_broker" dispatch_broker;
  register_method "check_alethe_step" check_alethe_step;
  Callback.register "pb_dispatch_call" dispatch

(** Stage-by-stage trace of the certificate path for ONE IR document.

    DIAGNOSTIC ONLY (checkpoint 1). Nothing here is a repair and nothing here
    is on any production path: the tool calls the SDK's own functions, in the
    order [Adapter_z3.dispatch] / [Adapter_cvc5.dispatch] / [Adapter_cvc4.dispatch]
    call them, and reports what each one returned. The point is to say WHICH
    STAGE loses the certificate, with the raw solver proof preserved.

    Stages reported per IR:

      pipeline     Pipeline.run (the dispatch pipeline every adapter is
                   fronted by) — final IR, trace identity, passes applied.
      compile      Farkas_search.compile_inputs on the final IR — which
                   hypotheses are Farkas-amenable at all, in compiled form.
      feasible     EXISTENCE probe (a measurement, not a closer): is there
                   ANY nonnegative-integer Farkas witness over exactly those
                   compiled inputs?  Asked of z3 as an integer feasibility
                   problem over the multipliers, then the model is turned
                   into a witness JSON and handed to the SDK's OWN
                   [Farkas.verify].  A `verified` here means the certificate
                   exists over the IR the tactic dispatched, so any failure
                   downstream is a recovery failure, not an absent proof.
      backends     per backend: emit → solve → raw proof → NATIVE extraction
                   (Z3_farkas / Alethe_farkas) → FALLBACK search
                   (Farkas_search.try_close) → Farkas.verify on whatever was
                   produced → the tier the adapter would mint and BY WHICH
                   ROUTE.
      bound_sweep  the smallest [Farkas_search.try_close ~bound] that
                   succeeds, over an explicit ladder — what "just raise the
                   enumeration bound" would actually cost.

    usage: diag.exe <ir.json> <out_dir> [case_id]
    Writes <out_dir>/<case>.report.json and the raw artifacts
    (<case>.<backend>.smt2 / .stdout / .proof).
*)

open Proof_broker
module J = Yojson.Safe

let read_file p = let ic = open_in_bin p in
  let n = in_channel_length ic in let s = really_input_string ic n in
  close_in ic; s

let write_file p s =
  let oc = open_out_bin p in output_string oc s; close_out oc

let now () = Unix.gettimeofday ()
let ms t0 = int_of_float ((now () -. t0) *. 1000.)

(* --- printing helpers ------------------------------------------------- *)

let compiled_to_string = function
  | Farkas.Le f -> "Le(" ^ Linear_arith.to_string f ^ " <= 0)"
  | Farkas.Lt f -> "Lt(" ^ Linear_arith.to_string f ^ " < 0)"
  | Farkas.Eq f -> "Eq(" ^ Linear_arith.to_string f ^ " = 0)"

let verdict_to_json (v : Farkas.verdict) : J.t =
  match v with
  | Verified -> `Assoc [ "verdict", `String "verified" ]
  | Unknown_hypothesis { hypothesis } ->
    `Assoc [ "verdict", `String "unknown_hypothesis"; "hypothesis", `String hypothesis ]
  | Duplicate_hypothesis { hypothesis } ->
    `Assoc [ "verdict", `String "duplicate_hypothesis"; "hypothesis", `String hypothesis ]
  | Nonlinear { hypothesis; detail } ->
    `Assoc [ "verdict", `String "nonlinear"; "hypothesis", `String hypothesis;
             "detail", `String detail ]
  | Bad_coefficient { hypothesis; raw } ->
    `Assoc [ "verdict", `String "bad_coefficient"; "hypothesis", `String hypothesis;
             "raw", `String raw ]
  | Negative_coefficient { hypothesis; value } ->
    `Assoc [ "verdict", `String "negative_coefficient"; "hypothesis", `String hypothesis;
             "value", `String value ]
  | Not_contradictory { residual } ->
    `Assoc [ "verdict", `String "not_contradictory"; "residual", `String residual ]
  | Malformed_witness { detail } ->
    `Assoc [ "verdict", `String "malformed_witness"; "detail", `String detail ]

let cert_summary (c : Certificate.t) : J.t =
  let witness =
    match c.payload with
    | Certificate.Tier1_witness { witness_data; witness_kind; _ } ->
      `Assoc [ "witness_kind",
               `String (match witness_kind with
                        | Certificate.Farkas -> "farkas"
                        | _ -> "other");
               "witness_data", witness_data ]
    | Certificate.Tier0_oracle { claim; _ } ->
      `Assoc [ "claim", `String claim ]
    | _ -> `Assoc [ "payload", `String "other" ]
  in
  `Assoc [
    "tier", `Int c.tier;
    "format", `String c.format;
    "payload", witness;
  ]

let adapter_result_json (r : Adapter.result) : J.t =
  match r with
  | Adapter.Cert c -> `Assoc [ "outcome", `String "cert"; "cert", cert_summary c ]
  | Adapter.Failed f ->
    `Assoc [ "outcome", `String "failed"; "failure", Adapter.failure_to_json f ]

(* --- the existence probe --------------------------------------------- *)

(* Ask z3 (exactly, over the integers) whether ANY Farkas witness exists over
   the compiled inputs. Multipliers: nonneg integers on Le/Lt inputs, free
   integers on Eq inputs. Constraints: every variable's total coefficient is
   0; the constant part is strictly positive (LIA — every strict input has
   already been folded into Le by compile_hypothesis's +1 trick, so the
   loose-combination rule "constant > 0 contradicts" is the right one, which
   is also exactly what Farkas.verify checks). Minimize the multiplier sum so
   the reported witness is the small one a reader can check by hand. *)

let z3_bin = "z3"

let run_z3 ?(timeout_ms = 10000) (script : string) : string =
  let argv = [| z3_bin; "-in"; "-smt2"; Printf.sprintf "-T:%d" (max 1 (timeout_ms / 1000)) |] in
  let out_r, out_w = Unix.pipe () in
  let in_r, in_w = Unix.pipe () in
  let err_r, err_w = Unix.pipe () in
  let pid = Unix.create_process z3_bin argv in_r out_w err_w in
  Unix.close in_r; Unix.close out_w; Unix.close err_w;
  let oc = Unix.out_channel_of_descr in_w in
  output_string oc script; flush oc; close_out oc;
  let ic = Unix.in_channel_of_descr out_r in
  let buf = Buffer.create 4096 in
  (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
  close_in ic;
  let eic = Unix.in_channel_of_descr err_r in
  (try while true do ignore (input_char eic) done with End_of_file -> ());
  close_in eic;
  ignore (Unix.waitpid [] pid);
  Buffer.contents buf

let z_to_smt (z : Z.t) : string =
  if Z.sign z < 0 then "(- " ^ Z.to_string (Z.neg z) ^ ")" else Z.to_string z

(* Rational coefficient -> exact integer pair via the common denominator of
   the whole system, computed by the caller. *)
let feasibility_probe ?(dump_prefix = "") (ir : Ir.t) (inputs : Farkas_search.input list) : J.t =
  if inputs = [] then `Assoc [ "status", `String "no_compilable_inputs" ]
  else begin
    (* Clear denominators: scale every input's linear form by the lcm of all
       denominators appearing in it, so the LP is over integers. Scaling a
       Farkas input by a positive rational is sound (the multiplier absorbs
       it); we undo the scale when reporting the witness coefficient. *)
    let scale_of (c : Farkas.compiled) =
      let f = match c with Farkas.Le f | Farkas.Lt f | Farkas.Eq f -> f in
      let dens = (List.map (fun (_, (r : Linear_arith.rational)) -> r.den) f.coeffs)
                 @ [ f.const.den ] in
      List.fold_left (fun acc d -> Z.lcm acc d) Z.one dens
    in
    let terms = List.map (fun (i : Farkas_search.input) ->
      let s = scale_of i.compiled in
      let f = match i.compiled with Farkas.Le f | Farkas.Lt f | Farkas.Eq f -> f in
      let intify (r : Linear_arith.rational) =
        Z.divexact (Z.mul r.num s) r.den in
      let is_eq = (match i.compiled with Farkas.Eq _ -> true | _ -> false) in
      (i.name, s, is_eq,
       List.map (fun (v, r) -> (v, intify r)) f.coeffs,
       intify f.const)) inputs
    in
    let vars =
      List.sort_uniq String.compare
        (List.concat_map (fun (_, _, _, cs, _) -> List.map fst cs) terms) in
    let lam i = Printf.sprintf "L%d" i in
    let b = Buffer.create 1024 in
    Buffer.add_string b "(set-option :produce-models true)\n";
    List.iteri (fun i (_, _, is_eq, _, _) ->
      Buffer.add_string b (Printf.sprintf "(declare-const %s Int)\n" (lam i));
      if not is_eq then
        Buffer.add_string b (Printf.sprintf "(assert (>= %s 0))\n" (lam i)))
      terms;
    (* every variable cancels *)
    List.iter (fun v ->
      let parts = List.concat (List.mapi (fun i (_, _, _, cs, _) ->
        match List.assoc_opt v cs with
        | None -> []
        | Some z -> [ Printf.sprintf "(* %s %s)" (lam i) (z_to_smt z) ]) terms) in
      let sum = match parts with
        | [] -> "0" | [ x ] -> x
        | xs -> "(+ " ^ String.concat " " xs ^ ")" in
      Buffer.add_string b (Printf.sprintf "(assert (= %s 0))\n" sum)) vars;
    (* the constant part is strictly positive *)
    let cparts = List.mapi (fun i (_, _, _, _, k) ->
      Printf.sprintf "(* %s %s)" (lam i) (z_to_smt k)) terms in
    let csum = match cparts with
      | [] -> "0" | [ x ] -> x
      | xs -> "(+ " ^ String.concat " " xs ^ ")" in
    Buffer.add_string b (Printf.sprintf "(assert (> %s 0))\n" csum);
    (* Smallest total multiplier mass, so the reported witness is the small
       one a reader can check by hand. |L_i| via an auxiliary nonneg A_i:
       minimizing the raw sum would be unbounded below on the FREE (equality)
       multipliers, and z3 then returns an arbitrary feasible model. *)
    List.iteri (fun i _ ->
      Buffer.add_string b (Printf.sprintf "(declare-const A%d Int)\n" i);
      Buffer.add_string b (Printf.sprintf "(assert (>= A%d %s))\n" i (lam i));
      Buffer.add_string b
        (Printf.sprintf "(assert (>= A%d (- %s)))\n" i (lam i))) terms;
    let mass = String.concat " " (List.mapi (fun i _ -> Printf.sprintf "A%d" i) terms) in
    Buffer.add_string b
      (Printf.sprintf "(minimize (+ %s))\n" (if List.length terms = 1 then mass ^ " 0" else mass));
    Buffer.add_string b "(check-sat)\n(get-model)\n(exit)\n";
    let lp = Buffer.contents b in
    if dump_prefix <> "" then write_file (dump_prefix ^ ".farkas_lp.smt2") lp;
    let out = run_z3 lp in
    if dump_prefix <> "" then write_file (dump_prefix ^ ".farkas_lp.stdout") out;
    let first_tok =
      let lines = String.split_on_char '\n' out in
      match List.find_opt (fun l -> String.trim l <> "") lines with
      | Some l -> String.trim l
      | None -> "" in
    if first_tok = "unsat" then
      `Assoc [ "status", `String "no_witness_exists";
               "detail", `String "no nonneg-integer Farkas combination of the \
                                  compiled inputs is contradictory" ]
    else if first_tok <> "sat" then
      `Assoc [ "status", `String "probe_inconclusive";
               "z3_first_line", `String first_tok ]
    else begin
      (* parse "(define-fun L3 () Int 262144)", value possibly "(- 5)" *)
      let re = Str.regexp
        "(define-fun[ \t\r\n]+L\\([0-9]+\\)[ \t\r\n]+()[ \t\r\n]+Int[ \t\r\n]+\\((-[ \t\r\n]+[0-9]+)\\|[0-9]+\\)" in
      let vals = Hashtbl.create 16 in
      let pos = ref 0 in
      (try while true do
        let _ = Str.search_forward re out !pos in
        let idx = int_of_string (Str.matched_group 1 out) in
        let raw = Str.matched_group 2 out in
        let v =
          if String.length raw > 0 && raw.[0] = '(' then
            Z.neg (Z.of_string (String.trim (String.sub raw 2 (String.length raw - 3))))
          else Z.of_string raw in
        Hashtbl.replace vals idx v;
        pos := Str.match_end ()
      done with Not_found -> ());
      let entries = List.concat (List.mapi (fun i (name, s, _, _, _) ->
        match Hashtbl.find_opt vals i with
        | None -> []
        | Some z when Z.equal z Z.zero -> []
        (* undo the denominator scaling: the witness coefficient that
           addresses the UNSCALED input is z * s. *)
        | Some z -> [ (name, Z.mul z s) ]) terms) in
      let witness = `Assoc [ "coefficients",
        `List (List.map (fun (n, z) -> `Assoc [
          "hypothesis", `String n;
          "coefficient", `String (Z.to_string z) ]) entries) ] in
      `Assoc [
        "status", `String "witness_exists";
        "support", `Int (List.length entries);
        "max_abs_coefficient",
        `String (Z.to_string (List.fold_left (fun a (_, z) -> Z.max a (Z.abs z))
                                Z.zero entries));
        "witness", witness;
        (* the loop closed against the SDK's OWN checker: if this says
           `verified`, a certificate for this IR exists and every failure
           downstream is a RECOVERY failure, not a missing proof. *)
        "farkas_verify", verdict_to_json (Farkas.verify ir witness);
      ]
    end
  end

(* --- the two internal-closer stages, timed apart ---------------------- *)

(* The adapters call [Farkas_search.try_close_then_exact]: the bounded
   coefficient enumeration first, and exact support-bounded recovery ONLY
   where that came up empty. The tracer runs the two separately so the report
   says which one produced the witness and what each cost — "the fallback
   found it" is not a useful sentence once there are two fallbacks. *)
let fallback_stages (ir : Ir.t) : J.t =
  let t = now () in
  let bounded = match Farkas_search.try_close ir with
    | Ok w ->
      `Assoc [ "result", `String "ok"; "ms", `Int (ms t);
               "witness", w;
               "farkas_verify", verdict_to_json (Farkas.verify ir w) ]
    | Error e ->
      `Assoc [ "result", `String "error"; "ms", `Int (ms t);
               "kind", `String (Farkas_search.kind_of_error e);
               "detail", `String (Farkas_search.detail_of_error e) ]
  in
  let t2 = now () in
  let exact = match Farkas_search.try_close_exact ir with
    | Ok w ->
      `Assoc [ "result", `String "ok"; "ms", `Int (ms t2);
               "witness", w;
               "farkas_verify", verdict_to_json (Farkas.verify ir w) ]
    | Error e ->
      `Assoc [ "result", `String "error"; "ms", `Int (ms t2);
               "kind", `String (Farkas_search.kind_of_error e);
               "detail", `String (Farkas_search.detail_of_error e) ]
  in
  let route =
    match Farkas_search.try_close ir, Farkas_search.try_close_exact ir with
    | Ok _, _ -> "bounded_enumeration"
    | Error _, Ok _ -> "exact_recovery"
    | Error _, Error _ -> "none"
  in
  `Assoc [ "route", `String route;
           "bounded_enumeration", bounded;
           "exact_recovery", exact ]

(* --- backend stages --------------------------------------------------- *)

let witness_coefficients (w : J.t) : J.t = w

type backend_run = {
  name : string;
  json : J.t;
}

let stage_z3 ~out_prefix (ir : Ir.t) : backend_run =
  let fragment = Farkas.effective_fragment ir in
  match Refinement.run ~fragment ir with
  | Error e ->
    { name = "z3";
      json = `Assoc [ "stage_failed", `String "refinement";
                      "kind", `String (Refinement.kind_of_error e);
                      "detail", `String (Refinement.detail_of_error e) ] }
  | Ok refinement ->
    (match Smtlib.emit refinement.refined_ir with
     | Error e ->
       { name = "z3";
         json = `Assoc [ "stage_failed", `String "smtlib_emit";
                         "kind", `String (Smtlib.kind_of_error e);
                         "detail", `String (Smtlib.detail_of_error e) ] }
     | Ok script ->
       let preamble =
         "(set-option :produce-proofs true)\n(set-option :smt.arith.solver 2)\n" in
       let body = preamble ^ script.body ^ "(check-sat)\n(get-proof)\n(exit)\n" in
       write_file (out_prefix ^ ".z3.smt2") body;
       let t0 = now () in
       let stdout, _stderr, _code = Adapter_z3.run_solver ~timeout_ms:5000 body in
       let solve_ms = ms t0 in
       write_file (out_prefix ^ ".z3.stdout") stdout;
       let resp = match Adapter_z3.parse_response stdout with
         | Adapter_z3.Unsat -> "unsat" | Adapter_z3.Sat -> "sat"
         | Adapter_z3.Unknown_resp -> "unknown" | Adapter_z3.Other_resp s -> "other:" ^ s in
       let proof = Adapter_z3.extract_proof_body stdout in
       (match proof with
        | Some p -> write_file (out_prefix ^ ".z3.proof") p
        | None -> ());
       let native =
         match proof with
         | None -> `Assoc [ "attempted", `Bool false;
                            "reason", `String "no proof body in solver stdout" ]
         | Some p ->
           let t1 = now () in
           (match Z3_farkas.extract ir p with
            | Ok w ->
              `Assoc [ "attempted", `Bool true; "result", `String "ok";
                       "ms", `Int (ms t1);
                       "witness", witness_coefficients w;
                       "farkas_verify", verdict_to_json (Farkas.verify ir w) ]
            | Error e ->
              `Assoc [ "attempted", `Bool true; "result", `String "error";
                       "ms", `Int (ms t1);
                       "kind", `String (Z3_farkas.error_kind e);
                       "detail", `String (Z3_farkas.error_detail e) ])
       in
       let fallback = fallback_stages ir in
       { name = "z3";
         json = `Assoc [
           "smtlib_logic", `String script.logic;
           "solver_response", `String resp;
           "solver_ms", `Int solve_ms;
           "proof_body_present", `Bool (proof <> None);
           "proof_bytes", `Int (match proof with Some p -> String.length p | None -> 0);
           "native_extraction", native;
           "fallback_search", fallback;
         ] })

let stage_cvc5 ~out_prefix (ir : Ir.t) : backend_run =
  let fragment = Farkas.effective_fragment ir in
  match Refinement.run ~fragment ir with
  | Error e ->
    { name = "cvc5";
      json = `Assoc [ "stage_failed", `String "refinement";
                      "detail", `String (Refinement.detail_of_error e) ] }
  | Ok refinement ->
    (match Smtlib.emit refinement.refined_ir with
     | Error e ->
       { name = "cvc5";
         json = `Assoc [ "stage_failed", `String "smtlib_emit";
                         "detail", `String (Smtlib.detail_of_error e) ] }
     | Ok script ->
       let body = script.body ^ "(check-sat)\n(get-proof)\n(exit)\n" in
       write_file (out_prefix ^ ".cvc5.smt2") body;
       let t0 = now () in
       let stdout, _stderr, _code = Adapter_cvc5.run_solver ~timeout_ms:5000 body in
       let solve_ms = ms t0 in
       write_file (out_prefix ^ ".cvc5.stdout") stdout;
       let resp = match Adapter_cvc5.parse_response stdout with
         | Adapter_cvc5.Unsat -> "unsat" | Adapter_cvc5.Sat -> "sat"
         | Adapter_cvc5.Unknown_resp -> "unknown"
         | Adapter_cvc5.Other_resp s -> "other:" ^ s in
       let proof = Adapter_cvc5.extract_proof_body stdout in
       (match proof with
        | Some p -> write_file (out_prefix ^ ".cvc5.proof") p
        | None -> ());
       let native =
         match proof with
         | None -> `Assoc [ "attempted", `Bool false;
                            "reason", `String "no proof body in solver stdout" ]
         | Some p ->
           let t1 = now () in
           (match Alethe_farkas.extract ir p with
            | Ok w ->
              `Assoc [ "attempted", `Bool true; "result", `String "ok";
                       "ms", `Int (ms t1); "witness", witness_coefficients w;
                       "farkas_verify", verdict_to_json (Farkas.verify ir w) ]
            | Error e ->
              `Assoc [ "attempted", `Bool true; "result", `String "error";
                       "ms", `Int (ms t1);
                       "kind", `String (Alethe_farkas.error_kind e);
                       "detail", `String (Alethe_farkas.error_detail e) ])
       in
       let case_split =
         match proof with
         | None -> `String "not attempted"
         | Some p ->
           (match Alethe_farkas.extract_case_split_payload ir p with
            | Ok _ -> `String "ok (tier 2 case split available)"
            | Error e -> `String ("error: " ^ Alethe_farkas.error_kind e))
       in
       let fallback = fallback_stages ir in
       { name = "cvc5";
         json = `Assoc [
           "smtlib_logic", `String script.logic;
           "solver_response", `String resp;
           "solver_ms", `Int solve_ms;
           "proof_body_present", `Bool (proof <> None);
           "proof_bytes", `Int (match proof with Some p -> String.length p | None -> 0);
           "native_extraction", native;
           "case_split_extraction", case_split;
           "fallback_search", fallback;
         ] })

let stage_cvc4 ~out_prefix (ir : Ir.t) : backend_run =
  let fragment = Farkas.effective_fragment ir in
  match Refinement.run ~fragment ir with
  | Error e ->
    { name = "cvc4";
      json = `Assoc [ "stage_failed", `String "refinement";
                      "detail", `String (Refinement.detail_of_error e) ] }
  | Ok refinement ->
    (match Smtlib.emit refinement.refined_ir with
     | Error e ->
       { name = "cvc4";
         json = `Assoc [ "stage_failed", `String "smtlib_emit";
                         "detail", `String (Smtlib.detail_of_error e) ] }
     | Ok script ->
       let body = script.body ^ "(check-sat)\n(exit)\n" in
       write_file (out_prefix ^ ".cvc4.smt2") body;
       let t0 = now () in
       let stdout, _stderr, _code = Adapter_cvc4.run_solver ~timeout_ms:5000 body in
       let solve_ms = ms t0 in
       write_file (out_prefix ^ ".cvc4.stdout") stdout;
       let resp = match Adapter_cvc4.parse_response stdout with
         | Adapter_cvc4.Unsat -> "unsat" | Adapter_cvc4.Sat -> "sat"
         | Adapter_cvc4.Unknown_resp -> "unknown"
         | Adapter_cvc4.Other_resp s -> "other:" ^ s in
       let fallback = fallback_stages ir in
       { name = "cvc4";
         json = `Assoc [
           "smtlib_logic", `String script.logic;
           "solver_response", `String resp;
           "solver_ms", `Int solve_ms;
           "proof_body_present", `Bool false;
           "native_extraction",
           `String "cvc4 has no proof-trace path (adapter goes straight to the \
                    internal closer)";
           "fallback_search", fallback;
         ] })

(* --- bound sweep ------------------------------------------------------ *)

let bound_sweep (ir : Ir.t) : J.t =
  let ladder = [ 3; 4; 6; 8; 12; 16; 24; 32 ] in
  let rec go = function
    | [] -> `Assoc [ "smallest_successful_bound", `Null;
                     "ladder_exhausted_at", `Int 32 ]
    | b :: rest ->
      let t0 = now () in
      (match Farkas_search.try_close ~bound:b ir with
       | Ok w ->
         `Assoc [ "smallest_successful_bound", `Int b; "ms", `Int (ms t0);
                  "witness", w ]
       | Error _ -> go rest)
  in
  go ladder

(* --- main ------------------------------------------------------------- *)

let () =
  let ir_path, out_dir, case =
    match Sys.argv with
    | [| _; a; b |] -> a, b, Filename.remove_extension (Filename.basename a)
    | [| _; a; b; c |] -> a, b, c
    | _ -> prerr_endline "usage: diag.exe <ir.json> <out_dir> [case_id]"; exit 2
  in
  let ir0 = Codec.of_json (J.from_string (read_file ir_path)) in
  let final_ir, trace = Pipeline.run Pipeline.default_dispatch_config ir0 in
  let out_prefix = Filename.concat out_dir case in
  write_file (out_prefix ^ ".final_ir.json")
    (J.pretty_to_string (Codec.to_json final_ir) ^ "\n");
  let rewrite_trace_hash = Hash.canonical_sha256 (Trace.to_json trace) in
  let inputs = Farkas_search.compile_inputs final_ir in
  let compiled_json = `List (List.map (fun (i : Farkas_search.input) ->
    `Assoc [ "name", `String i.name;
             "compiled", `String (compiled_to_string i.compiled) ]) inputs) in
  let dropped =
    let kept = List.map (fun (i : Farkas_search.input) -> i.name) inputs in
    `List (List.filter_map (fun (h : Ir.hypothesis) ->
      if List.mem h.name kept then None
      else
        let fragment = Farkas.effective_fragment final_ir in
        match Farkas.compile_hypothesis ~fragment h.shell with
        | Ok _ -> Some (`Assoc [ "name", `String h.name; "reason", `String "?" ])
        | Error d -> Some (`Assoc [ "name", `String h.name; "reason", `String d ]))
      final_ir.context.hypotheses)
  in
  let feas = feasibility_probe ~dump_prefix:out_prefix final_ir inputs in
  let backends = [ stage_z3 ~out_prefix final_ir;
                   stage_cvc5 ~out_prefix final_ir;
                   stage_cvc4 ~out_prefix final_ir ] in
  (* Cross-check: what the real adapters actually mint on this IR. *)
  let minted = `Assoc [
    "z3", adapter_result_json (Adapter_z3.dispatch ~rewrite_trace_hash final_ir);
    "cvc5", adapter_result_json (Adapter_cvc5.dispatch ~rewrite_trace_hash final_ir);
    "cvc4", adapter_result_json (Adapter_cvc4.dispatch ~rewrite_trace_hash final_ir);
  ] in
  let report = `Assoc [
    "case", `String case;
    "ir_source", `String ir_path;
    "ir_sha256", `String (Hash.sha256_of_json (Codec.to_json ir0));
    "final_ir_sha256", `String (Hash.sha256_of_json (Codec.to_json final_ir));
    "pipeline", `Assoc [
      "trace_is_identity", `Bool (Trace.is_identity trace);
      "entries", `List (List.map (fun (e : Trace.entry) ->
        `Assoc [ "pass", `String e.pass;
                 "outcome", `String (match e.outcome with
                   | Some Trace.Applied -> "applied"
                   | Some Trace.No_op -> "no_op"
                   | Some Trace.Skipped_preconditions -> "skipped_preconditions"
                   | Some Trace.Failed -> "failed"
                   | None -> "none") ]) trace.entries);
      "rewrite_trace_hash", `String rewrite_trace_hash;
    ];
    "fragment", `String (Farkas.effective_fragment final_ir);
    "hypotheses_in_final_ir", `Int (List.length final_ir.context.hypotheses);
    "farkas_compiled_inputs", compiled_json;
    "hypotheses_not_compilable", dropped;
    "witness_existence_probe", feas;
    "backends", `Assoc (List.map (fun b -> b.name, b.json) backends);
    "adapter_minted", minted;
    "fallback_bound_sweep", bound_sweep final_ir;
  ] in
  write_file (out_prefix ^ ".report.json") (J.pretty_to_string report ^ "\n");
  print_endline (J.pretty_to_string report)

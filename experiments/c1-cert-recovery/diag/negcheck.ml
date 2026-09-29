(** Negative checks: false goals and corrupted certificates — AS A GATE.

    DIAGNOSTIC ONLY. Uses the SHIPPED verification interfaces
    ([Farkas.verify], [Verifier.verify]) and CHECKS THEIR VERDICTS against an
    expectation computed here. A checkpoint that only reports what the broker
    accepts says nothing about whether acceptance means anything; a diagnostic
    that only records verdicts without asserting them is not a gate either.
    This exits NONZERO when any check fails, so a runner cannot report a green
    result by accident (C1 review, finding 3).

    ## What is checked

    * FALSE GOALS (with [--expect-sat]) — no adapter may mint a certificate;
      every one must return a typed failure. The corpus's falsity is
      established arithmetically in tools/truth_check.py, never by a prover's
      failure.

    * CORRUPTED CERTIFICATES — a certificate an adapter really minted on this
      IR is mutated one field at a time, and each mutant's verdict must equal
      the expectation.

    ## Why the expectation is computed, not assumed (C1 review, finding 2)

    Not every mutation is a corruption. Scaling a valid witness by a positive
    integer is a different valid proof of the same fact, and [Farkas.verify]
    accepting it is CORRECT. The first version of this file assumed all
    mutations must be rejected, then explained away the accepted ones with the
    wrong mechanism: its target picker called an input "load-bearing" only if
    its compiled form contained a VARIABLE, which classifies the ground
    contradiction of a variable-free goal (`O1`: `2^18 < P`) as vacuous. The
    target then fell back to `hP`, whose compiled form after definition
    unfolding is the identically-zero `0 = 0` — so the five "accepted
    mutations" had mutated a term that carries no proof content at all, and
    the real contradiction was never touched.

    So: [expected_verified] is a second, small implementation of the Farkas
    acceptance rule (spec v1.0 §6 / [Farkas.verify]'s documented contract),
    applied to each mutant, and the gate asserts the shipped verifier agrees
    with it. A disagreement is a finding in whichever direction it goes. The
    target is chosen to make the battery sharp — an entry whose compiled form
    has a VARIABLE where one exists, else a non-vacuous entry — and the class
    actually used is reported, never asserted.

    usage: negcheck.exe [--expect-sat] <ir.json> <out_dir> <case_id>
*)

open Proof_broker
module J = Yojson.Safe
module L = Linear_arith

let read_file p = let ic = open_in_bin p in
  let n = in_channel_length ic in let s = really_input_string ic n in
  close_in ic; s

let write_file p s = let oc = open_out_bin p in output_string oc s; close_out oc

let z_opt (s : string) : Z.t option =
  match Z.of_string s with v -> Some v | exception _ -> None

let farkas_verdict_name (v : Farkas.verdict) = match v with
  | Verified -> "VERIFIED"
  | Unknown_hypothesis _ -> "unknown_hypothesis"
  | Duplicate_hypothesis _ -> "duplicate_hypothesis"
  | Nonlinear _ -> "nonlinear"
  | Bad_coefficient _ -> "bad_coefficient"
  | Negative_coefficient _ -> "negative_coefficient"
  | Not_contradictory _ -> "not_contradictory"
  | Malformed_witness _ -> "malformed_witness"

(* [Verifier.reason_to_json] emits {"kind": "...", "detail": "..."}; the gate
   compares the KIND, so read that field rather than the whole object. *)
let reason_name (r : Verifier.reason) =
  match Verifier.reason_to_json r with
  | `Assoc kvs ->
    (match List.assoc_opt "kind" kvs with
     | Some (`String s) -> s
     | _ -> J.to_string (Verifier.reason_to_json r))
  | j -> J.to_string j

(* --- witness plumbing -------------------------------------------------- *)

let coefficients (w : J.t) : (string * string) list =
  match w with
  | `Assoc kvs ->
    (match List.assoc_opt "coefficients" kvs with
     | Some (`List xs) ->
       List.filter_map (function
         | `Assoc f ->
           (match List.assoc_opt "hypothesis" f, List.assoc_opt "coefficient" f with
            | Some (`String h), Some (`String c) -> Some (h, c)
            | _ -> None)
         | _ -> None) xs
     | _ -> [])
  | _ -> []

let of_coefficients (cs : (string * string) list) : J.t =
  `Assoc [ "coefficients", `List (List.map (fun (h, c) ->
    `Assoc [ "hypothesis", `String h; "coefficient", `String c ]) cs) ]

(* --- the expectation oracle -------------------------------------------- *)

(** The Farkas acceptance rule, re-implemented here so the gate has something
    to compare [Farkas.verify] against: nonneg coefficients on inequalities,
    the weighted sum must be a constant, and that constant must be positive —
    or, under LRA only, zero with a positively-weighted strict input. Returns
    [true] iff a correct verifier must accept this witness against [ir]. *)
let expected_verified (ir : Ir.t) (entries : (string * string) list) : bool =
  if entries = [] then false
  else
    let fragment = Farkas.effective_fragment ir in
    let lra = String.equal fragment "LRA" in
    let rec go acc has_strict = function
      | [] ->
        if acc.L.coeffs <> [] then false
        else
          let k = acc.L.const in
          if lra then L.rat_is_pos k || (L.rat_is_zero k && has_strict)
          else L.rat_is_pos k
      | (name, coef_s) :: rest ->
        (match L.rat_of_string coef_s with
         | None -> false
         | Some coef ->
           (match Farkas.lookup_hypothesis ir name with
            | None -> false
            | Some shell ->
              (match Farkas.compile_hypothesis ~fragment shell with
               | Error _ -> false
               | Ok compiled ->
                 let f, strict_here, sign_ok = match compiled with
                   | Farkas.Le f -> f, false, L.rat_is_nonneg coef
                   | Farkas.Lt f -> f, L.rat_is_pos coef, L.rat_is_nonneg coef
                   | Farkas.Eq f -> f, false, true
                 in
                 if not sign_ok then false
                 else
                   go (L.add acc (L.scale coef f))
                     (has_strict || strict_here) rest)))
    in
    go L.zero false entries

(* --- target selection -------------------------------------------------- *)

type target_class = Has_variables | Constant_nonzero | Vacuous | Unresolvable

let class_name = function
  | Has_variables -> "has_variables"
  | Constant_nonzero -> "constant_nonzero"
  | Vacuous -> "vacuous"
  | Unresolvable -> "unresolvable"

(** Classify the IR input a witness entry names.

    [Vacuous] is the identically-zero compiled form — no variables AND a zero
    constant. `hP : P = <numeral>` becomes `Eq(0 = 0)` after the
    definition-unfolding pass and lands here; scaling it changes nothing, so a
    mutation of its coefficient is not a corruption.

    [Constant_nonzero] is a variable-free form that still carries proof
    content, which happens two ways — and BOTH were got wrong here in turn:
    a nonzero constant (the ground contradiction of a goal like `2^18 < P`;
    the first version called this vacuous because it has no variable), and
    `Lt` of the zero form (`0 < 0`; the second version called this vacuous
    because its constant is zero). [Vacuous] is: no variables, zero constant,
    and not strict. *)
let classify (ir : Ir.t) (name : string) : target_class * string =
  let fragment = Farkas.effective_fragment ir in
  match Farkas.lookup_hypothesis ir name with
  | None -> Unresolvable, "no such input"
  | Some shell ->
    (match Farkas.compile_hypothesis ~fragment shell with
     | Error d -> Unresolvable, "does not compile: " ^ d
     | Ok c ->
       let tag, f, strict = match c with
         | Farkas.Le f -> "Le", f, false
         | Farkas.Lt f -> "Lt", f, true
         | Farkas.Eq f -> "Eq", f, false in
       let render = Printf.sprintf "%s(%s)" tag (L.to_string f) in
       if f.L.coeffs <> [] then Has_variables, render
       (* `Lt` of the ZERO form is `0 < 0` — false, so it is a contradiction
          all by itself and supplies the LRA strictness clause. Reading only
          the form's constant calls it vacuous and lets target selection fall
          through to a genuinely vacuous `Eq(0)`, leaving the actual
          contradiction unmutated (R6 checkpoint-2 review, finding 6).
          Strictness lives in the RELATION, so classification must read it. *)
       else if strict then Constant_nonzero, render
       else if L.rat_is_zero f.L.const then Vacuous, render
       else Constant_nonzero, render)

(** Index of the mutation target: the largest |coefficient| among entries
    whose input has variables; failing that, among non-vacuous entries;
    failing that, the largest overall. The class actually reached is reported
    so a reader can see which case applied. *)
let pick_target (ir : Ir.t) (cs : (string * string) list) : int =
  let best_in pred =
    let b = ref None in
    List.iteri (fun i (h, c) ->
      if pred (fst (classify ir h)) then
        match z_opt c with
        | Some z ->
          (match !b with
           | Some (_, m) when Z.geq m (Z.abs z) -> ()
           | _ -> b := Some (i, Z.abs z))
        | None -> ()) cs;
    !b
  in
  match best_in (fun k -> k = Has_variables) with
  | Some (i, _) -> i
  | None ->
    (match best_in (fun k -> k = Constant_nonzero) with
     | Some (i, _) -> i
     | None ->
       (match best_in (fun _ -> true) with Some (i, _) -> i | None -> 0))

(* --- mutations --------------------------------------------------------- *)

let mutation_names = [
  "coefficient_doubled"; "coefficient_off_by_one"; "coefficient_negated";
  "coefficient_zeroed"; "hypothesis_renamed"; "term_dropped";
  "empty_witness"; "coefficient_garbage" ]

let mutate (name : string) (i : int) (cs : (string * string) list)
  : (string * string) list option =
  let at j f = List.mapi (fun k x -> if k = j then f x else x) cs in
  let scale f = at i (fun (h, c) ->
    (h, match z_opt c with Some z -> Z.to_string (f z) | None -> c)) in
  match name with
  | "coefficient_doubled"    -> Some (scale (Z.mul (Z.of_int 2)))
  | "coefficient_off_by_one" -> Some (scale (fun z -> Z.sub z Z.one))
  | "coefficient_negated"    -> Some (scale Z.neg)
  | "coefficient_zeroed"     -> Some (at i (fun (h, _) -> (h, "0")))
  | "hypothesis_renamed"     -> Some (at i (fun (_, c) -> ("no_such_hypothesis", c)))
  | "term_dropped"           -> Some (List.filteri (fun k _ -> k <> i) cs)
  | "empty_witness"          -> Some []
  | "coefficient_garbage"    -> Some (at i (fun (h, _) -> (h, "not-a-number")))
  | _ -> None

(* --- main -------------------------------------------------------------- *)

let () =
  let args = Array.to_list Sys.argv in
  let expect_sat = List.mem "--expect-sat" args in
  let positional = List.filter (fun a -> a <> "--expect-sat") (List.tl args) in
  let ir_path, out_dir, case = match positional with
    | [ a; b; c ] -> a, b, c
    | _ ->
      prerr_endline
        "usage: negcheck.exe [--expect-sat] <ir.json> <out_dir> <case_id>";
      exit 2
  in
  let ir0 = Codec.of_json (J.from_string (read_file ir_path)) in
  let final_ir, trace = Pipeline.run Pipeline.default_dispatch_config ir0 in
  let rewrite_trace_hash = Hash.canonical_sha256 (Trace.to_json trace) in
  let violations = ref [] in
  let fail fmt = Printf.ksprintf (fun s -> violations := s :: !violations) fmt in
  let results = ref [] in
  let add k v = results := (k, v) :: !results in

  (* 1. what the adapters do on this IR *)
  let per_adapter = List.map (fun (name, dispatch) ->
    match dispatch ~rewrite_trace_hash final_ir with
    | Adapter.Cert c ->
      (name, `Assoc [ "outcome", `String "cert"; "tier", `Int c.Certificate.tier;
                      "format", `String c.Certificate.format ], Some c)
    | Adapter.Failed f ->
      (name, `Assoc [ "outcome", `String "failed";
                      "failure", Adapter.failure_to_json f ], None))
    [ "z3", Adapter_z3.dispatch; "cvc5", Adapter_cvc5.dispatch;
      "cvc4", Adapter_cvc4.dispatch ] in
  add "adapters" (`Assoc (List.map (fun (n, j, _) -> (n, j)) per_adapter));

  (* 2. false goals: no adapter may mint anything *)
  if expect_sat then
    List.iter (fun (n, _, c) ->
      if c <> None then
        fail "false-goal check: adapter %s minted a certificate on a goal \
              declared false" n) per_adapter;
  add "false_goal_check"
    (`Assoc [ "asserted", `Bool expect_sat;
              "expectation", `String (if expect_sat
                then "every adapter must fail (no cert minted)"
                else "not asserted for this case") ]);

  (* 3. corrupted certificates *)
  let tier1 = List.find_map (fun (n, _, c) ->
    match (c : Certificate.t option) with
    | Some cert ->
      (match cert.Certificate.payload with
       | Certificate.Tier1_witness { witness_kind = Certificate.Farkas; _ } ->
         Some (n, cert)
       | _ -> None)
    | None -> None) per_adapter in
  (match tier1 with
   | None ->
     add "corrupted_certificate"
       (`Assoc [ "status", `String "not applicable";
                 "detail", `String "no adapter minted a Tier 1 Farkas cert on \
                                    this IR, so there is no genuine cert here \
                                    to corrupt" ])
   | Some (backend, cert) ->
     let wd = match cert.Certificate.payload with
       | Certificate.Tier1_witness { witness_data; _ } -> witness_data
       | _ -> `Null in
     let entries = coefficients wd in
     let baseline_farkas = Farkas.verify final_ir wd in
     let baseline_cert = Verifier.verify ~trace:(Some trace) cert final_ir in
     if baseline_farkas <> Farkas.Verified then
       fail "baseline: the genuine cert from %s does not verify under \
             Farkas.verify (%s)" backend (farkas_verdict_name baseline_farkas);
     (* The certificate verifier is a SECOND shipped interface and it gets its
        own assertion, baseline included. The first version of this file
        computed `cv` and printed it without ever checking it, so forcing
        Verified_farkas for every mutant left gate.ok true
        (R6 checkpoint-2 review, finding 5). A witness mutation leaves the
        envelope untouched, so Verifier.verify dispatches straight to the
        Farkas check: its verdict must be `verified_farkas` exactly when the
        oracle expects acceptance, and something else exactly when it does
        not. *)
     if reason_name baseline_cert <> "verified_farkas" then
       fail "baseline: the genuine cert from %s does not verify under \
             Verifier.verify (%s)" backend (reason_name baseline_cert);
     if not (expected_verified final_ir entries) then
       fail "baseline: the oracle rejects the genuine witness from %s — the \
             oracle and the shipped verifier disagree" backend;
     let ti = pick_target final_ir entries in
     let tname, tcoef = List.nth entries ti in
     let tclass, trender = classify final_ir tname in
     let with_witness w =
       { cert with Certificate.payload = (match cert.Certificate.payload with
           | Certificate.Tier1_witness p ->
             Certificate.Tier1_witness { p with witness_data = w }
           | p -> p) } in
     let muts = List.filter_map (fun m ->
       match mutate m ti entries with
       | None -> None
       | Some mutant ->
         let w = of_coefficients mutant in
         let expect = expected_verified final_ir mutant in
         let fv = Farkas.verify final_ir w in
         let actual = (fv = Farkas.Verified) in
         let cv = Verifier.verify ~trace:(Some trace) (with_witness w) final_ir in
         let cv_name = reason_name cv in
         let cv_accepted = (cv_name = "verified_farkas") in
         if actual <> expect then
           fail "mutation %s on %s: Farkas.verify said %s, oracle expected %s"
             m case (if actual then "VERIFIED" else "rejected")
             (if expect then "VERIFIED" else "rejected");
         if cv_accepted <> expect then
           fail "mutation %s on %s: Verifier.verify said %s (%s), oracle \
                 expected %s"
             m case (if cv_accepted then "VERIFIED" else "rejected") cv_name
             (if expect then "VERIFIED" else "rejected");
         Some (`Assoc [
           "mutation", `String m;
           "witness", w;
           "expected", `String (if expect then "verified" else "rejected");
           "farkas_verify", `String (farkas_verdict_name fv);
           "cert_verify", `String cv_name;
           "agrees_with_oracle", `Bool (actual = expect && cv_accepted = expect);
           "farkas_agrees", `Bool (actual = expect);
           "cert_verifier_agrees", `Bool (cv_accepted = expect);
           (* a mutation that a correct verifier must still accept is a valid
              transformation of the certificate, not a corruption *)
           "kind", `String (if expect then "valid_transformation"
                            else "invalid_mutation") ])) mutation_names in
     let envelope = [
       ("dispatch_context_hash_replaced",
        { cert with Certificate.dispatch_context_hash =
            "sha256:0000000000000000000000000000000000000000000000000000000000000000" });
       ("rewrite_trace_hash_replaced",
        { cert with Certificate.rewrite_trace_hash =
            "sha256:1111111111111111111111111111111111111111111111111111111111111111" });
     ] in
     let env_json = List.map (fun (m, c) ->
       let r = Verifier.verify ~trace:(Some trace) c final_ir in
       let n = reason_name r in
       if n <> "hash_mismatch" then
         fail "envelope mutation %s was not refused as hash_mismatch (got %s)" m n;
       `Assoc [ "mutation", `String m; "cert_verify", `String n;
                "rejected", `Bool (n = "hash_mismatch") ]) envelope in
     add "corrupted_certificate" (`Assoc [
       "status", `String "checked";
       "genuine_cert_from", `String backend;
       "genuine_witness", wd;
       "baseline_farkas_verify", `String (farkas_verdict_name baseline_farkas);
       "baseline_cert_verify", `String (reason_name baseline_cert);
       "mutation_target",
       `Assoc [ "hypothesis", `String tname; "coefficient", `String tcoef;
                "class", `String (class_name tclass);
                "compiled", `String trender ];
       "witness_entry_classes", `List (List.map (fun (h, c) ->
         let k, r = classify final_ir h in
         `Assoc [ "hypothesis", `String h; "coefficient", `String c;
                  "class", `String (class_name k); "compiled", `String r ])
         entries);
       "witness_mutations", `List muts;
       "envelope_mutations", `List env_json;
     ]));

  let vs = List.rev !violations in
  let report = `Assoc ([ "case", `String case;
                         "ir_source", `String ir_path ] @ List.rev !results
                       @ [ "gate", `Assoc [
                             "ok", `Bool (vs = []);
                             "violations",
                             `List (List.map (fun s -> `String s) vs) ] ]) in
  let p = Filename.concat out_dir (case ^ ".negcheck.json") in
  write_file p (J.pretty_to_string report ^ "\n");
  print_endline (J.pretty_to_string report);
  if vs <> [] then begin
    List.iter (fun s -> prerr_endline ("negcheck: " ^ s)) vs;
    exit 1
  end

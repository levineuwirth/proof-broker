(** Tier 3 alethe-2024 per-step checker.

    The Lean re-checker (direction 2 of the Tier 3 plan) parses the
    Alethe proof and walks each step, dispatching the per-step
    soundness check to a rule-specific checker. This module is the
    OCaml side of one such checker: a single rule, [la_generic],
    routed through the existing [Alethe_farkas] + [Farkas]
    infrastructure. The Lean walker calls this via FFI for
    [la_generic] steps; future rules either get their own OCaml
    checkers here, or get implemented natively in Lean.

    Why per-step rather than whole-proof. The Lean walker owns the
    rule-dispatch decision and the [unsupported_rule] bailout — that
    structure is the point of direction 2. Per-step calls keep the
    walker honest: each FFI hop checks exactly one rule's
    application; failures pinpoint the offending step rather than
    swallow the whole proof. The cost (one FFI hop per step) is
    fine for proofs up to a few hundred steps and will only become
    a bottleneck if we ever ship Tier 3 for large industrial
    proofs, at which point batching becomes the optimization.

    Result taxonomy:
    * [Step_verified] — the rule-specific checker accepted the step.
    * [Step_unsupported_rule rule] — no checker registered for [rule]
      on the OCaml side; the walker can either bail or skip.
    * [Step_failed { rule; detail }] — checker rejected the step;
      [detail] explains which arithmetic invariant or shape match
      failed. *)

type step_result =
  | Step_verified
  | Step_unsupported_rule of string
  | Step_failed of { rule : string; detail : string }

(** Per-proof verification environment: the IR plus a map from
    already-verified step IDs (and assume IDs) to their proven
    clauses. Stateful rules ([trans], [cong], [resolution]) look
    up premise clauses through this; stateless rules ([la_generic],
    [refl], [false]) ignore the [proven] table. *)
type env = {
  ir : Ir.t;
  proven : (string, Alethe.Sexp.t list) Hashtbl.t;
}

(** [Sexp.t] structural equality is the right notion for clause
    literals since [Alethe.parse] already expanded named refs, so
    syntactically-equal forms after expansion really mean the same
    literal. *)
let sexp_equal : Alethe.Sexp.t -> Alethe.Sexp.t -> bool = (=)

(** Negate a clause literal: strip [(not L)] to [L]; otherwise wrap
    in [(not L)]. Used by the [resolution] check to pair off
    complementary literals. *)
let complement_literal (lit : Alethe.Sexp.t) : Alethe.Sexp.t =
  match lit with
  | List [ Atom "not"; inner ] -> inner
  | _ -> List [ Atom "not"; lit ]

(** Pop the first occurrence of [needle] from [lst]. [None] when
    no match. Multiset-aware diff via repeated [pop_first]. *)
let pop_first (needle : Alethe.Sexp.t) (lst : Alethe.Sexp.t list)
  : Alethe.Sexp.t list option =
  let rec loop acc = function
    | [] -> None
    | x :: rest when sexp_equal x needle ->
      Some (List.rev_append acc rest)
    | x :: rest -> loop (x :: acc) rest
  in
  loop [] lst

(** Check a single [la_generic] step. Reuses the existing
    [Alethe_farkas] extraction (clause-vs-IR-hypothesis matching by
    linear-form scaling, plus LIA tightening) to produce a Farkas
    witness, then runs [Farkas.verify] on the witness against the
    same IR. Verified iff [Farkas.verify] returns [Verified]. *)
let check_la_generic (ir : Ir.t) (step : Alethe.step) : step_result =
  let fragment = ir.logic_classification.first_order_fragment in
  let inputs = Alethe_farkas.compile_ir_inputs ir in
  match Alethe_farkas.extract_from_step ~fragment ~inputs step with
  | Error e ->
    Step_failed {
      rule = "la_generic";
      detail = Printf.sprintf "%s: %s"
        (Alethe_farkas.error_kind e)
        (Alethe_farkas.error_detail e);
    }
  | Ok entries ->
    let witness =
      Alethe_farkas.witness_to_json (Alethe_farkas.dedupe entries)
    in
    (match Farkas.verify ir witness with
     | Verified -> Step_verified
     | other ->
       Step_failed {
         rule = "la_generic";
         detail = (match other with
           | Verified -> "verified"
           | Unknown_hypothesis { hypothesis } ->
             "unknown_hypothesis: " ^ hypothesis
           | Nonlinear { hypothesis; detail } ->
             Printf.sprintf "nonlinear in %s: %s" hypothesis detail
           | Bad_coefficient { hypothesis; raw } ->
             Printf.sprintf "bad coefficient on %s: %s" hypothesis raw
           | Negative_coefficient { hypothesis; value } ->
             Printf.sprintf "negative coefficient on %s: %s"
               hypothesis value
           | Not_contradictory { residual } ->
             "not contradictory; residual=" ^ residual
           | Malformed_witness { detail } -> detail);
       })

(** [refl]: [(cl (= a a))]. The clause must contain exactly one
    equality literal whose two sides are syntactically equal after
    named-ref expansion. *)
let check_refl (step : Alethe.step) : step_result =
  match step.clause with
  | [ List [ Atom "="; a; b ] ] when sexp_equal a b -> Step_verified
  | [ List [ Atom "="; _; _ ] ] ->
    Step_failed {
      rule = "refl";
      detail = "operands of = are not syntactically equal";
    }
  | _ ->
    Step_failed {
      rule = "refl";
      detail = "expected (cl (= a b)) with one equality literal";
    }

(** [false]: [(cl (not false))]. Asserts the trivial fact that
    [false] is false; used in conjunction with [resolution] to
    convert a [(cl false)] clause into the empty clause [(cl)]. *)
let check_false (step : Alethe.step) : step_result =
  match step.clause with
  | [ List [ Atom "not"; Atom "false" ] ] -> Step_verified
  | _ ->
    Step_failed {
      rule = "false";
      detail = "expected (cl (not false))";
    }

(** [trans]: from [(cl (= a_0 a_1))], [(cl (= a_1 a_2))], …,
    [(cl (= a_{n-1} a_n))], conclude [(cl (= a_0 a_n))]. Each
    premise must be a singleton equality clause whose left-hand
    side is the previous link's right-hand side. *)
let check_trans (env : env) (step : Alethe.step) : step_result =
  let premises = Option.value step.premises ~default:[] in
  match step.clause with
  | [ List [ Atom "="; conclusion_a; conclusion_b ] ] ->
    if premises = [] then
      Step_failed { rule = "trans"; detail = "no premises" }
    else
      let lookup id =
        match Hashtbl.find_opt env.proven id with
        | Some [ List [ Atom "="; a; b ] ] -> Ok (a, b)
        | Some _ -> Error "premise not a singleton equality"
        | None -> Error ("unknown premise: " ^ id)
      in
      let rec walk expected_a = function
        | [] -> Step_failed { rule = "trans"; detail = "empty premise list" }
        | [ id ] ->
          (match lookup id with
           | Error msg -> Step_failed { rule = "trans"; detail = msg }
           | Ok (a, b) ->
             if not (sexp_equal a expected_a) then
               Step_failed {
                 rule = "trans";
                 detail = "last premise lhs doesn't match chain";
               }
             else if sexp_equal b conclusion_b then Step_verified
             else
               Step_failed {
                 rule = "trans";
                 detail = "last premise rhs doesn't match conclusion rhs";
               })
        | id :: rest ->
          (match lookup id with
           | Error msg -> Step_failed { rule = "trans"; detail = msg }
           | Ok (a, b) ->
             if not (sexp_equal a expected_a) then
               Step_failed {
                 rule = "trans";
                 detail = "premise lhs doesn't follow chain";
               }
             else walk b rest)
      in
      walk conclusion_a premises
  | _ ->
    Step_failed {
      rule = "trans";
      detail = "expected (cl (= a b)) singleton equality conclusion";
    }

(** [cong]: from [(cl (= a_1 b_1))], …, [(cl (= a_n b_n))],
    conclude [(cl (= (f a_1 … a_n) (f b_1 … b_n)))]. The premise
    list runs in arg-position order, including trivial [(= a a)]
    refl premises for syntactically-identical arg pairs (cvc5
    always emits all n premises, even the trivial ones). *)
let check_cong (env : env) (step : Alethe.step) : step_result =
  let premises = Option.value step.premises ~default:[] in
  match step.clause with
  | [ List [ Atom "=";
             List (Atom f1 :: args1);
             List (Atom f2 :: args2) ] ]
    when f1 = f2 && List.length args1 = List.length args2 ->
    if List.length premises <> List.length args1 then
      Step_failed {
        rule = "cong";
        detail = "premise count doesn't match function arity";
      }
    else
      let rec walk = function
        | [], [], [] -> Step_verified
        | a :: arest, b :: brest, p :: prest ->
          (match Hashtbl.find_opt env.proven p with
           | Some [ List [ Atom "="; pa; pb ] ]
             when sexp_equal pa a && sexp_equal pb b ->
             walk (arest, brest, prest)
           | Some _ ->
             Step_failed {
               rule = "cong";
               detail = "premise " ^ p ^ " doesn't match arg pair shape";
             }
           | None ->
             Step_failed {
               rule = "cong";
               detail = "unknown premise: " ^ p;
             })
        | _ ->
          Step_failed {
            rule = "cong";
            detail = "args/premises lists desynced (impossible)";
          }
      in
      walk (args1, args2, premises)
  | _ ->
    Step_failed {
      rule = "cong";
      detail = "expected (cl (= (f …) (f …))) with same head symbol";
    }

(** Scale a [Farkas.compiled] form by a rational [k]. The shape
    ([Le]/[Lt]/[Eq]) is preserved — we use this for [la_mult_neg]
    where the conclusion has the same direction as the hypothesis
    (multiplied by [|c|], not [c], so direction doesn't flip). *)
let scale_compiled (k : Linear_arith.rational) (c : Farkas.compiled)
  : Farkas.compiled =
  match c with
  | Farkas.Le f -> Farkas.Le (Linear_arith.scale k f)
  | Farkas.Lt f -> Farkas.Lt (Linear_arith.scale k f)
  | Farkas.Eq f -> Farkas.Eq (Linear_arith.scale k f)

(** Structural equality on [Farkas.compiled] forms. [Linear_arith.t]
    is canonicalized (sorted-assoc-list with no zero entries), so
    OCaml's [=] is the right notion of arithmetic equality. *)
let compiled_equal (a : Farkas.compiled) (b : Farkas.compiled) : bool =
  match a, b with
  | Farkas.Le x, Farkas.Le y
  | Farkas.Lt x, Farkas.Lt y
  | Farkas.Eq x, Farkas.Eq y -> x = y
  | _ -> false

(** [la_mult_neg]: tautological clause
    [(cl (=> (and (< c 0) hyp) conc))], where [c] is a strictly
    negative rational constant and [conc] is [hyp] scaled through
    by [c]. Multiplying an inequality by a negative constant flips
    its direction syntactically, but the resulting Farkas-normal
    form is the same as scaling the original linear form by [|c|]
    (since both [(>= x 3)] and [(<= -x -3)] linearize to the same
    [Le(3 - x)]). We check (a) the implication shape, (b) that
    [(< c 0)] really has [c < 0] and the right-hand side really is
    [0], and (c) that [conc]'s compiled form equals [hyp]'s
    compiled form scaled by [|c|]. *)
let check_la_mult_neg (step : Alethe.step) : step_result =
  match step.clause with
  | [ List [ Atom "=>";
             List [ Atom "and";
                    List [ Atom "<"; c_expr; zero_expr ];
                    hyp_atom ];
             conc_atom ] ] ->
    (match Alethe_farkas.lin_arith c_expr,
           Alethe_farkas.lin_arith zero_expr with
     | Some cl, Some zl
       when Linear_arith.is_constant cl
         && Linear_arith.is_constant zl
         && Linear_arith.rat_is_zero (Linear_arith.constant_value zl)
         && Linear_arith.rat_is_neg (Linear_arith.constant_value cl) ->
       let c = Linear_arith.constant_value cl in
       let abs_c = Linear_arith.rat_neg c in
       (match Alethe_farkas.compile_atom_pos hyp_atom,
              Alethe_farkas.compile_atom_pos conc_atom with
        | Some hc, Some cc ->
          if compiled_equal (scale_compiled abs_c hc) cc then Step_verified
          else
            Step_failed {
              rule = "la_mult_neg";
              detail = "conclusion is not hyp scaled by |c|";
            }
        | _ ->
          Step_failed {
            rule = "la_mult_neg";
            detail = "hyp or conc atom not linearizable";
          })
     | _ ->
       Step_failed {
         rule = "la_mult_neg";
         detail = "(< c 0) premise: c not a negative constant or 0 not zero";
       })
  | _ ->
    Step_failed {
      rule = "la_mult_neg";
      detail = "expected (cl (=> (and (< c 0) hyp) conc))";
    }

(** [equiv_pos2]: tautological clause [(cl (not (= φ ψ)) (not φ) ψ)].
    Encodes "from [φ ↔ ψ] and [φ], conclude [ψ]" in clause form;
    sound regardless of [φ], [ψ] since the disjunction is a
    propositional tautology. We just check the three-literal shape
    matches with the same [φ] and [ψ] across positions. *)
let check_equiv_pos2 (step : Alethe.step) : step_result =
  match step.clause with
  | [ List [ Atom "not"; List [ Atom "="; phi1; psi1 ] ];
      List [ Atom "not"; phi2 ];
      psi2 ]
    when sexp_equal phi1 phi2 && sexp_equal psi1 psi2 -> Step_verified
  | _ ->
    Step_failed {
      rule = "equiv_pos2";
      detail = "expected (cl (not (= phi psi)) (not phi) psi)";
    }

(** [equiv_simplify]: a rewrite rule whose conclusion is always a
    singleton equivalence [(cl (= LHS RHS))] for one of the standard
    boolean simplifications:
    - [(= φ true) ↔ φ], [(= true φ) ↔ φ]
    - [(= φ false) ↔ (not φ)], [(= false φ) ↔ (not φ)]
    - [(= φ φ) ↔ true]
    cvc5's fixture only uses the first form, but the others are the
    same shape-check cost. *)
let check_equiv_simplify (step : Alethe.step) : step_result =
  let ok =
    match step.clause with
    | [ List [ Atom "="; List [ Atom "="; a; Atom "true" ]; b ] ]
      when sexp_equal a b -> true
    | [ List [ Atom "="; List [ Atom "="; Atom "true"; a ]; b ] ]
      when sexp_equal a b -> true
    | [ List [ Atom "=";
               List [ Atom "="; a; Atom "false" ];
               List [ Atom "not"; b ] ] ]
      when sexp_equal a b -> true
    | [ List [ Atom "=";
               List [ Atom "="; Atom "false"; a ];
               List [ Atom "not"; b ] ] ]
      when sexp_equal a b -> true
    | [ List [ Atom "="; List [ Atom "="; a; b ]; Atom "true" ] ]
      when sexp_equal a b -> true
    | _ -> false
  in
  if ok then Step_verified
  else Step_failed {
    rule = "equiv_simplify";
    detail = "no recognized boolean-simplification shape";
  }

(** [and_neg]: tautological clause [(cl (and l_1 … l_n) (not l_1) …
    (not l_n))]. Encodes the de Morgan / and-introduction tautology.
    Shape check: head literal is [(and a_1 … a_n)], remaining literals
    are [(not a_1)], …, [(not a_n)] in order. *)
let check_and_neg (step : Alethe.step) : step_result =
  match step.clause with
  | Alethe.Sexp.List (Atom "and" :: args) :: rest
    when List.length rest = List.length args ->
    let rec walk args rest =
      match args, rest with
      | [], [] -> true
      | a :: arest,
        Alethe.Sexp.List [ Atom "not"; b ] :: nrest
        when sexp_equal a b -> walk arest nrest
      | _ -> false
    in
    if walk args rest then Step_verified
    else Step_failed {
      rule = "and_neg";
      detail = "negated literals don't match (and …) operands in order";
    }
  | _ ->
    Step_failed {
      rule = "and_neg";
      detail = "expected (cl (and l_1 … l_n) (not l_1) … (not l_n))";
    }

(** [implies]: from premise [(cl (=> A B))], conclude [(cl (not A) B)].
    Implication elimination as a clause rewrite. *)
let check_implies (env : env) (step : Alethe.step) : step_result =
  let premises = Option.value step.premises ~default:[] in
  match premises, step.clause with
  | [ p ], [ List [ Atom "not"; a_concl ]; b_concl ] ->
    (match Hashtbl.find_opt env.proven p with
     | Some [ List [ Atom "=>"; a_prem; b_prem ] ]
       when sexp_equal a_prem a_concl && sexp_equal b_prem b_concl ->
       Step_verified
     | Some _ ->
       Step_failed {
         rule = "implies";
         detail = "premise not (cl (=> A B)) matching conclusion";
       }
     | None ->
       Step_failed {
         rule = "implies";
         detail = "unknown premise: " ^ p;
       })
  | _ ->
    Step_failed {
      rule = "implies";
      detail = "expected one premise and (cl (not A) B) conclusion";
    }

(** [equiv1]: from premise [(cl (= A B))], conclude [(cl (not A) B)].
    One direction of equivalence elimination (the [equiv2] sibling
    yields [(cl A (not B))]; we register only [equiv1] until cvc5
    emits the other on a real proof). *)
let check_equiv1 (env : env) (step : Alethe.step) : step_result =
  let premises = Option.value step.premises ~default:[] in
  match premises, step.clause with
  | [ p ], [ List [ Atom "not"; a_concl ]; b_concl ] ->
    (match Hashtbl.find_opt env.proven p with
     | Some [ List [ Atom "="; a_prem; b_prem ] ]
       when sexp_equal a_prem a_concl && sexp_equal b_prem b_concl ->
       Step_verified
     | Some _ ->
       Step_failed {
         rule = "equiv1";
         detail = "premise not (cl (= A B)) matching conclusion";
       }
     | None ->
       Step_failed {
         rule = "equiv1";
         detail = "unknown premise: " ^ p;
       })
  | _ ->
    Step_failed {
      rule = "equiv1";
      detail = "expected one premise and (cl (not A) B) conclusion";
    }

(** [resolution]: from premise clauses C_1, …, C_n derive the
    conclusion clause D. The check is multiset-based: the
    multiset of premise literals minus the multiset of conclusion
    literals must consist entirely of complementary pairs
    [(L, ¬L)]. Sound but slightly incomplete — declines proofs
    that need [factoring] (duplicate-literal collapse), which
    Alethe technically handles via a separate rule. *)
let check_resolution (env : env) (step : Alethe.step) : step_result =
  let premises = Option.value step.premises ~default:[] in
  if premises = [] then
    Step_failed { rule = "resolution"; detail = "no premises" }
  else
    let unknown = List.filter
      (fun id -> not (Hashtbl.mem env.proven id)) premises
    in
    if unknown <> [] then
      Step_failed {
        rule = "resolution";
        detail = "unknown premises: " ^ String.concat ", " unknown;
      }
    else
      let premise_lits = List.concat_map
        (fun id -> Hashtbl.find env.proven id) premises
      in
      let conclusion_lits = step.clause in
      let rec subtract removed = function
        | [] -> Ok removed
        | lit :: rest ->
          (match pop_first lit removed with
           | Some removed' -> subtract removed' rest
           | None ->
             Error (Printf.sprintf
               "conclusion literal not in any premise: %s"
               (Alethe.Sexp.to_string lit)))
      in
      (match subtract premise_lits conclusion_lits with
       | Error msg -> Step_failed { rule = "resolution"; detail = msg }
       | Ok removed ->
         let rec pair_up = function
           | [] -> Ok ()
           | lit :: rest ->
             let comp = complement_literal lit in
             (match pop_first comp rest with
              | Some rest' -> pair_up rest'
              | None ->
                Error (Printf.sprintf
                  "unpaired residual literal (no complement): %s"
                  (Alethe.Sexp.to_string lit)))
         in
         (match pair_up removed with
          | Ok () -> Step_verified
          | Error msg ->
            Step_failed { rule = "resolution"; detail = msg }))

(** Top-level rule dispatch. Add a new clause here when wiring an
    OCaml-side checker for another Alethe rule, and add the same
    rule name to [supported_rules] below. The walker treats
    [Step_unsupported_rule _] as the bailout — Tier 3 verification
    fails when any step uses a rule no checker handles. *)
let check_step (env : env) (step : Alethe.step) : step_result =
  match step.rule with
  | "la_generic" -> check_la_generic env.ir step
  | "refl" -> check_refl step
  | "false" -> check_false step
  | "trans" -> check_trans env step
  | "cong" -> check_cong env step
  | "resolution" -> check_resolution env step
  | "equiv_pos2" -> check_equiv_pos2 step
  | "equiv_simplify" -> check_equiv_simplify step
  | "and_neg" -> check_and_neg step
  | "implies" -> check_implies env step
  | "equiv1" -> check_equiv1 env step
  | "la_mult_neg" -> check_la_mult_neg step
  | other -> Step_unsupported_rule other

(** Sorted list of every Alethe rule [check_step] has a registered
    checker for. Must stay in sync with the [check_step] match
    above; [test_supported_rules_sync] in [test_tier3_alethe]
    pins this. The cvc5 minter consults this set to decide whether
    a parsed proof is eligible for Tier 3 minting (the "fail
    closed" gate of direction 3). *)
let supported_rules : string list = [
  "and_neg"; "cong"; "equiv1"; "equiv_pos2"; "equiv_simplify";
  "false"; "implies"; "la_generic"; "la_mult_neg"; "refl";
  "resolution"; "trans";
]

(** True iff every step in [p] uses a rule [check_step] knows. The
    cvc5 minter uses this to decide between minting Tier 3 (gate
    passes) and falling back to lower-tier paths (gate fails);
    keeps the minting side and the verifier side aligned, so a
    minted Tier 3 cert is always re-checkable by the verifier as
    of mint time. *)
let proof_rules_supported (p : Alethe.proof) : bool =
  let supported = supported_rules in
  List.for_all
    (fun (s : Alethe.step) ->
      String.length s.rule = 0 || List.mem s.rule supported)
    p.steps

(** Render a [step_result] as the FFI envelope payload shape:
    [{ok: bool, kind: <reason kind>, [detail | rule]: ...}]. *)
let step_result_to_json (r : step_result) : Yojson.Safe.t =
  match r with
  | Step_verified ->
    `Assoc [ "ok", `Bool true; "kind", `String "step_verified" ]
  | Step_unsupported_rule rule ->
    `Assoc [
      "ok", `Bool false;
      "kind", `String "step_unsupported_rule";
      "rule", `String rule;
    ]
  | Step_failed { rule; detail } ->
    `Assoc [
      "ok", `Bool false;
      "kind", `String "step_failed";
      "rule", `String rule;
      "detail", `String detail;
    ]

(* --- whole-proof verification --------------------------------------- *)

(** Whole-proof verification verdict. [Verified] when every step's
    rule has a registered checker and every check accepted; one of
    the two failure variants names the offending step so dashboards
    can pinpoint where Tier 3 verification stopped. *)
type verify_result =
  | Verified
  | Unsupported_rule of { rule : string; step_id : string }
  | Step_failed of { step_id : string; rule : string; detail : string }

(** True iff [clause] is the empty clause [(cl)] or its
    [cvc5]-flavored equivalent [(cl false)] (a singleton clause
    with the [false] literal). cvc5's Alethe output usually
    terminates with one or the other; both denote the bottom
    derivation. *)
let is_terminal_clause (clause : Alethe.Sexp.t list) : bool =
  match clause with
  | [] -> true
  | [ Atom "false" ] -> true
  | _ -> false

(** Verify a Tier 3 alethe-2024 proof end-to-end. Walks every step
    in input order, threading an [env] populated with the assumes'
    atoms (as singleton clauses) and each verified step's clause
    so stateful rules ([trans], [cong], [resolution]) can look up
    premises. Returns on the first unsupported-rule or
    step-failure. After all steps pass, requires the final step's
    clause to be terminal ([(cl)] or [(cl false)]) — otherwise the
    proof verified locally but didn't reach the bottom derivation,
    and we surface that as a [Step_failed] on the final step.

    A parse error surfaces as a [Step_failed] with [step_id = ""]
    and [rule = "<parse>"] so callers don't need a third failure
    arm. *)
let verify (ir : Ir.t) (proof_str : string) : verify_result =
  let proof =
    try Ok (Alethe.parse proof_str)
    with Alethe.Parse_error msg -> Error msg
  in
  match proof with
  | Error msg ->
    Step_failed { step_id = ""; rule = "<parse>"; detail = msg }
  | Ok p ->
    let env = { ir; proven = Hashtbl.create 32 } in
    (* Seed the environment with each assume's atom as a singleton
       clause. Resolution premises can then reference assume IDs
       directly. *)
    List.iter
      (fun (id, atom) -> Hashtbl.replace env.proven id [ atom ])
      p.assumes;
    let rec walk = function
      | [] ->
        (* Every step verified; check the final step's clause is
           terminal. An empty step list is also a failure (no
           proof at all). *)
        (match List.rev p.steps with
         | [] ->
           Step_failed {
             step_id = "";
             rule = "<empty>";
             detail = "proof has no steps";
           }
         | last :: _ ->
           if is_terminal_clause last.clause then Verified
           else
             Step_failed {
               step_id = last.id;
               rule = last.rule;
               detail = "final step does not derive (cl) or (cl false)";
             })
      | (step : Alethe.step) :: rest ->
        (match check_step env step with
         | Step_verified ->
           Hashtbl.replace env.proven step.id step.clause;
           walk rest
         | Step_unsupported_rule rule ->
           Unsupported_rule { rule; step_id = step.id }
         | Step_failed { rule; detail } ->
           Step_failed { step_id = step.id; rule; detail })
    in
    walk p.steps

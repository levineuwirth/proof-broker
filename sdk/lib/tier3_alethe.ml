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

module StringSet = Set.Make (String)

(** Per-proof verification environment: the IR plus a map from
    already-verified step IDs (and assume IDs) to their proven
    clauses. Stateful rules ([trans], [cong], [resolution], …)
    look up premise clauses through this; stateless rules
    ([la_generic], [refl], [false]) ignore the [proven] table.

    [last_step_clause] tracks the most recently verified step's
    clause in input order; [subproof]'s soundness check needs the
    body conclusion (the step immediately before the [subproof]
    close), and rather than re-derive it by scanning the proof,
    we just remember it as the walker advances. Reset to [None]
    on entry, mutated each time [walk] verifies a step.

    [last_step_id] tracks the ID of the same step. Pairing it
    with the clause lets [check_subproof] enforce that the body
    conclusion lives in the subproof being closed: closing [T]
    requires the most recent step to be a direct child of [T]
    ([enclosing_subproof_id last_step_id = Some T]). Without this
    check the close would happily lift a clause derived in a
    deeper, still-open nested subproof — leaking that nested
    scope's local assumes through the outer discharge. *)
type env = {
  ir : Ir.t;
  proven : (string, Alethe.Sexp.t list) Hashtbl.t;
  assumes : (string, Alethe.Sexp.t) Hashtbl.t;
  (** Per-step assumption-dependency set. Each entry maps a
      step or assume ID to the set of (transitive) assumption IDs
      its clause depends on. Assumes are seeded with their own
      singleton; non-assume steps inherit the union of their
      premises' deps; [subproof] close subtracts the [:discharge]
      set. [check_subproof] uses these to enforce that every
      same-scope local assume the body actually consumed appears
      in [:discharge] — without this, a body could derive [false]
      from an undisclosed local assume [t1.bad], close while
      discharging only [t1.p], and export [(cl (not P) false)],
      which combined with a global proof of [P] resolves to the
      empty clause and is unsound. *)
  deps : (string, StringSet.t) Hashtbl.t;
  mutable last_step_clause : Alethe.Sexp.t list option;
  mutable last_step_id : string option;
  (** Set by [check_la_generic] when it verifies: the local-assume
      IDs whose Farkas inputs took a non-zero coefficient. The
      walker reads this when computing the la_generic step's
      [deps] entry, then resets to [None]. la_generic doesn't
      surface premises in [step.premises] (the rule pairs clause
      literals with [:args] coefficients implicitly), so we
      thread this signal explicitly rather than re-running the
      matching logic outside the rule. *)
  mutable last_la_generic_consumed : StringSet.t option;
}

(** Translate an IR shell to its [Alethe.Sexp.t] form, mirroring
    what cvc5 would emit when given this term as part of an
    SMT-LIB assert. Symbol names are normalized to SMT-LIB
    primitives ([HAdd.hAdd] → [+], [LE.le] → [<=], etc.) so the
    output matches cvc5's atom shapes after named-ref expansion.
    Returns [None] for shapes that have no SMT-LIB atomic form
    (Forall, Lambda, Opaque), which can't appear as Tier 3
    assume atoms anyway. *)
let rec shell_to_sexp (t : Ir.shell_term) : Alethe.Sexp.t option =
  let arith_sym = function
    | "HAdd.hAdd" | "Int.add" | "Add.add" | "+" -> "+"
    | "HSub.hSub" | "Int.sub" | "Sub.sub" | "-" -> "-"
    | "HMul.hMul" | "Int.mul" | "Mul.mul" | "*" -> "*"
    | "Neg.neg" | "Int.neg" -> "-"
    | "LE.le" | "<=" -> "<="
    | "LT.lt" | "<"  -> "<"
    | "GE.ge" | ">=" -> ">="
    | "GT.gt" | ">"  -> ">"
    | s -> s
  in
  let bin op a b =
    match shell_to_sexp a, shell_to_sexp b with
    | Some sa, Some sb -> Some (Alethe.Sexp.List [ Atom op; sa; sb ])
    | _ -> None
  in
  match t with
  | Var { name } -> Some (Atom name)
  | Const { name = "True" } -> Some (Atom "true")
  | Const { name = "False" } -> Some (Atom "false")
  | Const { name } -> Some (Atom name)
  | Num_lit { value; _ } -> Some (Atom value)
  | And { left; right } -> bin "and" left right
  | Or  { left; right } -> bin "or"  left right
  | Implies { antecedent; consequent } ->
    bin "=>" antecedent consequent
  | Not { operand } ->
    (match shell_to_sexp operand with
     | Some s -> Some (List [ Atom "not"; s ])
     | None -> None)
  | Eq { left; right; _ } -> bin "=" left right
  | App { symbol; args; _ } ->
    let sargs = List.map shell_to_sexp args in
    if List.for_all Option.is_some sargs then
      Some (List (Atom (arith_sym symbol)
                  :: List.map Option.get sargs))
    else None
  | _ -> None

(** Canonicalize numeric atoms in a Sexp by parsing them as
    rationals and re-emitting via [rat_to_string]. This makes
    cvc5's [3/1] match the IR's [3], and [-3/1] match [-3], so
    structural equality on normalized Sexps is the right
    arithmetic-aware notion of equality between assume atoms and
    IR-derived atoms. *)
let rec normalize_numeric_atoms (s : Alethe.Sexp.t) : Alethe.Sexp.t =
  match s with
  | Atom a ->
    (match Linear_arith.rat_of_string a with
     | Some r -> Atom (Linear_arith.rat_to_string r)
     | None -> Atom a)
  | List xs -> List (List.map normalize_numeric_atoms xs)

(** Validate top-level assumes against the IR. Each top-level
    [(assume aN ATOM)] in cvc5's output must correspond to either
    an IR hypothesis or the negated goal — otherwise a malicious
    or buggy proof could simply [(assume a99 false)] and use it
    as a global premise. We compute the expected atom set from
    the IR's hypotheses plus [(not goal)] (omitting the negation
    when [goal = False] since [(not False) = True] is trivially
    valid and cvc5 doesn't bother asserting it), normalize both
    sides, and require every top-level assume's atom to appear in
    the expected set.

    Subproof-local assumes (IDs with a dot) are out of scope here
    — they're introduced by their enclosing [(anchor)] block and
    don't need to back to an IR-level fact. *)
let validate_top_level_assumes
    (ir : Ir.t) (assumes : (string * Alethe.Sexp.t) list)
  : (unit, string) result =
  let expected =
    let from_hyps =
      List.filter_map (fun (h : Ir.hypothesis) ->
        match shell_to_sexp h.shell with
        | Some s -> Some (normalize_numeric_atoms s)
        | None -> None) ir.context.hypotheses
    in
    (* Always include (not goal) — the SMT-LIB script asserts it
       regardless of whether [(not goal)] is a tautology. cvc5
       emits the corresponding [(assume aN (not <goal>))] step
       even when the negation is trivially true (e.g.
       [(not false)] for a [Const False] goal). *)
    let neg_goal =
      match shell_to_sexp ir.goal.shell with
      | Some s -> [ normalize_numeric_atoms (List [ Atom "not"; s ]) ]
      | None -> []
    in
    from_hyps @ neg_goal
  in
  let check_one (id, atom) =
    (* Skip subproof-local assumes (dotted IDs). *)
    match Alethe.enclosing_subproof_id id with
    | Some _ -> Ok ()
    | None ->
      let normed = normalize_numeric_atoms atom in
      if List.exists (fun e -> e = normed) expected then Ok ()
      else
        Error (Printf.sprintf
          "top-level assume %s = %s does not match any IR hypothesis or \
           the negated goal" id (Alethe.Sexp.to_string atom))
  in
  let rec walk = function
    | [] -> Ok ()
    | a :: rest ->
      (match check_one a with
       | Ok () -> walk rest
       | Error msg -> Error msg)
  in
  walk assumes

(** Validate that every dotted assume / step ID has a corresponding
    [(anchor :step ID)] opening for each prefix in its dotted path.
    A top-level [(assume t1.t2.a0 ...)] without an enclosing anchor
    structure is structurally illegitimate — Alethe's emission
    discipline never produces it — and admitting it would let a
    proof seed a fake nested-local premise that no anchor opened.

    Returns [Ok ()] when every dotted ID's enclosing-subproof
    prefix appears in [anchors]; otherwise reports the offending
    ID. *)
let validate_anchor_structure
    ~(anchors : string list)
    ~(assumes : (string * Alethe.Sexp.t) list)
    ~(steps : Alethe.step list)
  : (unit, string) result =
  let opened = List.fold_left
                 (fun acc id -> Hashtbl.replace acc id (); acc)
                 (Hashtbl.create 16) anchors in
  let prefixes (id : string) : string list =
    let rec loop acc s =
      match Alethe.enclosing_subproof_id s with
      | None -> List.rev acc
      | Some p -> loop (p :: acc) p
    in
    loop [] id
  in
  let check_id ~kind id =
    let ps = prefixes id in
    let bad = List.find_opt (fun p -> not (Hashtbl.mem opened p)) ps in
    match bad with
    | None -> Ok ()
    | Some p ->
      Error (Printf.sprintf
        "%s id %s has dotted prefix %s with no matching (anchor :step %s)"
        kind id p p)
  in
  let rec walk_assumes = function
    | [] -> Ok ()
    | (id, _) :: rest ->
      (match check_id ~kind:"assume" id with
       | Ok () -> walk_assumes rest
       | Error _ as e -> e)
  in
  let rec walk_steps = function
    | [] -> Ok ()
    | (s : Alethe.step) :: rest ->
      (match check_id ~kind:"step" s.id with
       | Ok () -> walk_steps rest
       | Error _ as e -> e)
  in
  match walk_assumes assumes with
  | Error _ as e -> e
  | Ok () -> walk_steps steps

(** True iff [id] is in scope at [step.id]. An ID with no dot is
    "global" and always in scope. An ID like [t1.a0] is local to
    subproof [t1] and is in scope only when the current step's ID
    has [t1.] as a prefix (so [t1.t10], [t1.t5.t8], etc. can see
    [t1.a0]; [t22.t5] cannot). The scope check rules out the most
    pernicious bug class identified by the review: a malicious or
    buggy proof citing a subproof-local assume from outer scope or
    a sibling subproof. *)
let id_in_scope_of (step_id : string) (id : string) : bool =
  match Alethe.enclosing_subproof_id id with
  | None -> true
  | Some encl ->
    let prefix = encl ^ "." in
    let plen = String.length prefix in
    String.length step_id >= plen
    && String.sub step_id 0 plen = prefix

(** Scope-aware lookup. Returns the clause keyed by [id] in
    [env.proven] only if [id] is in [step]'s scope. Wraps every
    rule's premise/discharge lookup so a top-level step cannot
    cite a subproof-local assume, and a step in subproof [t22]
    cannot cite an assume from sibling [t1]. *)
let proven_in_scope (env : env) (step : Alethe.step) (id : string)
  : Alethe.Sexp.t list option =
  if id_in_scope_of step.id id then Hashtbl.find_opt env.proven id
  else None

(** Recover the set of local-assume atoms in scope at [step.id].

    Subproof bodies open fresh assume scopes: assumes parsed
    inside [(anchor :step T)] have IDs prefixed [T.] and live
    inside that block plus any of its descendants. The correct
    structural rule is "assume A is visible at step S iff A's
    enclosing subproof is an ancestor of S's path". An earlier
    iteration here used a raw prefix match against the step's
    enclosing-subproof path, which over-collected: a step at
    [t1.body] (enclosing [t1]) saw assumes from sibling
    subproof [t1.t2] like [t1.t2.a0] because they happened to
    start with [t1.] too. That sibling-leak was not blocked by
    the subproof-close direct-child check, since the leaking
    la_generic step is itself a direct child of [t1] — only its
    *premises* came from a non-ancestor scope.

    Now uses [id_in_scope_of] for each candidate assume, which
    asks the right structural question: is the assume's
    enclosing subproof actually a strict prefix of [step.id]'s
    dotted path? [t1.t2.a0]'s enclosing [t1.t2] is not a prefix
    of [t1.body], so it's correctly excluded.

    Used by [check_la_generic] so a la_generic step inside a
    subproof can use local assumes as additional Farkas inputs
    (the case-split fixture has la_generic steps inside [t1]'s
    body that reference [t1.a0] — those won't match any IR
    hypothesis but match the local-assume atoms exactly). *)
let local_assume_atoms (env : env) (step : Alethe.step)
  : (string * Alethe.Sexp.t) list =
  Hashtbl.fold (fun id atom acc ->
    if id_in_scope_of step.id id
       && Option.is_some (Alethe.enclosing_subproof_id id)
    then (id, atom) :: acc else acc) env.assumes []

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

(** Sum a Farkas witness [(name, coef)] against the precompiled
    [inputs] and report whether the residual is a strictly-positive
    constant (contradiction). Sibling of [Farkas.verify], differing
    only in that it consumes the already-compiled inputs (so it
    works for local-assume names that aren't IR hypotheses). *)
let verify_witness_with_inputs
    (inputs : Alethe_farkas.input_entry list)
    (entries : (string * Linear_arith.rational) list)
  : (unit, string) result =
  let lookup_compiled name =
    List.find_map (fun (e : Alethe_farkas.input_entry) ->
      if e.name = name then Some e.compiled else None) inputs
  in
  let rec sum_up acc has_strict = function
    | [] -> Ok (acc, has_strict)
    | (name, coef) :: rest ->
      (match lookup_compiled name with
       | None -> Error ("unknown input: " ^ name)
       | Some (Farkas.Le f) ->
         if not (Linear_arith.rat_is_nonneg coef) then
           Error ("negative coefficient on " ^ name)
         else
           sum_up (Linear_arith.add acc (Linear_arith.scale coef f))
             has_strict rest
       | Some (Farkas.Lt f) ->
         if not (Linear_arith.rat_is_nonneg coef) then
           Error ("negative coefficient on " ^ name)
         else
           let strict' = has_strict || Linear_arith.rat_is_pos coef in
           sum_up (Linear_arith.add acc (Linear_arith.scale coef f))
             strict' rest
       | Some (Farkas.Eq f) ->
         sum_up (Linear_arith.add acc (Linear_arith.scale coef f))
           has_strict rest)
  in
  match sum_up Linear_arith.zero false entries with
  | Error msg -> Error msg
  | Ok (residual, has_strict) ->
    if not (Linear_arith.is_constant residual) then
      Error ("not contradictory; residual=" ^ Linear_arith.to_string residual)
    else
      let c = Linear_arith.constant_value residual in
      let ok =
        if has_strict then Linear_arith.rat_is_nonneg c
        else Linear_arith.rat_is_pos c
      in
      if ok then Ok ()
      else
        Error ("non-positive residual constant: "
               ^ Linear_arith.rat_to_string c)

(** Check a single [la_generic] step. Reuses [Alethe_farkas]
    extraction (clause-vs-input matching by linear-form scaling,
    plus LIA tightening) to produce a Farkas witness, then runs
    [verify_witness_with_inputs] on the precompiled inputs (IR
    hypotheses + any local assumes in scope). Verified iff the
    residual sum is a positive constant. *)
let check_la_generic (env : env) (step : Alethe.step) : step_result =
  let ir = env.ir in
  let fragment = Farkas.effective_fragment ir in
  let base_inputs = Alethe_farkas.compile_ir_inputs ir in
  (* Add local-assume atoms (if [step] is inside a subproof) as
     Farkas inputs alongside the IR's hypotheses. The la_generic
     check otherwise only matches against IR hyps, which is wrong
     inside a subproof body where the local assumes are also
     usable facts. *)
  let local_inputs =
    List.filter_map (fun (id, atom) ->
      match Alethe_farkas.compile_assume_atom ~fragment atom with
      | Some compiled ->
        Some Alethe_farkas.{ name = id; compiled }
      | None -> None) (local_assume_atoms env step)
  in
  let inputs = base_inputs @ local_inputs in
  match Alethe_farkas.extract_from_step ~fragment ~inputs step with
  | Error e ->
    Step_failed {
      rule = "la_generic";
      detail = Printf.sprintf "%s: %s"
        (Alethe_farkas.error_kind e)
        (Alethe_farkas.error_detail e);
    }
  | Ok entries ->
    (* Verify directly against the precompiled inputs rather than
       re-resolving names through [Farkas.verify]. The names may
       reference local-assume IDs (e.g. [t1.a0]) that aren't IR
       hypotheses; [Farkas.verify] would reject those as
       Unknown_hypothesis. *)
    let deduped = Alethe_farkas.dedupe entries in
    (match verify_witness_with_inputs inputs deduped with
     | Ok () ->
       (* Record which local-assume IDs participated with a
          non-zero coefficient so the walker can fold them into
          this step's dependency set. IR-hypothesis names are
          not local assumes and don't propagate as deps. *)
       let local_names =
         List.fold_left (fun acc (id, _) ->
           StringSet.add id acc)
           StringSet.empty
           (List.map fst (local_assume_atoms env step)
            |> List.filter_map (fun id ->
                if Hashtbl.mem env.assumes id then Some (id, ()) else None))
       in
       let consumed =
         List.fold_left (fun acc (name, coef) ->
           if (not (Linear_arith.rat_is_zero coef))
              && StringSet.mem name local_names
           then StringSet.add name acc else acc)
           StringSet.empty deduped
       in
       env.last_la_generic_consumed <- Some consumed;
       Step_verified
     | Error msg -> Step_failed { rule = "la_generic"; detail = msg })

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
        match proven_in_scope env step id with
        | Some [ List [ Atom "="; a; b ] ] -> Ok (a, b)
        | Some _ -> Error "premise not a singleton equality"
        | None -> Error ("unknown or out-of-scope premise: " ^ id)
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
          (match proven_in_scope env step p with
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
               detail = "unknown or out-of-scope premise: " ^ p;
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

(** Evaluate a constant comparison literal like [(<= 0 -2)] or
    [(< -1 0)] to a boolean, when both operands are numeric
    constants. Returns [None] if either operand isn't a constant
    or the operator isn't a recognized arithmetic comparison.
    Used by the [hole]/[rare_rewrite] equality-rewrite checkers
    to prove things like [(<= 0 -2) = false]. *)
let evaluate_comparison_to_bool (lhs : Alethe.Sexp.t) : bool option =
  let const_of e =
    match Alethe_farkas.lin_arith e with
    | Some lf when Linear_arith.is_constant lf ->
      Some (Linear_arith.constant_value lf)
    | _ -> None
  in
  match lhs with
  | List [ Atom op; a; b ] ->
    (match const_of a, const_of b with
     | Some ra, Some rb ->
       let d = Linear_arith.rat_sub ra rb in
       (match op with
        | "<=" -> Some (not (Linear_arith.rat_is_pos d))
        | "<"  -> Some (Linear_arith.rat_is_neg d)
        | ">=" -> Some (Linear_arith.rat_is_nonneg d)
        | ">"  -> Some (Linear_arith.rat_is_pos d)
        | "="  -> Some (Linear_arith.rat_is_zero d)
        | _ -> None)
     | _ -> None)
  | _ -> None

(** Reduce a literal to a canonical [Farkas.compiled] form, treating
    arbitrary nesting of [(not ...)] as repeated negation. Counts
    the [(not)] wrappers; even count means the inner atom stays
    positive, odd means negate. Under non-LRA fragments (LIA), a
    final [Lt] is folded to [Le(f+1)] via the +1 trick — sound only
    over the integers, but exactly the trick cvc5 uses internally
    when emitting tightening rewrites like [(<= n 10) = (not (>= n
    11))]. Returns [None] when the inner atom isn't a Farkas-amenable
    comparison or when the negation produces a non-inequality
    (negating an [Eq] yields a disjunction, not a single Farkas
    form, and we don't normalize that case). *)
let normalize_literal ?(fragment = "LRA") (lit : Alethe.Sexp.t)
  : Farkas.compiled option =
  let lia = not (String.equal fragment "LRA") in
  let rec count_nots n s =
    match s with
    | Alethe.Sexp.List [ Alethe.Sexp.Atom "not"; inner ] ->
      count_nots (n + 1) inner
    | _ -> (n, s)
  in
  let (n, atom) = count_nots 0 lit in
  match Alethe_farkas.compile_atom_pos atom with
  | None -> None
  | Some c ->
    let normed =
      if n mod 2 = 0 then Some c
      else Alethe_farkas.neg_compiled c
    in
    (match normed with
     | None -> None
     | Some r when lia -> Some (Alethe_farkas.lia_normalize r)
     | Some r -> Some r)

(** Evaluate a literal whose top-level structure is some number of
    [(not ...)] wrappers around a [true]/[false] atom. Used to
    handle theory rewrites like [(not (not true)) = true] and
    [(= true (not false))] that cvc5 emits as ground propositional
    folds. Returns [None] for any other shape. *)
let evaluate_constant_literal (lit : Alethe.Sexp.t) : bool option =
  let rec walk parity = function
    | Alethe.Sexp.Atom "true" -> Some parity
    | Alethe.Sexp.Atom "false" -> Some (not parity)
    | Alethe.Sexp.List [ Alethe.Sexp.Atom "not"; inner ] ->
      walk (not parity) inner
    | _ -> None
  in
  walk true lit

(** Verify a theory-rewrite equality [(= LHS RHS)]. Strategy, in
    order of generality:
    1. Linear-form arithmetic equality: linearize both sides via
       [Alethe_farkas.lin_arith] and compare canonical forms.
       Handles constant-fold rewrites (e.g. [-1] times [3] equals
       [-3]) and algebraic identities (e.g. [x] plus [-x] equals
       [0]).
    2. Normalized-literal equality: reduce each side to a canonical
       [Farkas.compiled] form, accounting for [(not)] nesting and
       LIA tightening. Handles direction flips, double negation,
       LIA tightenings (over the integers, [n <= 10] is the same
       atom as [not (n >= 11)]), equation rearrangements (an
       equation reordered or moved to one side), and any
       composition of these.
    3. Constant-boolean evaluation: if both sides reduce to the
       same boolean via [(not)] wrappers around [true]/[false],
       accept. Handles propositional folds like [(not (not true))
       = true].
    4. Comparison-boolean evaluation: if [RHS] is [true]/[false]
       and [LHS] is a comparison with constant operands, evaluate
       the comparison. Handles [(<= 0 -2) = false], [(< -1 0) =
       true].
    Otherwise reject — there are still classes of cvc5 theory
    rewrites we don't recognize (uninterpreted-function ground
    rewrites, bit-vector evaluation, complex propositional
    simplifications). *)
let check_theory_rewrite_equality
    ?(fragment = "LIA")
    (lhs : Alethe.Sexp.t) (rhs : Alethe.Sexp.t)
  : (unit, string) result =
  match Alethe_farkas.lin_arith lhs, Alethe_farkas.lin_arith rhs with
  | Some la, Some lb when la = lb -> Ok ()
  | _ ->
    (match normalize_literal ~fragment lhs,
           normalize_literal ~fragment rhs with
     | Some ca, Some cb when compiled_equal ca cb -> Ok ()
     | _ ->
       (match evaluate_constant_literal lhs,
              evaluate_constant_literal rhs with
        | Some a, Some b when a = b -> Ok ()
        | Some _, Some _ ->
          Error "constant-boolean sides evaluate to opposite truths"
        | _ ->
          (match rhs with
           | Atom "true" ->
             (match evaluate_comparison_to_bool lhs with
              | Some true -> Ok ()
              | Some false ->
                Error "comparison evaluates to false but rhs is true"
              | None ->
                Error "no rewrite path: not linear-equal, normalized-equal, \
                       constant-bool, or comparison-eval")
           | Atom "false" ->
             (match evaluate_comparison_to_bool lhs with
              | Some false -> Ok ()
              | Some true ->
                Error "comparison evaluates to true but rhs is false"
              | None ->
                Error "no rewrite path: not linear-equal, normalized-equal, \
                       constant-bool, or comparison-eval")
           | _ ->
             Error "no rewrite path: not linear-equal, normalized-equal, \
                    constant-bool, or comparison-eval")))

(** [hole]: cvc5's escape hatch for theory rewrites it doesn't
    spell out fully. The conclusion is a single equality clause
    [(cl (= LHS RHS))], typed by [:args ("TRUST_THEORY_REWRITE"
    ...)]. Sound treatment: ignore the [:args] tag (it's a hint,
    not a proof), and verify the equality independently via
    [check_theory_rewrite_equality]. If we can prove [LHS = RHS]
    by one of the rewrite paths, the step is sound regardless of
    what tag cvc5 used. The IR's fragment threads through to
    enable LIA tightening when normalizing literals. *)
let check_hole (env : env) (step : Alethe.step) : step_result =
  let fragment = Farkas.effective_fragment env.ir in
  match step.clause with
  | [ List [ Atom "="; lhs; rhs ] ] ->
    (match check_theory_rewrite_equality ~fragment lhs rhs with
     | Ok () -> Step_verified
     | Error msg -> Step_failed { rule = "hole"; detail = msg })
  | _ ->
    Step_failed {
      rule = "hole";
      detail = "expected singleton (cl (= LHS RHS))";
    }

(** [rare_rewrite]: same shape as [hole] — a single equality clause
    [(cl (= LHS RHS))] — typed by [:args ("evaluate" ...)] or other
    rewrite-kind tags. Same sound treatment as [hole]: verify the
    equality independently, threading the IR's fragment for LIA
    tightening. The two rules are kept separate (rather than
    aliased) because future cvc5 versions may give them different
    soundness contracts; this leaves room to tighten one without
    affecting the other. *)
let check_rare_rewrite (env : env) (step : Alethe.step) : step_result =
  let fragment = Farkas.effective_fragment env.ir in
  match step.clause with
  | [ List [ Atom "="; lhs; rhs ] ] ->
    (match check_theory_rewrite_equality ~fragment lhs rhs with
     | Ok () -> Step_verified
     | Error msg -> Step_failed { rule = "rare_rewrite"; detail = msg })
  | _ ->
    Step_failed {
      rule = "rare_rewrite";
      detail = "expected singleton (cl (= LHS RHS))";
    }

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
    (match proven_in_scope env step p with
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
    (match proven_in_scope env step p with
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
      (fun id -> Option.is_none (proven_in_scope env step id)) premises
    in
    if unknown <> [] then
      Step_failed {
        rule = "resolution";
        detail = "unknown or out-of-scope premises: "
                 ^ String.concat ", " unknown;
      }
    else
      let premise_lits = List.concat_map
        (fun id -> Option.get (proven_in_scope env step id)) premises
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

(** Multiset equality on clause-literal lists. Clauses are unordered
    disjunctions, so [reordering] / [contraction] / [subproof] need
    multiset-rather-than-list equality on their conclusion checks. *)
let multiset_equal_clauses
    (a : Alethe.Sexp.t list) (b : Alethe.Sexp.t list) : bool =
  let rec subtract a' = function
    | [] -> Some a'
    | x :: rest ->
      (match pop_first x a' with
       | None -> None
       | Some a'' -> subtract a'' rest)
  in
  match subtract a b with
  | Some [] -> true
  | _ -> false

(** [implies_neg1]: tautological clause [(cl (=> A B) A)]. From the
    classical equivalence [(=> A B)] iff [(not A) or B], the
    disjunction [(=> A B) or A] is a tautology (one of the two
    disjuncts must hold). No premises needed; pure shape check. *)
let check_implies_neg1 (step : Alethe.step) : step_result =
  match step.clause with
  | [ List [ Atom "=>"; a; _b ]; a' ] when sexp_equal a a' -> Step_verified
  | _ ->
    Step_failed {
      rule = "implies_neg1";
      detail = "expected (cl (=> A B) A)";
    }

(** [implies_neg2]: tautological clause [(cl (=> A B) (not B))].
    Sibling of [implies_neg1] for the other disjunct: the
    disjunction [(=> A B) or (not B)] is a tautology (under the
    classical reading of implication). *)
let check_implies_neg2 (step : Alethe.step) : step_result =
  match step.clause with
  | [ List [ Atom "=>"; _a; b ]; List [ Atom "not"; b' ] ]
    when sexp_equal b b' -> Step_verified
  | _ ->
    Step_failed {
      rule = "implies_neg2";
      detail = "expected (cl (=> A B) (not B))";
    }

(** [implies_simplify]: rewrite rule with conclusion
    [(cl (= (=> A false) (not A)))]. Encodes the boolean simplification
    that an implication with a [false] consequent is just the
    negation of the antecedent. The single-shape [(=> A false)] is
    what cvc5 actually emits in the case-split fixture. *)
let check_implies_simplify (step : Alethe.step) : step_result =
  match step.clause with
  | [ List [ Atom "=";
             List [ Atom "=>"; a; Atom "false" ];
             List [ Atom "not"; a' ] ] ]
    when sexp_equal a a' -> Step_verified
  | _ ->
    Step_failed {
      rule = "implies_simplify";
      detail = "expected (cl (= (=> A false) (not A)))";
    }

(** [and_pos]: from no premise, conclude [(cl (not (and l_1 … l_n))
    l_i)] where [i] is given in [:args]. Encodes "from a conjunction,
    project a chosen conjunct" as a tautological disjunction. *)
let check_and_pos (step : Alethe.step) : step_result =
  let args = Option.value step.args ~default:[] in
  match args, step.clause with
  | [ Atom idx_str ],
    [ List [ Atom "not"; List (Atom "and" :: conjuncts) ]; l ] ->
    (match int_of_string_opt idx_str with
     | None ->
       Step_failed {
         rule = "and_pos";
         detail = "args[0] is not an integer index";
       }
     | Some i when i >= 0 && i < List.length conjuncts
                && sexp_equal (List.nth conjuncts i) l ->
       Step_verified
     | Some _ ->
       Step_failed {
         rule = "and_pos";
         detail = "args index doesn't match the projected conjunct";
       })
  | _ ->
    Step_failed {
      rule = "and_pos";
      detail = "expected :args (i) and (cl (not (and …)) l_i)";
    }

(** [reordering]: from premise [(cl L_1 … L_n)], conclude any
    permutation of those literals. Pure multiset check — clause
    literals are unordered, so a reordered conclusion is sound iff
    the multisets agree. *)
let check_reordering (env : env) (step : Alethe.step) : step_result =
  let premises = Option.value step.premises ~default:[] in
  match premises with
  | [ p ] ->
    (match proven_in_scope env step p with
     | None ->
       Step_failed {
         rule = "reordering";
         detail = "unknown premise: " ^ p;
       }
     | Some prem_clause ->
       if multiset_equal_clauses prem_clause step.clause then Step_verified
       else
         Step_failed {
           rule = "reordering";
           detail = "conclusion is not a permutation of the premise";
         })
  | _ ->
    Step_failed {
      rule = "reordering";
      detail = "expected exactly one premise";
    }

(** [contraction]: from premise [(cl … L … L …)], conclude
    [(cl … L …)] where any duplicate literals are collapsed.
    Soundness: the conclusion's set of literals equals the
    premise's; the premise has no literal absent from the
    conclusion, and vice versa. *)
let check_contraction (env : env) (step : Alethe.step) : step_result =
  let premises = Option.value step.premises ~default:[] in
  match premises with
  | [ p ] ->
    (match proven_in_scope env step p with
     | None ->
       Step_failed {
         rule = "contraction";
         detail = "unknown premise: " ^ p;
       }
     | Some prem_clause ->
       let prem_set = List.sort_uniq compare prem_clause in
       let concl_set = List.sort_uniq compare step.clause in
       if prem_set = concl_set then Step_verified
       else
         Step_failed {
           rule = "contraction";
           detail = "conclusion's literal set differs from premise's";
         })
  | _ ->
    Step_failed {
      rule = "contraction";
      detail = "expected exactly one premise";
    }

(** [not_and]: from premise [(cl (not (and l_1 … l_n)))], conclude
    [(cl (not l_1) … (not l_n))]. De Morgan's law: the negation of
    a conjunction is the disjunction of negations. *)
let check_not_and (env : env) (step : Alethe.step) : step_result =
  let premises = Option.value step.premises ~default:[] in
  match premises with
  | [ p ] ->
    (match proven_in_scope env step p with
     | None ->
       Step_failed { rule = "not_and"; detail = "unknown premise: " ^ p }
     | Some [ List [ Atom "not"; List (Atom "and" :: conjuncts) ] ] ->
       let expected =
         List.map (fun c -> Alethe.Sexp.List [ Atom "not"; c ]) conjuncts
       in
       if expected = step.clause then Step_verified
       else
         Step_failed {
           rule = "not_and";
           detail = "conclusion's negated literals don't match conjuncts";
         }
     | Some _ ->
       Step_failed {
         rule = "not_and";
         detail = "premise is not (cl (not (and …)))";
       })
  | _ ->
    Step_failed { rule = "not_and"; detail = "expected exactly one premise" }

(** [or]: from premise [(cl (or l_1 … l_n))], conclude
    [(cl l_1 … l_n)]. Strips the [(or)] wrapper from a singleton
    disjunction-as-literal back to its component literals. *)
let check_or (env : env) (step : Alethe.step) : step_result =
  let premises = Option.value step.premises ~default:[] in
  match premises with
  | [ p ] ->
    (match proven_in_scope env step p with
     | None ->
       Step_failed { rule = "or"; detail = "unknown premise: " ^ p }
     | Some [ List (Atom "or" :: disjuncts) ] ->
       if disjuncts = step.clause then Step_verified
       else
         Step_failed {
           rule = "or";
           detail = "conclusion's literals don't match (or …) disjuncts";
         }
     | Some _ ->
       Step_failed { rule = "or"; detail = "premise is not (cl (or …))" })
  | _ ->
    Step_failed { rule = "or"; detail = "expected exactly one premise" }

(** [symm]: from premise [(cl (= a b))], conclude [(cl (= b a))].
    Symmetry of equality. cvc5 emits this when the proof's
    consumer needs the equality oriented the opposite way from
    its derivation. *)
let check_symm (env : env) (step : Alethe.step) : step_result =
  let premises = Option.value step.premises ~default:[] in
  match premises, step.clause with
  | [ p ], [ List [ Atom "="; b'; a' ] ] ->
    (match proven_in_scope env step p with
     | Some [ List [ Atom "="; a; b ] ]
       when sexp_equal a a' && sexp_equal b b' ->
       Step_verified
     | Some _ ->
       Step_failed {
         rule = "symm";
         detail = "premise sides don't match conclusion's flipped sides";
       }
     | None ->
       Step_failed { rule = "symm"; detail = "unknown premise: " ^ p })
  | _ ->
    Step_failed {
      rule = "symm";
      detail = "expected one premise and (cl (= b a)) conclusion";
    }

(** [subproof]: closes an [(anchor :step ID)] block. The body
    derived a clause [C] under local assumptions [A_1 … A_n] (named
    in [:discharge]); the subproof step concludes
    [(cl (not A_1) … (not A_n) C)] — the discharge equivalence.

    Soundness check:
    1. Look up each discharged ID in [env.proven] to recover the
       local-assume atoms.
    2. The body conclusion is the most recently verified step
       (tracked via [env.last_step_clause]) — the step immediately
       preceding this close in input order is always the body's
       last step under cvc5's emission order.
    3. The subproof's clause must match
       [(not A_i)…] ++ body_clause as a multiset.

    On success we also strip the inner-scope assumes and steps
    (anything whose ID has [step.id ^ "."] as a prefix) from
    [env.proven] so an outer step can't accidentally reference a
    discharged local fact as if it were globally proven. *)
let check_subproof (env : env) (step : Alethe.step) : step_result =
  let discharge = Option.value step.discharge ~default:[] in
  if discharge = [] then
    Step_failed { rule = "subproof"; detail = "no :discharge list" }
  else
    (* Subproof close [step.id = T] discharges assumes whose
       enclosing subproof is exactly [T] — i.e., assumes parsed
       inside [(anchor :step T)] before any further nested anchor.
       The general [proven_in_scope] check would reject these
       since [step.id = T] doesn't itself sit inside subproof [T];
       this lookup applies the close-step-specific scope rule. *)
    let lookup_atom id =
      match Alethe.enclosing_subproof_id id with
      | Some encl when String.equal encl step.id ->
        (match Hashtbl.find_opt env.proven id with
         | Some [ atom ] -> Ok atom
         | Some _ ->
           Error ("discharged id " ^ id ^ " is not a singleton clause")
         | None -> Error ("unknown discharged assume: " ^ id))
      | _ ->
        Error ("discharged id " ^ id
               ^ " is not local to this subproof's immediate body")
    in
    let rec collect_atoms acc = function
      | [] -> Ok (List.rev acc)
      | id :: rest ->
        (match lookup_atom id with
         | Ok atom -> collect_atoms (atom :: acc) rest
         | Error msg -> Error msg)
    in
    match collect_atoms [] discharge with
    | Error msg -> Step_failed { rule = "subproof"; detail = msg }
    | Ok atoms ->
      (* The body conclusion is the step immediately preceding the
         close. It must live directly inside subproof [step.id] —
         i.e., its enclosing-subproof id is exactly [step.id]. A
         body conclusion with a deeper enclosing scope means a
         nested subproof was never closed, so the close-step would
         be lifting a clause derived under unsealed nested-local
         assumptions. *)
      let direct_child = match env.last_step_id with
        | None -> false
        | Some sid ->
          (match Alethe.enclosing_subproof_id sid with
           | Some encl -> String.equal encl step.id
           | None -> false)
      in
      if not direct_child then
        Step_failed {
          rule = "subproof";
          detail = "body conclusion is not a direct child of the \
                    subproof being closed";
        }
      else
      (match env.last_step_clause with
       | None ->
         Step_failed {
           rule = "subproof";
           detail = "no preceding body conclusion";
         }
       | Some body_concl ->
         let expected =
           List.map (fun a -> Alethe.Sexp.List [ Atom "not"; a ]) atoms
           @ body_concl
         in
         if not (multiset_equal_clauses expected step.clause) then
           Step_failed {
             rule = "subproof";
             detail = "conclusion is not (not A_i)… ++ body_clause";
           }
         else
           (* Dependency check: every same-scope local assume the
              body actually used must appear in [:discharge].
              Without this an undisclosed local assume (e.g.
              [t1.bad: false]) consumed by the body would leak
              into the close's clause as if it didn't exist —
              the close would lift only the [:discharge]'d
              assumes and silently drop the rest, producing an
              unsound exported clause. *)
           let body_id = Option.get env.last_step_id in
           let body_deps =
             match Hashtbl.find_opt env.deps body_id with
             | Some s -> s
             | None -> StringSet.empty
           in
           let local_T_used =
             StringSet.filter (fun id ->
               match Alethe.enclosing_subproof_id id with
               | Some encl -> String.equal encl step.id
               | None -> false) body_deps
           in
           let discharge_set = StringSet.of_list discharge in
           let undisclosed = StringSet.diff local_T_used discharge_set in
           if not (StringSet.is_empty undisclosed) then
             Step_failed {
               rule = "subproof";
               detail = Printf.sprintf
                 "body depends on local assume %s but it's not in \
                  :discharge"
                 (StringSet.choose undisclosed);
             }
           else begin
             let inner_prefix = step.id ^ "." in
             let plen = String.length inner_prefix in
             let prefixed k =
               String.length k > plen
               && String.sub k 0 plen = inner_prefix
             in
             let drop_proven =
               Hashtbl.fold (fun k _ acc ->
                 if prefixed k then k :: acc else acc) env.proven []
             in
             let drop_assumes =
               Hashtbl.fold (fun k _ acc ->
                 if prefixed k then k :: acc else acc) env.assumes []
             in
             let drop_deps =
               Hashtbl.fold (fun k _ acc ->
                 if prefixed k then k :: acc else acc) env.deps []
             in
             List.iter (Hashtbl.remove env.proven) drop_proven;
             List.iter (Hashtbl.remove env.assumes) drop_assumes;
             List.iter (Hashtbl.remove env.deps) drop_deps;
             Step_verified
           end)

(** Top-level rule dispatch. Add a new clause here when wiring an
    OCaml-side checker for another Alethe rule, and add the same
    rule name to [supported_rules] below. The walker treats
    [Step_unsupported_rule _] as the bailout — Tier 3 verification
    fails when any step uses a rule no checker handles. *)
let check_step (env : env) (step : Alethe.step) : step_result =
  match step.rule with
  | "la_generic" -> check_la_generic env step
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
  | "hole" -> check_hole env step
  | "rare_rewrite" -> check_rare_rewrite env step
  | "implies_neg1" -> check_implies_neg1 step
  | "implies_neg2" -> check_implies_neg2 step
  | "implies_simplify" -> check_implies_simplify step
  | "and_pos" -> check_and_pos step
  | "reordering" -> check_reordering env step
  | "contraction" -> check_contraction env step
  | "not_and" -> check_not_and env step
  | "or" -> check_or env step
  | "symm" -> check_symm env step
  | "subproof" -> check_subproof env step
  | other -> Step_unsupported_rule other

(** Sorted list of every Alethe rule [check_step] has a registered
    checker for. Must stay in sync with the [check_step] match
    above; [test_supported_rules_sync] in [test_tier3_alethe]
    pins this. The cvc5 minter consults this set to decide whether
    a parsed proof is eligible for Tier 3 minting (the "fail
    closed" gate of direction 3). *)
let supported_rules : string list = [
  "and_neg"; "and_pos"; "cong"; "contraction"; "equiv1";
  "equiv_pos2"; "equiv_simplify"; "false"; "hole"; "implies";
  "implies_neg1"; "implies_neg2"; "implies_simplify";
  "la_generic"; "la_mult_neg"; "not_and"; "or"; "rare_rewrite";
  "refl"; "reordering"; "resolution"; "subproof"; "symm"; "trans";
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

(** Verify a parsed Tier 3 alethe-2024 proof end-to-end against
    [ir]. Walks every step in input order, threading an [env]
    populated with the assumes' atoms (as singleton clauses) and
    each verified step's clause so stateful rules ([trans], [cong],
    [resolution]) can look up premises. Returns on the first
    unsupported-rule or step-failure. After all steps pass,
    requires the final step's clause to be terminal ([(cl)] or
    [(cl false)]) — otherwise the proof verified locally but
    didn't reach the bottom derivation, and we surface that as a
    [Step_failed] on the final step.

    Exposes the parsed-proof entry point so the cvc5 minter can
    re-use one [Alethe.parse] result for the gate check and the
    payload construction (rather than parsing twice). *)
let verify_parsed (ir : Ir.t) (p : Alethe.proof) : verify_result =
  match validate_anchor_structure
          ~anchors:p.anchors ~assumes:p.assumes ~steps:p.steps with
  | Error msg ->
    Step_failed { step_id = ""; rule = "<anchor>"; detail = msg }
  | Ok () ->
  match validate_top_level_assumes ir p.assumes with
  | Error msg ->
    Step_failed { step_id = ""; rule = "<assume>"; detail = msg }
  | Ok () ->
  let env = {
    ir;
    proven = Hashtbl.create 32;
    assumes = Hashtbl.create 8;
    deps = Hashtbl.create 32;
    last_step_clause = None;
    last_step_id = None;
    last_la_generic_consumed = None;
  } in
  (* Seed env with assumes. Top-level assumes (no dot in ID) are
     globally in scope — we've just validated they match an IR
     fact. Subproof-local assumes (dotted ID) are also seeded
     (the parser collected them all), but [proven_in_scope] /
     [local_assume_atoms] gate every lookup by the step's ID
     prefix, so a step in subproof T cannot see assumes from
     sibling subproof U even though both are in [env.assumes].
     [check_subproof] additionally strips inner-scope entries
     after discharge, so an outer step run after the close gets
     a clean env.

     Each assume seeds a singleton [{id}] dependency set. Any
     step that looks the assume up via a premise inherits that
     ID into its own deps set; a [subproof] close subtracts the
     [:discharge] set from the body's deps, sealing the
     discharged assumes. *)
  List.iter (fun (id, atom) ->
    Hashtbl.replace env.proven id [ atom ];
    Hashtbl.replace env.assumes id atom;
    Hashtbl.replace env.deps id (StringSet.singleton id))
    p.assumes;
  let rec walk = function
    | [] ->
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
         (* Compute and record this step's dependency set.

            Most rules cite premises in [step.premises] and the
            step's deps are simply the union of those premises'
            deps (already in [env.deps]; for an assume cited as
            a premise this is its singleton [{id}]).

            [la_generic] doesn't surface premises in
            [step.premises]; [check_la_generic] stashes the
            consumed local-assume IDs into
            [env.last_la_generic_consumed] and we fold them in.

            [subproof] close has special semantics: the close
            seals the discharged assumes, so its deps are the
            body's deps minus the [:discharge] set. The body
            here is whichever step the close listed as
            [last_step_id]. *)
         let union_premise_deps () =
           let prems = Option.value step.premises ~default:[] in
           List.fold_left (fun acc id ->
             match Hashtbl.find_opt env.deps id with
             | Some s -> StringSet.union acc s
             | None -> acc)
             StringSet.empty prems
         in
         let step_deps =
           match step.rule with
           | "subproof" ->
             let body_id = Option.value env.last_step_id ~default:"" in
             let body_deps =
               match Hashtbl.find_opt env.deps body_id with
               | Some s -> s | None -> StringSet.empty
             in
             let discharge_set = StringSet.of_list
                                   (Option.value step.discharge ~default:[]) in
             StringSet.diff body_deps discharge_set
           | "la_generic" ->
             let consumed =
               Option.value env.last_la_generic_consumed
                 ~default:StringSet.empty
             in
             env.last_la_generic_consumed <- None;
             (* Each consumed name is an in-scope local assume,
                already seeded with singleton deps in env.deps. *)
             StringSet.fold (fun id acc ->
               match Hashtbl.find_opt env.deps id with
               | Some s -> StringSet.union acc s
               | None -> StringSet.add id acc) consumed StringSet.empty
           | _ -> union_premise_deps ()
         in
         Hashtbl.replace env.deps step.id step_deps;
         env.last_step_clause <- Some step.clause;
         env.last_step_id <- Some step.id;
         walk rest
       | Step_unsupported_rule rule ->
         Unsupported_rule { rule; step_id = step.id }
       | Step_failed { rule; detail } ->
         Step_failed { step_id = step.id; rule; detail })
  in
  walk p.steps

(** Top-level [verify]: parses [proof_str] then dispatches to
    [verify_parsed]. A parse error surfaces as a [Step_failed]
    with [step_id = ""] and [rule = "<parse>"] so callers don't
    need a third failure arm. *)
let verify (ir : Ir.t) (proof_str : string) : verify_result =
  match Alethe.parse proof_str with
  | exception Alethe.Parse_error msg ->
    Step_failed { step_id = ""; rule = "<parse>"; detail = msg }
  | p -> verify_parsed ir p

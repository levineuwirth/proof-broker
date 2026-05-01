(** Extract a Tier 1 Farkas witness from a cvc5 Alethe proof.

    cvc5 closes a linear-arithmetic goal with a single [la_generic]
    step whose [:args] are rational coefficients and whose clause
    literals encode the inequalities being summed. Verifying that
    those inequalities are exactly the IR's hypotheses (plus the
    negated goal) reduces the problem to:

    1. Locate the unique [la_generic] step.
    2. For each clause literal, compile its negation as a
       [Farkas.compiled] form (an [Le], [Lt], or [Eq] linear form).
    3. Compile each IR hypothesis and the negated goal the same way
       via [Farkas.compile_hypothesis].
    4. Match each cvc5 form to an IR input by linear-form equality
       under positive scaling.
    5. Emit the matched [(hypothesis_name, coefficient)] list as a
       JSON witness consumable by [Farkas.verify].

    Scope. We support both LRA and LIA. For LRA we match each
    cvc5 clause literal by structural scaling against an IR input.
    For LIA, cvc5 may tighten loose inequalities ([<= x 1] becomes
    [< x 2]) before forming the la_generic step; we mirror the IR
    side's "+1 trick" by rewriting any [Lt(f)] cvc5 literal to
    [Le(f + 1)] before matching, which is equivalent over the
    integers and aligns with what [Farkas.compile_hypothesis] does
    on the IR side under LIA. The only literals we drop are
    pure-constant residues introduced by la_generic's
    normalization. *)

module L = Linear_arith
module S = Alethe.Sexp

(* --- linearization on Alethe S-expressions --------------------------- *)

(** Linearize an arithmetic term. Recognizes SMT-LIB n-ary [+], [*],
    [-] (both binary and unary), numeric literals (incl. rationals
    like [3/4] and negatives like [-5]), and variables. Returns
    [None] on any non-linear shape — multiplication with two
    non-constant factors, an unknown function symbol, or a
    parse-failed numeric atom. *)
let rec lin_arith (s : S.t) : L.t option =
  match s with
  | S.Atom name ->
    (match L.rat_of_string name with
     | Some r -> Some (L.const r)
     | None -> Some (L.var name))
  | S.List (S.Atom "+" :: args) ->
    fold_sum L.zero args
  | S.List (S.Atom "-" :: [ a ]) ->
    (match lin_arith a with
     | Some la -> Some (L.neg la)
     | None -> None)
  | S.List (S.Atom "-" :: a :: rest) ->
    (match lin_arith a with
     | Some la -> fold_diff la rest
     | None -> None)
  | S.List (S.Atom "*" :: args) ->
    fold_product L.rat_one None args
  | _ -> None

and fold_sum acc = function
  | [] -> Some acc
  | x :: rest ->
    (match lin_arith x with
     | Some lx -> fold_sum (L.add acc lx) rest
     | None -> None)

and fold_diff acc = function
  | [] -> Some acc
  | x :: rest ->
    (match lin_arith x with
     | Some lx -> fold_diff (L.sub acc lx) rest
     | None -> None)

(** Fold an n-ary multiplication node. We track an accumulated
    constant factor [k] and an optional variable part [vp]; if a
    second non-constant factor appears the term is non-linear. *)
and fold_product k vp = function
  | [] ->
    (match vp with
     | Some f -> Some (L.scale k f)
     | None -> Some (L.const k))
  | x :: rest ->
    (match lin_arith x with
     | None -> None
     | Some lx when L.is_constant lx ->
       fold_product (L.rat_mul k (L.constant_value lx)) vp rest
     | Some lx ->
       (match vp with
        | None -> fold_product k (Some lx) rest
        | Some _ -> None))

(* --- atom compilation ------------------------------------------------- *)

(** Compile a positive atom into a [Farkas.compiled] form. *)
let compile_atom_pos (s : S.t) : Farkas.compiled option =
  let from_le a b =
    match lin_arith a, lin_arith b with
    | Some la, Some lb -> Some (Farkas.Le (L.sub la lb))
    | _ -> None
  in
  let from_lt a b =
    match lin_arith a, lin_arith b with
    | Some la, Some lb -> Some (Farkas.Lt (L.sub la lb))
    | _ -> None
  in
  let from_eq a b =
    match lin_arith a, lin_arith b with
    | Some la, Some lb -> Some (Farkas.Eq (L.sub la lb))
    | _ -> None
  in
  match s with
  | S.List [ S.Atom "<="; a; b ] -> from_le a b
  | S.List [ S.Atom "<";  a; b ] -> from_lt a b
  | S.List [ S.Atom ">="; a; b ] -> from_le b a
  | S.List [ S.Atom ">";  a; b ] -> from_lt b a
  | S.List [ S.Atom "=";  a; b ] -> from_eq a b
  | _ -> None

(** Negate a compiled form: [¬(f ≤ 0) ≡ -f < 0] and so on. Returns
    [None] for [Eq], since the negation of an equality is not a
    single Farkas-amenable inequality and we never need it for
    [la_generic] clauses. *)
let neg_compiled = function
  | Farkas.Le f -> Some (Farkas.Lt (L.neg f))
  | Farkas.Lt f -> Some (Farkas.Le (L.neg f))
  | Farkas.Eq _ -> None

(** Apply the integer +1 trick: over Z, [f < 0] is equivalent to
    [f + 1 ≤ 0]. We use this to fold cvc5's tightened strict
    literals back into a loose form that matches the IR side
    (where [Farkas.compile_hypothesis] already applies the same
    trick under LIA). For LRA we leave [Lt] alone. *)
let lia_normalize (c : Farkas.compiled) : Farkas.compiled =
  match c with
  | Farkas.Lt f -> Farkas.Le (L.add f (L.const L.rat_one))
  | _ -> c

(** Compile the *negation* of a clause literal. The la_generic
    rule's conjunction is [¬L1 ∧ ... ∧ ¬Ln]; we want the linear
    form of each conjunct.

    A literal of shape [(not P)] contributes [P] to the conjunction
    directly; otherwise we negate. The result is then normalized
    according to [fragment]: under any non-LRA fragment (notably
    [LIA]), strict [Lt] forms are folded to [Le(f+1)]. *)
let compile_neg_literal ?(fragment = "LRA") (lit : S.t)
  : Farkas.compiled option =
  let raw =
    match lit with
    | S.List [ S.Atom "not"; inner ] -> compile_atom_pos inner
    | _ ->
      (match compile_atom_pos lit with
       | Some c -> neg_compiled c
       | None -> None)
  in
  match raw with
  | None -> None
  | Some c when String.equal fragment "LRA" -> Some c
  | Some c -> Some (lia_normalize c)

(* --- scalar-multiple matching ---------------------------------------- *)

(** Multiplicative inverse of a rational. *)
let rat_inv (r : L.rational) : L.rational =
  if r.num = 0 then invalid_arg "Alethe_farkas.rat_inv: zero"
  else L.mk_rat r.den r.num

(** Find the rational [r] such that [f1 = r * f2], or [None] when
    no such [r] exists. The canonical form of [Linear_arith.t]
    (sorted assoc list, no zero entries) makes this a straight
    pivot-and-verify check. *)
let scale_factor (f1 : L.t) (f2 : L.t) : L.rational option =
  match f2.coeffs, f1.coeffs with
  | [], [] ->
    (* Both pure constants. Special cases: 0 = r*0 for any r (we
       pick 1); 0 = r*c with c≠0 means r=0; otherwise r = c1/c2. *)
    if L.rat_is_zero f2.const then
      if L.rat_is_zero f1.const then Some L.rat_one else None
    else if L.rat_is_zero f1.const then Some L.rat_zero
    else Some (L.rat_mul f1.const (rat_inv f2.const))
  | [], _ :: _ ->
    (* f2 is constant, f1 has variables — not a scalar multiple. *)
    None
  | (n2, c2) :: _, _ ->
    (match List.assoc_opt n2 f1.coeffs with
     | None -> None
     | Some c1 ->
       let r = L.rat_mul c1 (rat_inv c2) in
       if L.scale r f2 = f1 then Some r else None)

(** Match a compiled form from cvc5 against one from the IR. Both
    must be the same shape ([Le], [Lt], or [Eq]) and the IR linear
    form must scale by some [r] to the cvc5 form: positive [r] for
    inequalities, any nonzero [r] for equalities. Returns the scale
    factor used, or [None] on no match. *)
let match_shape ~from_cvc5 ~from_ir : L.rational option =
  match from_cvc5, from_ir with
  | Farkas.Le c, Farkas.Le d
  | Farkas.Lt c, Farkas.Lt d ->
    (match scale_factor c d with
     | Some r when L.rat_is_pos r -> Some r
     | _ -> None)
  | Farkas.Eq c, Farkas.Eq d ->
    (match scale_factor c d with
     | Some r when not (L.rat_is_zero r) -> Some r
     | _ -> None)
  | _ -> None

(* --- IR input compilation --------------------------------------------- *)

type input_entry = {
  name : string;
  compiled : Farkas.compiled;
}

(** Compile every IR hypothesis plus the synthetic [neg_goal] entry,
    using [Farkas.compile_hypothesis] under the IR's declared
    fragment. Hypotheses that fail to compile (non-linear, unsupported
    shape) are simply dropped — they can't participate in a Farkas
    sum anyway, and the caller will fail gracefully if a clause
    literal wants them. *)
let compile_ir_inputs (ir : Ir.t) : input_entry list =
  let fragment = ir.logic_classification.first_order_fragment in
  let one (name, shell) =
    match Farkas.compile_hypothesis ~fragment shell with
    | Ok c -> Some { name; compiled = c }
    | Error _ -> None
  in
  let from_hyps =
    List.filter_map (fun (h : Ir.hypothesis) -> one (h.name, h.shell))
      ir.context.hypotheses
  in
  let neg_goal_shell = Ir.Not { operand = ir.goal.shell } in
  match one ("neg_goal", neg_goal_shell) with
  | Some e -> from_hyps @ [ e ]
  | None -> from_hyps

(* --- top-level extraction --------------------------------------------- *)

type error =
  | No_la_generic
  | Coefficient_count_mismatch of { args : int; literals : int }
  | Bad_coefficient of { raw : string }
  | Unrecognized_literal of { sexp : string }
  | Unmatched_literal of { sexp : string; compiled : string }

let error_kind = function
  | No_la_generic -> "no_la_generic"
  | Coefficient_count_mismatch _ -> "coefficient_count_mismatch"
  | Bad_coefficient _ -> "bad_coefficient"
  | Unrecognized_literal _ -> "unrecognized_literal"
  | Unmatched_literal _ -> "unmatched_literal"

let error_detail = function
  | No_la_generic -> "no la_generic step in proof"
  | Coefficient_count_mismatch { args; literals } ->
    Printf.sprintf "la_generic has %d args but %d clause literals"
      args literals
  | Bad_coefficient { raw } -> "could not parse coefficient: " ^ raw
  | Unrecognized_literal { sexp } -> "could not linearize: " ^ sexp
  | Unmatched_literal { sexp; compiled } ->
    Printf.sprintf "no IR input matches clause literal %s (compiled %s)"
      sexp compiled

let compiled_to_string = function
  | Farkas.Le f -> "Le(" ^ L.to_string f ^ ")"
  | Farkas.Lt f -> "Lt(" ^ L.to_string f ^ ")"
  | Farkas.Eq f -> "Eq(" ^ L.to_string f ^ ")"

(** Tell whether a compiled form is a pure constant (no variable
    coefficients) — then the literal is a la_generic residue and
    contributes nothing to the matched witness. *)
let is_constant_form = function
  | Farkas.Le f | Farkas.Lt f | Farkas.Eq f -> f.coeffs = []

(** Try to match one cvc5 clause literal against the IR inputs.
    Returns [(input_name, scale_factor)] on success, [None] when
    the literal is a pure-constant residue, or [Error _] on a
    matching failure. *)
let match_one ~fragment (lit : S.t) (inputs : input_entry list)
  : ((string * L.rational) option, error) result =
  match compile_neg_literal ~fragment lit with
  | None ->
    Error (Unrecognized_literal { sexp = S.to_string lit })
  | Some c when is_constant_form c -> Ok None
  | Some c ->
    let rec find = function
      | [] ->
        Error (Unmatched_literal {
          sexp = S.to_string lit;
          compiled = compiled_to_string c;
        })
      | e :: rest ->
        (match match_shape ~from_cvc5:c ~from_ir:e.compiled with
         | Some r -> Ok (Some (e.name, r))
         | None -> find rest)
    in
    find inputs

(** Walk a single la_generic step's clause+args, matching each
    literal against [inputs] and accumulating the witness pairs.
    Factored so case-split extraction can supply augmented inputs
    (the disjunctive case as an extra entry). *)
let extract_from_step
    ~fragment ~(inputs : input_entry list) (step : Alethe.step)
  : ((string * L.rational) list, error) result =
  let args = Option.value step.args ~default:[] in
  if List.length args <> List.length step.clause then
    Error (Coefficient_count_mismatch {
      args = List.length args;
      literals = List.length step.clause;
    })
  else
    let rec walk acc = function
      | [], [] -> Ok (List.rev acc)
      | lit :: lits, arg :: args' ->
        let raw = match arg with
          | S.Atom s -> s
          | s -> S.to_string s
        in
        (match L.rat_of_string raw with
         | None -> Error (Bad_coefficient { raw })
         | Some k ->
           (match match_one ~fragment lit inputs with
            | Error e -> Error e
            | Ok None -> walk acc (lits, args')
            | Ok (Some (name, r)) ->
              let coef = L.rat_mul k r in
              walk ((name, coef) :: acc) (lits, args')))
      | _ -> Error No_la_generic  (* unreachable: lengths checked *)
    in
    walk [] (step.clause, args)

(** Pair clause literals with [:args] coefficients, parse each
    coefficient as a rational, and produce the matched witness. The
    [:args] list must have the same length as [clause]; that's an
    Alethe-level invariant on [la_generic]. *)
let extract_witness (ir : Ir.t) (proof : Alethe.proof)
  : ((string * L.rational) list, error) result =
  match Alethe.unique_la_generic proof with
  | None -> Error No_la_generic
  | Some step ->
    let fragment = ir.logic_classification.first_order_fragment in
    let inputs = compile_ir_inputs ir in
    extract_from_step ~fragment ~inputs step

(** Combine duplicate hypothesis names (same name appearing twice
    in the witness, e.g. if cvc5 split the same input across two
    clause literals): sum the coefficients. Preserves first-seen
    order. *)
let dedupe (entries : (string * L.rational) list)
  : (string * L.rational) list =
  let order = ref [] in
  let table : (string, L.rational) Hashtbl.t = Hashtbl.create 8 in
  List.iter (fun (n, r) ->
    match Hashtbl.find_opt table n with
    | Some r' -> Hashtbl.replace table n (L.rat_add r' r)
    | None ->
      Hashtbl.add table n r;
      order := n :: !order) entries;
  List.rev_map (fun n -> (n, Hashtbl.find table n)) !order

(** Encode a deduplicated witness as the JSON shape expected by
    [Farkas.verify]: [{coefficients: [{hypothesis, coefficient},
    ...]}]. Drops any zero-coefficient entries for cleanliness. *)
let witness_to_json (entries : (string * L.rational) list)
  : Yojson.Safe.t =
  let items = List.filter_map (fun (n, r) ->
    if L.rat_is_zero r then None
    else Some (`Assoc [
      "hypothesis", `String n;
      "coefficient", `String (L.rat_to_string r);
    ])) entries in
  `Assoc [ "coefficients", `List items ]

(** End-to-end: parse the Alethe proof string, find la_generic,
    match its literals against the IR, and produce the witness JSON.
    Returns [Error _] on any extraction failure; the caller should
    fall back to a Tier 0 oracle cert in that case. *)
let extract (ir : Ir.t) (proof_str : string)
  : (Yojson.Safe.t, error) result =
  let proof =
    try Ok (Alethe.parse proof_str)
    with Alethe.Parse_error msg ->
      Error (Unrecognized_literal { sexp = "parse error: " ^ msg })
  in
  match proof with
  | Error e -> Error e
  | Ok p ->
    (match extract_witness ir p with
     | Error e -> Error e
     | Ok entries -> Ok (witness_to_json (dedupe entries)))

(* --- case-split (Tier 2) extraction ---------------------------------- *)

(** Flatten [Or { left; right }] into a flat disjunct list. *)
let rec disjuncts_of (s : Ir.shell_term) : Ir.shell_term list =
  match s with
  | Or { left; right } -> disjuncts_of left @ disjuncts_of right
  | _ -> [ s ]

type disjunctive_target = {
  hyp_name : string;
  disjuncts : Ir.shell_term list;
  compiled_disjuncts : Farkas.compiled list;
}

(** Find an IR hypothesis that is a disjunction of linear atoms.
    Returns the unique target if exactly one such hypothesis exists
    and every disjunct compiles cleanly; otherwise [None]. We only
    handle a single disjunctive hypothesis per case-split cert —
    multiple disjunctive hyps are out of scope and fall back to
    Tier 0. *)
let unique_disjunctive_target ~fragment (ir : Ir.t)
  : disjunctive_target option =
  let candidates =
    List.filter_map (fun (h : Ir.hypothesis) ->
      match h.shell with
      | Or _ ->
        let ds = disjuncts_of h.shell in
        let cs = List.map (Farkas.compile_hypothesis ~fragment) ds in
        if List.for_all (function Ok _ -> true | _ -> false) cs then
          Some {
            hyp_name = h.name;
            disjuncts = ds;
            compiled_disjuncts =
              List.map (function Ok c -> c | _ -> assert false) cs;
          }
        else None
      | _ -> None) ir.context.hypotheses
  in
  match candidates with
  | [ t ] -> Some t
  | _ -> None

(** Compile a positive Alethe atom to a [Farkas.compiled] form,
    applying the LIA +1 trick for tightened strict literals so the
    result aligns with what [Farkas.compile_hypothesis] produces on
    the IR side. *)
let compile_assume_atom ~fragment (atom : S.t) : Farkas.compiled option =
  match compile_atom_pos atom with
  | None -> None
  | Some c when String.equal fragment "LRA" -> Some c
  | Some c -> Some (lia_normalize c)

(** Among the local assumes of [subproof_step], find the one that
    matches a disjunct of [target]. Returns the matched disjunct's
    IR shell (so the caller can record it as the "case") and the
    matched index, or [None] if no local assume matches any
    disjunct. *)
let identify_subproof_case
    ~fragment (proof : Alethe.proof) (target : disjunctive_target)
    (subproof_step : Alethe.step)
  : (Ir.shell_term * int) option =
  match subproof_step.discharge with
  | None -> None
  | Some ids ->
    let try_one assume_id =
      match Alethe.assume_atom proof assume_id with
      | None -> None
      | Some atom ->
        (match compile_assume_atom ~fragment atom with
         | None -> None
         | Some c ->
           let rec find i = function
             | [] -> None
             | d :: rest ->
               (match match_shape ~from_cvc5:c ~from_ir:d with
                | Some _ -> Some i
                | None -> find (i + 1) rest)
           in
           (match find 0 target.compiled_disjuncts with
            | Some i -> Some (List.nth target.disjuncts i, i)
            | None -> None))
    in
    let rec scan = function
      | [] -> None
      | a :: rest ->
        (match try_one a with
         | Some hit -> Some hit
         | None -> scan rest)
    in
    scan ids

(** Locate the la_generic step inside [subproof_step]'s body. *)
let la_generic_in_subproof (proof : Alethe.proof) (subproof_step : Alethe.step)
  : Alethe.step option =
  let inner = Alethe.steps_in_subproof proof subproof_step.id in
  match List.filter (fun (s : Alethe.step) -> s.rule = "la_generic") inner with
  | [ s ] -> Some s
  | _ -> None

type case_lemma = {
  case : Ir.shell_term;
  witness : Yojson.Safe.t;
}

type case_split_result = {
  disjunctive_hyp : string;
  lemmas : case_lemma list;
}

(** Extract a case-split (Tier 2) witness. Requires exactly one
    disjunctive IR hypothesis with linear-atom disjuncts, and a
    matching set of subproofs each closing one disjunct via
    la_generic. Cases must collectively cover every disjunct
    (no duplicates, no gaps). *)
let extract_case_split (ir : Ir.t) (proof : Alethe.proof)
  : (case_split_result, error) result =
  let fragment = ir.logic_classification.first_order_fragment in
  match unique_disjunctive_target ~fragment ir with
  | None -> Error No_la_generic
  | Some target ->
    let close_steps = Alethe.subproof_close_steps proof in
    let n_disjuncts = List.length target.disjuncts in
    if List.length close_steps <> n_disjuncts then
      Error No_la_generic
    else
      let base_inputs = compile_ir_inputs ir in
      let rec each_subproof acc seen = function
        | [] ->
          if List.length acc = n_disjuncts
             && List.length seen = n_disjuncts
          then Ok { disjunctive_hyp = target.hyp_name;
                    lemmas = List.rev acc }
          else Error No_la_generic
        | (sp : Alethe.step) :: rest ->
          (match la_generic_in_subproof proof sp with
           | None -> Error No_la_generic
           | Some la ->
             match identify_subproof_case ~fragment proof target sp with
             | None -> Error No_la_generic
             | Some (case_shell, idx) ->
               if List.mem idx seen then Error No_la_generic
               else
                 let case_compiled =
                   match Farkas.compile_hypothesis ~fragment case_shell with
                   | Ok c -> c
                   | Error _ -> assert false
                 in
                 let inputs =
                   base_inputs @ [ { name = "case"; compiled = case_compiled } ]
                 in
                 (match extract_from_step ~fragment ~inputs la with
                  | Error e -> Error e
                  | Ok entries ->
                    let witness = witness_to_json (dedupe entries) in
                    each_subproof
                      ({ case = case_shell; witness } :: acc)
                      (idx :: seen)
                      rest))
      in
      each_subproof [] [] close_steps

(** Encode a case-split extraction as a Tier 2 [lemmas_used] list:
    each lemma is [{"case": <shell>, "witness": <farkas>}]. The
    structural_hint tells the verifier which IR hypothesis to
    expect the cases to partition. *)
let case_split_to_lemmas (r : case_split_result) : Yojson.Safe.t list =
  List.map (fun (l : case_lemma) ->
    `Assoc [
      "case", Codec.shell_to_json l.case;
      "witness", l.witness;
    ]) r.lemmas

(** End-to-end Tier 2 extraction: parse + try case-split. Returns
    the lemma list and the disjunctive-hypothesis name for use in
    [Tier2_lemma_list]'s [structural_hint]. *)
let extract_case_split_payload (ir : Ir.t) (proof_str : string)
  : (Yojson.Safe.t list * string, error) result =
  let proof =
    try Ok (Alethe.parse proof_str)
    with Alethe.Parse_error msg ->
      Error (Unrecognized_literal { sexp = "parse error: " ^ msg })
  in
  match proof with
  | Error e -> Error e
  | Ok p ->
    (match extract_case_split ir p with
     | Error e -> Error e
     | Ok r -> Ok (case_split_to_lemmas r, r.disjunctive_hyp))

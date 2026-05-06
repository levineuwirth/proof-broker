(** Extract a Tier 1 Farkas witness from a z3 proof.

    z3 closes a linear-arithmetic goal by emitting a Farkas-flavored
    th-lemma — [(_ th-lemma arith farkas C1 C2 ... Cn)] — whose
    coefficients are positional indices on the rule head and whose
    clause is [(or (not L1) (not L2) ... (not Ln))]. The Farkas
    tautology asserts that [L1 ∧ L2 ∧ ... ∧ Ln] is unsat, with
    [c_i] as the positive multiplier for [L_i] in the inconsistent
    sum.

    Verifying that those literals are exactly the IR's hypotheses
    (plus the negated goal) reduces the problem to:

    1. Locate the root Farkas-flavored th-lemma application via
       [Z3_proof.find_farkas_clause].
    2. For each clause literal, compile the (positive) atom [L_i]
       to a [Farkas.compiled] form.
    3. Compile each IR hypothesis and the negated goal the same
       way via [Farkas.compile_hypothesis].
    4. Match each z3 literal to an IR input by linear-form
       equality under positive scaling.
    5. Multiply the z3 coefficient by the scale factor and emit
       the matched [(hypothesis_name, coefficient)] list as a JSON
       witness consumable by [Farkas.verify].

    Scope mirrors [Alethe_farkas]: LRA and LIA both supported,
    with the LIA +1 trick applied inside [Farkas.compile_hypothesis]
    and a matching adjustment in [Alethe_farkas.compile_neg_literal]
    (which we reuse — z3's clause disjuncts are [(not L_i)] so the
    same negation logic applies). *)

module L = Linear_arith
module S = Alethe.Sexp

(* --- error taxonomy --------------------------------------------------- *)

type error =
  | No_envelope
  | No_farkas_clause
  | Unrecognized_literal of { sexp : string }
  | Unmatched_literal of { sexp : string; compiled : string }

let error_kind = function
  | No_envelope -> "no_envelope"
  | No_farkas_clause -> "no_farkas_clause"
  | Unrecognized_literal _ -> "unrecognized_literal"
  | Unmatched_literal _ -> "unmatched_literal"

let error_detail = function
  | No_envelope -> "could not parse z3 proof envelope"
  | No_farkas_clause ->
    "no Farkas-flavored th-lemma in proof (likely opaque arith form)"
  | Unrecognized_literal { sexp } -> "could not linearize: " ^ sexp
  | Unmatched_literal { sexp; compiled } ->
    Printf.sprintf "no IR input matches clause literal %s (compiled %s)"
      sexp compiled

(* --- alignment -------------------------------------------------------- *)

(** Match one (literal, z3-coefficient) pair to an IR input, scaling
    z3's coefficient by the literal-vs-input scale factor. We reuse
    [Alethe_farkas.match_one] by wrapping the (positive) z3 literal
    in [(not L)] — that is exactly the form [match_one] expects for a
    clause disjunct, and its negation handling produces the right
    Farkas-compiled form for L. *)
let align_one
    ~(fragment : string)
    ~(inputs : Alethe_farkas.input_entry list)
    (lit : S.t)
    (z3_coef : L.rational)
  : ((string * L.rational) option, error) result =
  let wrapped = S.List [ S.Atom "not"; lit ] in
  match Alethe_farkas.match_one ~fragment wrapped inputs with
  | Error (Alethe_farkas.Unrecognized_literal { sexp }) ->
    Error (Unrecognized_literal { sexp })
  | Error (Alethe_farkas.Unmatched_literal { sexp; compiled }) ->
    Error (Unmatched_literal { sexp; compiled })
  | Error _ ->
    (* Other Alethe_farkas errors (Coefficient_count_mismatch,
       Bad_coefficient, No_la_generic) cannot arise in match_one;
       fall back to a generic literal failure if they ever do. *)
    Error (Unrecognized_literal { sexp = S.to_string lit })
  | Ok None -> Ok None
  | Ok (Some (name, scale)) ->
    Ok (Some (name, L.rat_mul z3_coef scale))

(** Align every clause literal to an IR input, producing the matched
    [(name, coefficient)] list. *)
let align_extract
    ~(fragment : string)
    ~(inputs : Alethe_farkas.input_entry list)
    (extract : Z3_proof.farkas_extract)
  : ((string * L.rational) list, error) result =
  let rec walk acc = function
    | [], [] -> Ok (List.rev acc)
    | lit :: lits, c :: coefs ->
      (match align_one ~fragment ~inputs lit c with
       | Error e -> Error e
       | Ok None -> walk acc (lits, coefs)
       | Ok (Some entry) -> walk (entry :: acc) (lits, coefs))
    | _ -> Ok (List.rev acc)  (* unreachable: Z3_proof guarantees equal length *)
  in
  walk [] (extract.literals, extract.coefficients)

(* --- top-level extraction -------------------------------------------- *)

(** Parse the z3 proof, find the Farkas-flavored th-lemma, align
    each clause literal to an IR hypothesis or the negated goal,
    and return the witness as JSON consumable by [Farkas.verify].

    Returns [Error _] on any failure — the caller (the dispatch
    ladder) should fall through to the next strategy
    ([Farkas_search.try_close] or the Tier 0 oracle) on error. *)
let extract (ir : Ir.t) (proof_str : string) : (Yojson.Safe.t, error) result =
  match Z3_proof.extract_proof_term proof_str with
  | None -> Error No_envelope
  | Some term ->
    (match Z3_proof.find_farkas_clause term with
     | None -> Error No_farkas_clause
     | Some extract_payload ->
       let fragment = Farkas.effective_fragment ir in
       let inputs = Alethe_farkas.compile_ir_inputs ir in
       (match align_extract ~fragment ~inputs extract_payload with
        | Error e -> Error e
        | Ok entries ->
          Ok (Alethe_farkas.witness_to_json
                (Alethe_farkas.dedupe entries))))

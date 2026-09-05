(** Extract a Tier 1 Farkas witness from a z3 proof.

    z3 closes a linear-arithmetic goal by emitting a Farkas-flavored
    th-lemma — [(_ th-lemma arith farkas C1 C2 ... Cn)] — in one
    of two structural shapes:

    1. Clause-introducing:
       [((_ th-lemma arith farkas C1...Cn) (or (not L1) ... (not Ln)))]
       fed downstream to [unit-resolution]. Coefficients are
       unsigned in practice; the literals are positive atoms once
       the clause's [(not _)] wrappers are stripped.

    2. Direct-from-premises:
       [((_ th-lemma arith farkas C1...Cn) p1 p2 ... pn false)]
       where each [pi] is a proof term whose conclusion is the
       literal [Li]. Coefficients are emitted with z3's internal
       sign convention (we've seen [-1, -1, 1] for an example1-
       shape LIA proof) which is not documented; we take absolute
       values and let [Farkas.verify] decide whether the resulting
       witness is sound. Direct-shape literals can themselves be
       [(not P)] forms (because z3's premises may prove negated
       atoms), so the alignment compiles them through a uniform
       [compile_summand] that handles both polarities.

    Verifying that those literals are exactly the IR's hypotheses
    (plus the negated goal) reduces the problem to:

    1. Locate the th-lemma application via [Z3_proof.find_farkas]
       (tries clause shape first, then direct).
    2. For each literal compile a [Farkas.compiled] form via
       [compile_summand], applying the LIA +1 trick.
    3. Compile each IR hypothesis and the negated goal the same
       way via [Farkas.compile_hypothesis].
    4. Match each z3 literal to an IR input by linear-form
       equality under positive scaling (or any nonzero scaling
       when the IR side is an equality).
    5. Multiply the absolute value of the z3 coefficient by the
       scale factor and emit the matched [(hypothesis_name,
       coefficient)] list as a JSON witness consumable by
       [Farkas.verify].
    6. Pre-verify the witness inside this module via
       [Farkas.verify]. If verification fails the heuristic is
       wrong (typically a sign-convention mismatch on the direct
       shape) and we return [Error Witness_did_not_verify]; the
       dispatch ladder falls through to the next strategy
       ([Farkas_search.try_close]) without minting an unverifiable
       Tier 1 cert. *)

module L = Linear_arith
module S = Alethe.Sexp

(* --- error taxonomy --------------------------------------------------- *)

type error =
  | No_envelope
  | No_farkas_th_lemma
  | Unrecognized_literal of { sexp : string }
  | Unmatched_literal of { sexp : string; compiled : string }
  | Witness_did_not_verify of { detail : string }

let error_kind = function
  | No_envelope -> "no_envelope"
  | No_farkas_th_lemma -> "no_farkas_th_lemma"
  | Unrecognized_literal _ -> "unrecognized_literal"
  | Unmatched_literal _ -> "unmatched_literal"
  | Witness_did_not_verify _ -> "witness_did_not_verify"

let error_detail = function
  | No_envelope -> "could not parse z3 proof envelope"
  | No_farkas_th_lemma ->
    "no Farkas-flavored th-lemma in proof (likely opaque arith form)"
  | Unrecognized_literal { sexp } -> "could not linearize: " ^ sexp
  | Unmatched_literal { sexp; compiled } ->
    Printf.sprintf "no IR input matches clause literal %s (compiled %s)"
      sexp compiled
  | Witness_did_not_verify { detail } ->
    "witness did not pass Farkas.verify: " ^ detail

(* --- compilation: positive and (not P) literals --------------------- *)

(** Take the absolute value of a rational. *)
let rat_abs (r : L.rational) : L.rational =
  if L.rat_is_pos r || L.rat_is_zero r then r else L.rat_neg r

(** Compile a literal participating in the Farkas sum to a
    [Farkas.compiled] form. Handles two cases:

    * Positive atom [(<= a b)], [(>= a b)], [(= a b)], etc. —
      compile directly via [Alethe_farkas.compile_atom_pos].
    * Negation [(not P)] — compile [P] and apply
      [Alethe_farkas.neg_compiled] to flip the sense. (Equality
      negations [(not (= a b))] can't be compiled this way; we
      return [None] and let the alignment step fail with
      [Unrecognized_literal].)

    Strict forms get the LIA +1 trick under non-LRA fragments to
    line up with [Farkas.compile_hypothesis] on the IR side. *)
let compile_summand ?(fragment = "LRA") (lit : S.t) : Farkas.compiled option =
  let raw =
    match lit with
    | S.List [ S.Atom "not"; inner ] ->
      (match Alethe_farkas.compile_atom_pos inner with
       | Some c -> Alethe_farkas.neg_compiled c
       | None -> None)
    | _ -> Alethe_farkas.compile_atom_pos lit
  in
  match raw with
  | None -> None
  | Some c when String.equal fragment "LRA" -> Some c
  | Some c -> Some (Alethe_farkas.lia_normalize c)

(* --- shape matching, including Le/Lt vs Eq ---------------------------- *)

(** Match a z3 literal's compiled form against an IR input's. We
    extend [Alethe_farkas.match_shape] with cross-shape matches
    [Le ~ Eq] and [Lt ~ Eq]: when z3's preprocessing splits an IR
    equality hypothesis into [<=] / [>=] halves, the th-lemma's
    literal lands as a [Le] or [Lt] form whose linear shape still
    coincides with the IR's [Eq]. Equalities accept any nonzero
    scale; the sign of the resulting witness coefficient is
    legal under [Farkas.verify]'s "any nonzero rational" rule for
    [Eq] hypotheses. *)
let match_z3_to_ir
    ~(from_z3 : Farkas.compiled)
    ~(from_ir : Farkas.compiled)
  : L.rational option =
  match from_z3, from_ir with
  | Farkas.Le _, Farkas.Le _
  | Farkas.Lt _, Farkas.Lt _
  | Farkas.Eq _, Farkas.Eq _ ->
    (* The same-shape cases are exactly what Alethe_farkas.match_shape
       does; reuse so equality with cvc5's matching stays coupled. *)
    Alethe_farkas.match_shape ~from_cvc5:from_z3 ~from_ir
  | Farkas.Le c, Farkas.Eq d
  | Farkas.Lt c, Farkas.Eq d ->
    (match Alethe_farkas.scale_factor c d with
     | Some r when not (L.rat_is_zero r) -> Some r
     | _ -> None)
  | _ -> None

(* --- alignment ------------------------------------------------------- *)

(** Match one (literal, z3-coefficient) pair to an IR input. The
    resulting witness coefficient is [|z3_coef| * scale_factor]
    — we take the absolute value of [z3_coef] because z3's
    direct-shape sign convention is unverified; if abs is wrong
    the witness simply fails [Farkas.verify] and the caller falls
    through. *)
let align_one
    ~(fragment : string)
    ~(inputs : Alethe_farkas.input_entry list)
    (lit : S.t)
    (z3_coef : L.rational)
  : ((string * L.rational) option, error) result =
  let abs_coef = rat_abs z3_coef in
  match compile_summand ~fragment lit with
  | None ->
    Error (Unrecognized_literal { sexp = S.to_string lit })
  | Some c when Alethe_farkas.is_constant_form c ->
    (* Pure-constant residue: contributes nothing to the witness. *)
    Ok None
  | Some c ->
    let rec find = function
      | [] ->
        let compiled_str = match c with
          | Farkas.Le f -> "Le(" ^ L.to_string f ^ ")"
          | Farkas.Lt f -> "Lt(" ^ L.to_string f ^ ")"
          | Farkas.Eq f -> "Eq(" ^ L.to_string f ^ ")"
        in
        Error (Unmatched_literal {
          sexp = S.to_string lit;
          compiled = compiled_str;
        })
      | (e : Alethe_farkas.input_entry) :: rest ->
        (match match_z3_to_ir ~from_z3:c ~from_ir:e.compiled with
         | Some r -> Ok (Some (e.name, L.rat_mul abs_coef r))
         | None -> find rest)
    in
    find inputs

(** Align every clause literal to an IR input, producing the
    matched [(name, coefficient)] list. The literal/coefficient
    lists have equal length by [Z3_proof]'s parsing invariant. *)
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

(** Format a [Farkas.verdict] for inclusion in the
    [Witness_did_not_verify] error detail. *)
let verdict_detail = function
  | Farkas.Verified -> "verified"
  | Unknown_hypothesis { hypothesis } ->
    "unknown hypothesis: " ^ hypothesis
  | Duplicate_hypothesis { hypothesis } ->
    "duplicate hypothesis name: " ^ hypothesis
  | Nonlinear { hypothesis; detail } ->
    Printf.sprintf "nonlinear hypothesis %s: %s" hypothesis detail
  | Bad_coefficient { hypothesis; raw } ->
    Printf.sprintf "bad coefficient on %s: %s" hypothesis raw
  | Negative_coefficient { hypothesis; value } ->
    Printf.sprintf "negative coefficient on inequality %s: %s"
      hypothesis value
  | Not_contradictory { residual } ->
    "not contradictory; residual " ^ residual
  | Malformed_witness { detail } -> "malformed: " ^ detail

(** Parse the z3 proof, find a Farkas-flavored th-lemma (either
    shape), align each literal to an IR hypothesis or the negated
    goal, and return the witness as JSON consumable by
    [Farkas.verify]. The witness is pre-verified inside this
    function: if it doesn't pass [Farkas.verify], we return
    [Error Witness_did_not_verify] so the dispatch ladder can
    fall through to [Farkas_search.try_close] without minting an
    unverifiable Tier 1 cert. *)
let extract (ir : Ir.t) (proof_str : string) : (Yojson.Safe.t, error) result =
  match Z3_proof.extract_proof_term proof_str with
  | None -> Error No_envelope
  | Some term ->
    (match Z3_proof.find_farkas term with
     | None -> Error No_farkas_th_lemma
     | Some extract_payload ->
       let fragment = Farkas.effective_fragment ir in
       let inputs = Alethe_farkas.compile_ir_inputs ir in
       (match align_extract ~fragment ~inputs extract_payload with
        | Error e -> Error e
        | Ok entries ->
          let witness =
            Alethe_farkas.witness_to_json (Alethe_farkas.dedupe entries)
          in
          (match Farkas.verify ir witness with
           | Verified -> Ok witness
           | bad ->
             Error (Witness_did_not_verify {
               detail = verdict_detail bad;
             }))))

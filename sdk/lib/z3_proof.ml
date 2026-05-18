(** Minimal z3 proof S-expression parser.

    z3's [(get-proof)] output for an [unsat] verdict is a single
    [(set-logic ...)] form followed by a [(proof TERM)] form, where
    [TERM] is heavily let-bound: subterms and proof terms are both
    shared via [(let ((NAME VAL)) BODY)] forms (typically nested,
    one binding per let). The leaves are positional rule
    applications like [(asserted ATOM)], [(rewrite (= L R))], [(mp
    P EQ Q)], or theory closers like
    [(_ th-lemma arith farkas N1 N2 ...) clause premises... false].

    This module only does what's needed to feed downstream
    extractors:
    1. Parse the proof envelope into S-expressions (we reuse the
       Alethe lexer — z3 atoms include [?x], [$x], [@x] tokens but
       contain no parens or whitespace, so the same tokenizer
       suffices).
    2. Extract the [(proof TERM)] body.
    3. Resolve every nested [(let ((NAME VAL) ...) BODY)] into a
       primitive term tree by substituting each NAME with the
       resolved VAL.

    Higher-level extraction (finding a root [th-lemma], reading
    Farkas coefficients, aligning literals to IR hypotheses) lives
    in [Adapter_z3]'s dispatch path; this module is purely the
    syntax layer. *)

module Sexp = Alethe.Sexp

exception Parse_error of string

(** Parse a complete z3 proof body into the list of top-level
    S-expressions. Reuses [Alethe.parse_string] verbatim — the
    lexer handles z3's atoms ([?x25], [$x37], [@x40], etc.) the
    same way it handles Alethe atoms, since none of those
    characters are paren or whitespace. *)
let parse_string (s : string) : Sexp.t list =
  try Alethe.parse_string s
  with Alethe.Parse_error msg -> raise (Parse_error msg)

(* --- let-binding resolution ------------------------------------------ *)

(** Recognize a [(let BINDINGS BODY)] form. Returns the binding
    list and body when matched, or [None] otherwise. The bindings
    list itself is the inner [((NAME VAL) ...)] S-expression. *)
let as_let (t : Sexp.t) : (Sexp.t list * Sexp.t) option =
  match t with
  | Sexp.List [ Atom "let"; List bindings; body ] ->
    Some (bindings, body)
  | _ -> None

(** [substitute table t] returns [t] with every atom occurrence
    that appears as a key in [table] replaced by the bound value.
    Non-matching atoms and lists are walked structurally. The walk
    does not enter let-binding scope (callers should resolve lets
    bottom-up via [resolve_lets] before substitution); we treat
    every atom uniformly here for simplicity. *)
let rec substitute (table : (string, Sexp.t) Hashtbl.t) (t : Sexp.t) : Sexp.t =
  match t with
  | Atom s ->
    (match Hashtbl.find_opt table s with
     | Some v -> v
     | None -> Atom s)
  | List xs -> List (List.map (substitute table) xs)

(** Resolve every nested [(let BINDINGS BODY)] in [t] into a
    primitive term tree. Bindings are processed in order and each
    binding's value is resolved under the enclosing substitution
    *before* the binding is added — z3 emits single-binding nested
    lets in practice, but multi-binding lets are also handled
    correctly under SMT-LIB's parallel-binding semantics: every
    binding's value is resolved against the OUTER table, then all
    new names enter the table simultaneously for the body's walk.

    The returned term contains no [let] nodes (assuming z3's
    proof format is well-formed: every binder is bound exactly
    once, no shadowing inside its scope). *)
let resolve_lets (t : Sexp.t) : Sexp.t =
  let rec go (table : (string, Sexp.t) Hashtbl.t) (t : Sexp.t) : Sexp.t =
    match as_let t with
    | Some (bindings, body) ->
      let new_pairs = List.map (fun b ->
        match b with
        | Sexp.List [ Atom name; value ] ->
          let resolved = go table value in
          (name, resolved)
        | _ ->
          raise (Parse_error
            (Printf.sprintf "malformed let binding: %s" (Sexp.to_string b))))
        bindings
      in
      let scoped = Hashtbl.copy table in
      List.iter (fun (name, value) -> Hashtbl.replace scoped name value)
        new_pairs;
      go scoped body
    | None ->
      (match t with
       | Atom _ -> substitute table t
       | List xs -> List (List.map (go table) xs))
  in
  go (Hashtbl.create 16) t

(* --- proof envelope -------------------------------------------------- *)

(** Pull the proof term out of z3's [(get-proof)] envelope. The
    envelope is a single outer S-expression
    [((set-logic L) (proof TERM))]; we ignore the [(set-logic ...)]
    line (it carries no information beyond what the IR already
    encodes) and return [TERM] with all let-bindings resolved.

    Returns [None] when the input doesn't match the expected
    envelope shape — callers can fall back to whichever non-Tier-1
    path is appropriate. *)
let extract_proof_term (s : string) : Sexp.t option =
  try
    begin match parse_string s with
    | [ Sexp.List forms ] ->
      let proof_term =
        List.find_map (fun form ->
          match form with
          | Sexp.List (Atom "proof" :: term :: _) -> Some term
          | _ -> None)
          forms
      in
      Option.map resolve_lets proof_term
    | _ -> None
    end
  with Stack_overflow ->
    (* Hostile/buggy z3 output: deep let-nesting or substitution
       blow-up. Fail closed — no Tier-1 extraction, caller falls
       back to the non-Tier-1 path (same as the envelope-mismatch
       [None] case) rather than crashing the process / FFI host. *)
    None

(* --- Farkas th-lemma extraction -------------------------------------- *)

(** A Farkas-flavored th-lemma application reduced to coefficients
    + the literals they apply to. The Farkas certificate's claim
    is that the positive linear combination
    [C1 * L1 + ... + Cn * Ln] (read as a sum of inequality
    expressions) yields a contradiction; each [Ci] is a
    nonnegative rational and each [Li] is the inequality atom in
    the same position.

    For consumers downstream: align [literals] to the IR's
    hypotheses or the negated goal, sign the coefficients
    appropriately (z3 emits unsigned coefficients; the IR side
    decides whether each literal corresponds to a forward or
    flipped hypothesis), and feed the result through
    [Farkas.verify]. *)
type farkas_extract = {
  coefficients : Linear_arith.rational list;
  literals : Sexp.t list;
}

(** Recognize the rule head of a Farkas th-lemma application. The
    rule head looks like [(_ th-lemma arith farkas C1 C2 ... Cn)] —
    an indexed identifier whose first three indices are
    [th-lemma], [arith], [farkas], followed by the Farkas
    coefficients as positional atoms (decimal integers or
    [num/den] rationals). Returns [Some coefficients] when the
    head matches and every coefficient parses as a rational, [None]
    otherwise. *)
let parse_farkas_rule_head (head : Sexp.t) : Linear_arith.rational list option =
  match head with
  | Sexp.List (Atom "_" :: Atom "th-lemma" :: Atom "arith" :: Atom "farkas" :: rest)
    when rest <> [] ->
    let coefs = List.filter_map (fun s ->
      match s with
      | Sexp.Atom token -> Linear_arith.rat_of_string token
      | _ -> None)
      rest
    in
    if List.length coefs = List.length rest then Some coefs else None
  | _ -> None

(** Pull the negated literal [Li] out of a [(not Li)] form. Used
    when destructuring a th-lemma's [(or (not L1) ... (not Ln))]
    clause. *)
let strip_not (s : Sexp.t) : Sexp.t option =
  match s with
  | Sexp.List [ Atom "not"; lit ] -> Some lit
  | _ -> None

(** Destructure a Farkas th-lemma application of the
    "clause-introducing" shape:
    [((_ th-lemma arith farkas C1...Cn) (or (not L1) ... (not Ln)))].

    This is the form z3 emits when the th-lemma will be consumed
    by a downstream [unit-resolution]: th-lemma produces the
    Farkas tautology as a clause, and resolution closes it
    against unit proofs of each [Li].

    Returns [Some {coefficients; literals}] when the application
    shape matches AND the number of clause disjuncts equals the
    number of coefficients; [None] otherwise. *)
let parse_farkas_clause_application (app : Sexp.t)
  : farkas_extract option =
  match app with
  | Sexp.List [ head; Sexp.List (Atom "or" :: disjuncts) ] ->
    (match parse_farkas_rule_head head with
     | None -> None
     | Some coefficients ->
       let lits = List.filter_map strip_not disjuncts in
       if List.length lits <> List.length disjuncts
          || List.length lits <> List.length coefficients
       then None
       else Some { coefficients; literals = lits })
  | _ -> None

(** Walk a proof term depth-first looking for the first
    Farkas-clause th-lemma application (the clause-introducing
    shape consumed by unit-resolution; see
    [parse_farkas_clause_application]). Returns [None] if none is
    present.

    The walk is structural: any list-shaped subterm is recursed
    into. We don't model z3's proof-rule semantics — we just look
    for the syntactic shape. The first match wins; for proofs
    with multiple Farkas th-lemmas (case-split-shaped), a
    different walker will be needed. *)
let rec find_farkas_clause (t : Sexp.t) : farkas_extract option =
  match parse_farkas_clause_application t with
  | Some extract -> Some extract
  | None ->
    (match t with
     | Atom _ -> None
     | List xs ->
       List.fold_left (fun acc child ->
         match acc with
         | Some _ -> acc
         | None -> find_farkas_clause child) None xs)

(* --- direct (premise-shaped) Farkas th-lemma extraction --- *)

(** Pull the conclusion out of a z3 proof rule application. z3's
    proof grammar emits each rule as
    [(rule arg1 ... argN conclusion)] with the conclusion (the
    proven formula) in the LAST positional slot. Returns [Some
    last] for a list-shaped term, [None] for an atom (which can
    only appear post-let-resolution if z3 emits a bare boolean
    like [false] — that has no separate conclusion).

    Used when chasing each premise of a direct-shape th-lemma to
    the literal it proves. The walk is non-recursive: we want the
    immediate conclusion of the proof rule, not a deeper claim
    that some premise of that rule eventually establishes. *)
let chase_to_conclusion (t : Sexp.t) : Sexp.t option =
  match t with
  | Atom _ -> None
  | List xs ->
    (match List.rev xs with
     | [] -> None
     | last :: _ -> Some last)

(** Destructure a Farkas th-lemma application of the
    "direct from premises" shape:
    [((_ th-lemma arith farkas C1...Cn) p1 p2 ... pn false)].

    Each [pi] is a proof term whose conclusion is the literal
    [Li] participating in the Farkas combination; we chase each
    to its literal via [chase_to_conclusion]. The trailing
    [false] is z3's conclusion for the th-lemma itself.

    The coefficients are returned signed exactly as z3 emits them.
    Higher-level consumers (notably [Z3_farkas]) decide how to
    interpret the signs — for example, taking absolute values and
    delegating to [Farkas.verify] as the source of truth, since
    z3's internal sign convention for direct-shape th-lemmas
    isn't documented and a verifying-or-fall-through heuristic is
    safer than committing to a guess.

    Returns [None] if the application doesn't match this shape,
    if the conclusion isn't [false], if any premise is atomic, or
    if the premise count doesn't equal the coefficient count. *)
let parse_farkas_direct_application (app : Sexp.t)
  : farkas_extract option =
  match app with
  | Sexp.List (head :: rest) when rest <> [] ->
    (match parse_farkas_rule_head head with
     | None -> None
     | Some coefficients ->
       (match List.rev rest with
        | Sexp.Atom "false" :: rev_premises ->
          let premises = List.rev rev_premises in
          if List.length premises <> List.length coefficients then None
          else
            let literals = List.filter_map chase_to_conclusion premises in
            if List.length literals = List.length premises then
              Some { coefficients; literals }
            else None
        | _ -> None))
  | _ -> None

(** Walk a proof term depth-first looking for the first
    direct-shaped Farkas th-lemma application. See
    [find_farkas_clause] for the analogous walker over the
    clause-introducing shape; the structure is identical. *)
let rec find_farkas_direct (t : Sexp.t) : farkas_extract option =
  match parse_farkas_direct_application t with
  | Some extract -> Some extract
  | None ->
    (match t with
     | Atom _ -> None
     | List xs ->
       List.fold_left (fun acc child ->
         match acc with
         | Some _ -> acc
         | None -> find_farkas_direct child) None xs)

(** Unified Farkas extraction: try the clause-introducing shape
    first (cleaner literals, unsigned coefficients in practice),
    falling back to the direct-from-premises shape when no clause
    th-lemma is present. The order matters: for a proof that has
    BOTH shapes nested, the outer clause shape wins because the
    clause shape's literals are positive atoms (so consumers don't
    have to chase any further) while direct-shape literals can be
    [(not P)] forms requiring an extra negation step. *)
let find_farkas (t : Sexp.t) : farkas_extract option =
  match find_farkas_clause t with
  | Some e -> Some e
  | None -> find_farkas_direct t

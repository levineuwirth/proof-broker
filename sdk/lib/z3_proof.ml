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
  match parse_string s with
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

(** Minimal Alethe S-expression parser and helpers.

    cvc5 emits Alethe proofs as a parenthesized sequence of [(assume
    ID ATOM)] and [(step ID (cl ...) :rule R [:premises ...] [:args
    ...])] commands, with [(anchor :step ID)]/[(step ID ...)] forms
    bracketing subproofs. We only need enough machinery to:

    1. Parse the proof into S-expressions.
    2. Resolve [(! TERM :named NAME)] annotations into a substitution
       table so subsequent atom references expand to primitive terms.
    3. Walk the entire (possibly nested) command sequence and find
       every [step] form, indexed by ID.
    4. Extract the unique [la_generic] step's clause literals and
       rational coefficient args.

    The parser is deliberately lax: it does not validate Alethe
    schema beyond what's needed for these queries, and it ignores
    [anchor] forms entirely (we just collect every [step] regardless
    of subproof depth — IDs are dotted and unique). *)

(* --- S-expressions --------------------------------------------------- *)

module Sexp = struct
  type t =
    | Atom of string
    | List of t list

  let rec to_string = function
    | Atom s -> s
    | List xs -> "(" ^ String.concat " " (List.map to_string xs) ^ ")"
end

(* --- lexer / parser --------------------------------------------------- *)

exception Parse_error of string

let is_whitespace c = c = ' ' || c = '\t' || c = '\n' || c = '\r'
let is_paren c = c = '(' || c = ')'

(** Tokenize an Alethe proof string. SMT-LIB-style line comments
    starting with [;] are skipped to end-of-line. Atoms run from one
    delimiter (whitespace, paren) to the next. *)
let tokenize (s : string) : string list =
  let n = String.length s in
  let i = ref 0 in
  let toks = ref [] in
  while !i < n do
    let c = s.[!i] in
    if is_whitespace c then incr i
    else if c = ';' then begin
      while !i < n && s.[!i] <> '\n' do incr i done
    end
    else if is_paren c then begin
      toks := String.make 1 c :: !toks;
      incr i
    end
    else begin
      let j = ref !i in
      while !j < n
            && not (is_whitespace s.[!j])
            && not (is_paren s.[!j]) do
        incr j
      done;
      toks := String.sub s !i (!j - !i) :: !toks;
      i := !j
    end
  done;
  List.rev !toks

let rec parse_one (toks : string list ref) : Sexp.t =
  match !toks with
  | [] -> raise (Parse_error "unexpected EOF")
  | "(" :: rest ->
    toks := rest;
    let rec loop acc =
      match !toks with
      | [] -> raise (Parse_error "missing close paren")
      | ")" :: rest' -> toks := rest'; Sexp.List (List.rev acc)
      | _ ->
        let item = parse_one toks in
        loop (item :: acc)
    in
    loop []
  | ")" :: _ -> raise (Parse_error "unexpected close paren")
  | tok :: rest ->
    toks := rest;
    Sexp.Atom tok

(** Parse a complete proof string into the list of top-level forms.
    cvc5's [(get-proof)] output is wrapped in a single outer pair
    of parens, so the result typically has a single [List] element
    whose contents are the [assume]/[step]/[anchor] commands. *)
let parse_string (s : string) : Sexp.t list =
  let toks = ref (tokenize s) in
  let acc = ref [] in
  while !toks <> [] do
    acc := parse_one toks :: !acc
  done;
  List.rev !acc

(* --- named-ref expansion --------------------------------------------- *)

(** Find a [:named NAME] keyword inside an annotation list. cvc5 may
    attach other keywords ([:pattern], etc.) so we scan rather than
    expect a specific position. *)
let rec find_named_annotation = function
  | Sexp.Atom ":named" :: Sexp.Atom name :: _ -> Some name
  | _ :: rest -> find_named_annotation rest
  | [] -> None

(** Walk [t], stripping every [(! INNER :named NAME)] form to its
    inner term and recording [NAME → expanded_inner] in [table].
    Subsequent atom occurrences of [NAME] (anywhere in the same
    walk, or in later walks sharing [table]) are substituted with
    the expanded form.

    Inner annotations are expanded first, so the table always holds
    fully-primitive terms. Self-referential names (illegal in
    Alethe) would produce infinite recursion; we don't defend
    against that. *)
let rec expand_one
    (table : (string, Sexp.t) Hashtbl.t)
    (t : Sexp.t) : Sexp.t =
  match t with
  | Atom s ->
    (match Hashtbl.find_opt table s with
     | Some v -> v
     | None -> Atom s)
  | List (Atom "!" :: inner :: annots) ->
    let stripped = expand_one table inner in
    (match find_named_annotation annots with
     | Some name -> Hashtbl.replace table name stripped
     | None -> ());
    stripped
  | List xs ->
    List (List.map (expand_one table) xs)

(* --- step extraction -------------------------------------------------- *)

type step = {
  id : string;
  clause : Sexp.t list;
  rule : string;
  args : Sexp.t list option;
  premises : string list option;
}

(** Pull the clause literals from a [(cl ...)] form. *)
let clause_of (s : Sexp.t) : Sexp.t list option =
  match s with
  | List (Atom "cl" :: lits) -> Some lits
  | _ -> None

(** Walk a list of [Sexp.t] alternating keyword/value pairs and
    return them as an assoc list. Stops at the first malformed pair
    (silently, since steps may have been truncated by an earlier
    parse error). *)
let kv_pairs (xs : Sexp.t list) : (string * Sexp.t) list =
  let rec walk acc = function
    | Sexp.Atom k :: v :: tl when String.length k > 0 && k.[0] = ':' ->
      walk ((k, v) :: acc) tl
    | _ -> List.rev acc
  in
  walk [] xs

(** Match a single [(step ID CLAUSE :rule R [:premises ...] [:args ...])]
    form into the [step] record, after named-ref expansion of the
    clause. Returns [None] for any other form. *)
let step_of_sexp ~table (s : Sexp.t) : step option =
  match s with
  | List (Atom "step" :: Atom id :: clause_form :: rest) ->
    let clause_form = expand_one table clause_form in
    let rest = List.map (expand_one table) rest in
    let kvs = kv_pairs rest in
    let rule = match List.assoc_opt ":rule" kvs with
      | Some (Atom r) -> r | _ -> ""
    in
    let args = match List.assoc_opt ":args" kvs with
      | Some (List xs) -> Some xs | _ -> None
    in
    let premises = match List.assoc_opt ":premises" kvs with
      | Some (List xs) ->
        Some (List.filter_map
                (function Sexp.Atom a -> Some a | _ -> None)
                xs)
      | _ -> None
    in
    let clause = match clause_of clause_form with
      | Some lits -> lits | None -> []
    in
    Some { id; clause; rule; args; premises }
  | _ -> None

(** Match a single [(assume ID ATOM)] form. Returns [(id,
    expanded_atom)] or [None]. As a side effect, records any
    [:named] annotations on the atom into [table]. *)
let assume_of_sexp ~table (s : Sexp.t) : (string * Sexp.t) option =
  match s with
  | List [ Atom "assume"; Atom id; atom ] ->
    let atom' = expand_one table atom in
    Some (id, atom')
  | _ -> None

type proof = {
  assumes : (string * Sexp.t) list;
  steps : step list;
  table : (string, Sexp.t) Hashtbl.t;
}

(** Walk a sequence of top-level forms, extracting all [assume]s
    and [step]s. Subproof anchors and other forms are recursed into
    so nested steps (e.g. [t6.t10.t21]) are picked up. The shared
    [table] threads named-ref expansion across the whole proof. *)
let collect ~table (cmds : Sexp.t list) : (string * Sexp.t) list * step list =
  let assumes = ref [] in
  let steps = ref [] in
  let rec go cmd =
    match assume_of_sexp ~table cmd with
    | Some pair -> assumes := pair :: !assumes
    | None ->
      match step_of_sexp ~table cmd with
      | Some s -> steps := s :: !steps
      | None ->
        (* Recurse into List forms so nested anchor/step bodies are
           still walked. We don't care about (anchor :step ID) per
           se; we just want all step forms regardless of nesting. *)
        match cmd with
        | List xs -> List.iter go xs
        | Atom _ -> ()
  in
  List.iter go cmds;
  (List.rev !assumes, List.rev !steps)

(** Top-level parse: read the proof string, walk every form and
    record assumes / steps with named-ref expansion applied. *)
let parse (s : string) : proof =
  let table = Hashtbl.create 64 in
  let top = parse_string s in
  let assumes, steps = collect ~table top in
  { assumes; steps; table }

(** Find every step whose [:rule] matches [name]. *)
let steps_with_rule (p : proof) (name : string) : step list =
  List.filter (fun (s : step) -> String.equal s.rule name) p.steps

(** Find the unique [la_generic] step in [p], or [None] if there is
    no such step or there are several (the caller can decide whether
    to fall back). *)
let unique_la_generic (p : proof) : step option =
  match steps_with_rule p "la_generic" with
  | [ s ] -> Some s
  | _ -> None

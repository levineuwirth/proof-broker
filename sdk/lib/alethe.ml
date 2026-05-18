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

  (** JSON serialization for crossing the FFI to Lean. Atoms render
      as JSON strings; lists as JSON arrays. The encoding is
      unambiguous because JSON's [String] and [List] are distinct
      type tags, so the inverse [of_json] is total without an
      auxiliary tag field. Note that an Alethe atom that happens to
      look like a number ([42]) still rides as [`String "42"`]. *)
  let rec to_json = function
    | Atom s -> `String s
    | List xs -> `List (List.map to_json xs)

  let rec of_json (j : Yojson.Safe.t) : t =
    match j with
    | `String s -> Atom s
    | `List xs -> List (List.map of_json xs)
    | _ ->
      raise (Codec.Decode_error
               ("expected JSON string or array for Alethe Sexp", j))
end

(* --- lexer / parser --------------------------------------------------- *)

exception Parse_error of string

(** Max S-expression / named-ref nesting depth. Solver stdout is
    untrusted (a hostile or buggy build, or a goal crafted to make
    the solver emit deeply-nested output): unbounded recursion in
    [parse_one]/[expand_one] would overflow the stack and crash the
    process — and through the FFI, the host. Past this depth we
    raise [Parse_error] (caught upstream → fail-closed) instead.
    50k is orders of magnitude beyond any legitimate Alethe proof
    in v1 scope. [parse]/[parse_string] additionally backstop
    [Stack_overflow] in case any non-bounded recursion is reached. *)
let max_parse_depth = 50_000

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

let rec parse_one ?(depth = 0) (toks : string list ref) : Sexp.t =
  if depth > max_parse_depth then
    raise (Parse_error "S-expression nesting exceeds max_parse_depth");
  match !toks with
  | [] -> raise (Parse_error "unexpected EOF")
  | "(" :: rest ->
    toks := rest;
    let rec loop acc =
      match !toks with
      | [] -> raise (Parse_error "missing close paren")
      | ")" :: rest' -> toks := rest'; Sexp.List (List.rev acc)
      | _ ->
        let item = parse_one ~depth:(depth + 1) toks in
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
  try
    let toks = ref (tokenize s) in
    let acc = ref [] in
    while !toks <> [] do
      acc := parse_one toks :: !acc
    done;
    List.rev !acc
  with Stack_overflow ->
    (* Backstop: depth bounds should fire first, but any unbounded
       recursion reached on hostile input becomes a typed parse
       failure, never a process crash. *)
    raise (Parse_error "stack overflow while parsing solver output")

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
    Alethe) would otherwise produce infinite recursion on untrusted
    solver output; [max_parse_depth] bounds it to a [Parse_error]. *)
let rec expand_one
    ?(depth = 0)
    (table : (string, Sexp.t) Hashtbl.t)
    (t : Sexp.t) : Sexp.t =
  if depth > max_parse_depth then
    raise (Parse_error "named-ref expansion exceeds max_parse_depth \
                        (self-referential :named?)");
  match t with
  | Atom s ->
    (match Hashtbl.find_opt table s with
     | Some v -> v
     | None -> Atom s)
  | List (Atom "!" :: inner :: annots) ->
    let stripped = expand_one ~depth:(depth + 1) table inner in
    (match find_named_annotation annots with
     | Some name -> Hashtbl.replace table name stripped
     | None -> ());
    stripped
  | List xs ->
    List (List.map (expand_one ~depth:(depth + 1) table) xs)

(* --- step extraction -------------------------------------------------- *)

type step = {
  id : string;
  clause : Sexp.t list;
  rule : string;
  args : Sexp.t list option;
  premises : string list option;
  discharge : string list option;
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
    let discharge = match List.assoc_opt ":discharge" kvs with
      | Some (List xs) ->
        Some (List.filter_map
                (function Sexp.Atom a -> Some a | _ -> None)
                xs)
      | _ -> None
    in
    let clause = match clause_of clause_form with
      | Some lits -> lits | None -> []
    in
    Some { id; clause; rule; args; premises; discharge }
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
  anchors : string list;
  table : (string, Sexp.t) Hashtbl.t;
}

(** Match an [(anchor :step ID ...)] command. Returns the subproof
    ID being opened, or [None] if [s] isn't an anchor. The keyword
    arguments after [:step ID] (e.g. [:assumes (a0 a1)]) are
    ignored — we only need the opened ID. *)
let anchor_id_of_sexp (s : Sexp.t) : string option =
  match s with
  | List (Atom "anchor" :: Atom ":step" :: Atom id :: _) -> Some id
  | _ -> None

(** Walk a sequence of top-level forms, extracting all [assume]s,
    [step]s, and [(anchor :step ID)] openings. Anchors mark the
    set of subproof IDs that the proof actually opens; any dotted
    assume / step whose enclosing-subproof prefix isn't an opened
    anchor is structurally suspect and the verifier rejects it.

    Other List forms are recursed into so nested anchor/step
    bodies are still walked. The shared [table] threads named-ref
    expansion across the whole proof. *)
let collect ~table (cmds : Sexp.t list)
  : (string * Sexp.t) list * step list * string list =
  let assumes = ref [] in
  let steps = ref [] in
  let anchors = ref [] in
  let rec go cmd =
    match assume_of_sexp ~table cmd with
    | Some pair -> assumes := pair :: !assumes
    | None ->
      match step_of_sexp ~table cmd with
      | Some s -> steps := s :: !steps
      | None ->
        (match anchor_id_of_sexp cmd with
         | Some id ->
           anchors := id :: !anchors;
           (match cmd with
            | List xs -> List.iter go xs
            | Atom _ -> ())
         | None ->
           (match cmd with
            | List xs -> List.iter go xs
            | Atom _ -> ()))
  in
  List.iter go cmds;
  (List.rev !assumes, List.rev !steps, List.rev !anchors)

(** Top-level parse: read the proof string, walk every form and
    record assumes / steps / anchors with named-ref expansion
    applied. *)
let parse (s : string) : proof =
  try
    let table = Hashtbl.create 64 in
    let top = parse_string s in
    let assumes, steps, anchors = collect ~table top in
    { assumes; steps; anchors; table }
  with Stack_overflow ->
    (* Backstop over collect / expand_one as well as parse_string. *)
    raise (Parse_error "stack overflow while parsing solver output")

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

(* --- subproof helpers ------------------------------------------------- *)

(** Strip the last dotted component of a step or assume ID, yielding
    the ID of the immediately enclosing subproof. Top-level IDs (no
    dot) return [None]. Examples: ["t1.t10"] → [Some "t1"];
    ["t1.t10.t21"] → [Some "t1.t10"]; ["t1"] → [None]. *)
let enclosing_subproof_id (id : string) : string option =
  match String.rindex_opt id '.' with
  | None -> None
  | Some i -> Some (String.sub id 0 i)

(** Look up an assume's atom by ID. *)
let assume_atom (p : proof) (id : string) : Sexp.t option =
  List.assoc_opt id p.assumes

(** Every step whose [:rule] is ["subproof"]. Each marks the close
    of a subproof whose ID is the step's own ID. The step's
    [:discharge] list names the local assumes. *)
let subproof_close_steps (p : proof) : step list =
  steps_with_rule p "subproof"

(** Steps whose ID lies inside the given subproof (i.e., starts
    with [<subproof_id>.]). *)
let steps_in_subproof (p : proof) (subproof_id : string) : step list =
  let prefix = subproof_id ^ "." in
  let plen = String.length prefix in
  List.filter (fun (s : step) ->
    String.length s.id > plen
    && String.sub s.id 0 plen = prefix) p.steps

(* --- step JSON serialization (for the Lean Tier 3 walker) ----------- *)

(** Serialize a step to JSON for FFI transport. The shape is:
    [{id, rule, clause, args?, premises?, discharge?}], with [args],
    [premises], [discharge] omitted when [None]. Sexp arrays in
    [clause]/[args] use [Sexp.to_json]. *)
let step_to_json (s : step) : Yojson.Safe.t =
  let f = [
    "id", `String s.id;
    "rule", `String s.rule;
    "clause", `List (List.map Sexp.to_json s.clause);
  ] in
  let f = match s.args with
    | None -> f
    | Some xs -> f @ [ "args", `List (List.map Sexp.to_json xs) ]
  in
  let f = match s.premises with
    | None -> f
    | Some xs -> f @ [ "premises", `List (List.map (fun s -> `String s) xs) ]
  in
  let f = match s.discharge with
    | None -> f
    | Some xs ->
      f @ [ "discharge", `List (List.map (fun s -> `String s) xs) ]
  in
  `Assoc f

(** Inverse of [step_to_json]. Optional fields default to [None]
    when missing so the JSON is forward-compatible. *)
let step_of_json (j : Yojson.Safe.t) : step =
  let pairs = match j with
    | `Assoc p -> p
    | _ -> raise (Codec.Decode_error ("expected object for step", j))
  in
  let req k = match List.assoc_opt k pairs with
    | Some v -> v
    | None ->
      raise (Codec.Decode_error
               ("missing required field: " ^ k, `Assoc pairs))
  in
  let str = function
    | `String s -> s
    | other ->
      raise (Codec.Decode_error ("expected string", other))
  in
  let str_list = function
    | `List xs -> List.map str xs
    | other ->
      raise (Codec.Decode_error ("expected array of strings", other))
  in
  let sexp_list = function
    | `List xs -> List.map Sexp.of_json xs
    | other ->
      raise (Codec.Decode_error ("expected array of Sexp JSON", other))
  in
  {
    id = str (req "id");
    rule = str (req "rule");
    clause = sexp_list (req "clause");
    args = Option.map sexp_list (List.assoc_opt "args" pairs);
    premises = Option.map str_list (List.assoc_opt "premises" pairs);
    discharge = Option.map str_list (List.assoc_opt "discharge" pairs);
  }

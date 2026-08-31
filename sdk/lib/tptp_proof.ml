(** Minimal TSTP (TPTP proof) parser for Vampire derivations.

    Vampire's [--proof tptp] output is, between the
    [% SZS output start] / [% SZS output end] markers, a sequence
    of annotated formulas:

    {[
      fof(f1, axiom, ( p(a) ), file('/dev/stdin', h1)).
      fof(f4, negated_conjecture, ( ~q(a) ),
          inference(negated_conjecture,[status(cth)],[f3])).
      cnf(f11, plain, ($false),
          inference(forward_subsumption_resolution,[],[f10,f9])).
    ]}

    Each statement is [LANG(NAME, ROLE, FORMULA, SOURCE).]. The M2
    Tier-3 verifier ([Tier3_tptp]) does provenance + DAG structure
    checking, not formula-level re-derivation, so this parser is
    deliberately shallow:

    * [NAME] and [ROLE] are atoms.
    * [FORMULA] is kept as its verbatim (trimmed) source text —
      enough to recognize the [$false] sink; we never re-parse
      Vampire's reformatted/clausified first-order syntax (var
      renaming, flattening, extra parens make structural equality
      against our serialization unreliable, so we don't rely on
      it — provenance is by axiom *name*, see [Tier3_tptp]).
    * [SOURCE] is parsed into a small term tree because the
      verifier must read the inference rule, its parents, and the
      [file(_, NAME)] / [introduced(_)] provenance tags out of it.

    Hardening mirrors [Alethe]: solver stdout is untrusted, so
    nesting is depth-bounded to a [Parse_error] (caught upstream →
    fail-closed) and [Stack_overflow] is backstopped, never a
    process crash through the FFI. *)

exception Parse_error of string

let max_parse_depth = 50_000

(* --- annotation term model ------------------------------------------- *)

(** A TPTP source/annotation term. [App] is functor application
    ([inference(...)], [file(...)], [introduced(...)], [status(...)]);
    [Tlist] is a bracketed list ([[f3]], [[status(cth)]]); [Atom]
    covers identifiers, single-quoted atoms (quotes kept verbatim),
    [$false], numbers. *)
type term =
  | Atom of string
  | App of string * term list
  | Tlist of term list

let rec term_to_string = function
  | Atom s -> s
  | App (f, xs) ->
    f ^ "(" ^ String.concat "," (List.map term_to_string xs) ^ ")"
  | Tlist xs -> "[" ^ String.concat "," (List.map term_to_string xs) ^ "]"

(* --- statement model ------------------------------------------------- *)

type node = {
  name : string;       (* e.g. "f4" *)
  role : string;       (* axiom | conjecture | negated_conjecture | plain | … *)
  formula : string;    (* verbatim trimmed source text of the formula arg *)
  source : term;       (* parsed 4th arg; [Atom ""] when absent *)
}

type proof = {
  nodes : node list;
  by_name : (string, node) Hashtbl.t;
}

(* --- proof-block extraction ------------------------------------------ *)

(** Slice the lines between [% SZS output start] and
    [% SZS output end]. Vampire always brackets the derivation with
    these; if they are absent (older builds, piped fragment) we fall
    back to the whole input. Comment lines (leading [%]) are dropped
    so they can't appear inside a statement scan. *)
let extract_block (stdout : string) : string =
  let lines = String.split_on_char '\n' stdout in
  let rec collect acc inside = function
    | [] -> List.rev acc
    | line :: rest ->
      let t = String.trim line in
      let starts p = String.length t >= String.length p
                     && String.sub t 0 (String.length p) = p in
      if starts "% SZS output start" then collect acc true rest
      else if starts "% SZS output end" then List.rev acc
      else if inside then
        (if starts "%" then collect acc inside rest
         else collect (line :: acc) inside rest)
      else collect acc inside rest
  in
  let block = collect [] false lines in
  let block =
    if block = [] then
      (* No markers: keep non-comment lines that could be statements. *)
      List.filter
        (fun l ->
           let t = String.trim l in
           t <> "" && not (String.length t > 0 && t.[0] = '%'))
        lines
    else block
  in
  String.concat "\n" block

(* --- statement splitting --------------------------------------------- *)

(** Split the block into raw statement strings. A statement ends at
    a [.] that sits at paren/bracket depth 0 and outside a
    single-quoted atom. Quote escaping follows the TPTP grammar
    ([\\] and [\']). *)
let split_statements (block : string) : string list =
  let n = String.length block in
  let out = ref [] in
  let buf = Buffer.create 256 in
  let depth = ref 0 in
  let in_quote = ref false in
  let i = ref 0 in
  while !i < n do
    let c = block.[!i] in
    if !in_quote then begin
      Buffer.add_char buf c;
      if c = '\\' && !i + 1 < n then begin
        Buffer.add_char buf block.[!i + 1];
        incr i
      end
      else if c = '\'' then in_quote := false
    end
    else begin
      (match c with
       | '\'' -> in_quote := true; Buffer.add_char buf c
       | '(' | '[' -> incr depth; Buffer.add_char buf c
       | ')' | ']' -> decr depth; Buffer.add_char buf c
       | '.' when !depth = 0 ->
         let s = String.trim (Buffer.contents buf) in
         if s <> "" then out := s :: !out;
         Buffer.clear buf
       | _ -> Buffer.add_char buf c)
    end;
    incr i
  done;
  let tail = String.trim (Buffer.contents buf) in
  if tail <> "" then out := tail :: !out;
  List.rev !out

(** Split [s] on top-level commas (depth 0, outside quotes). Used to
    break [LANG(a,b,c,d)]'s inner argument list. *)
let split_top_commas (s : string) : string list =
  let n = String.length s in
  let out = ref [] in
  let buf = Buffer.create 64 in
  let depth = ref 0 in
  let in_quote = ref false in
  let i = ref 0 in
  while !i < n do
    let c = s.[!i] in
    if !in_quote then begin
      Buffer.add_char buf c;
      if c = '\\' && !i + 1 < n then (Buffer.add_char buf s.[!i + 1]; incr i)
      else if c = '\'' then in_quote := false
    end
    else begin
      (match c with
       | '\'' -> in_quote := true; Buffer.add_char buf c
       | '(' | '[' -> incr depth; Buffer.add_char buf c
       | ')' | ']' -> decr depth; Buffer.add_char buf c
       | ',' when !depth = 0 ->
         out := String.trim (Buffer.contents buf) :: !out;
         Buffer.clear buf
       | _ -> Buffer.add_char buf c)
    end;
    incr i
  done;
  out := String.trim (Buffer.contents buf) :: !out;
  List.rev !out

(* --- source (annotation) term parser --------------------------------- *)

let is_ident_char c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
  || (c >= '0' && c <= '9') || c = '_' || c = '$'

(** Tokenize a SOURCE annotation. Single-quoted atoms become one
    token (quotes preserved). Punctuation [( ) [ ] ,] are
    individual tokens. Whitespace separates. *)
let tokenize_src (s : string) : string list =
  let n = String.length s in
  let i = ref 0 in
  let toks = ref [] in
  while !i < n do
    let c = s.[!i] in
    if c = ' ' || c = '\t' || c = '\n' || c = '\r' then incr i
    else if c = '\'' then begin
      let b = Buffer.create 16 in
      Buffer.add_char b c;
      incr i;
      let closed = ref false in
      while !i < n && not !closed do
        let d = s.[!i] in
        Buffer.add_char b d;
        if d = '\\' && !i + 1 < n then
          (Buffer.add_char b s.[!i + 1]; i := !i + 2)
        else if d = '\'' then (closed := true; incr i)
        else incr i
      done;
      toks := Buffer.contents b :: !toks
    end
    else if c = '(' || c = ')' || c = '[' || c = ']' || c = ',' then begin
      toks := String.make 1 c :: !toks; incr i
    end
    else begin
      let j = ref !i in
      while !j < n && is_ident_char s.[!j] do incr j done;
      if !j = !i then incr i  (* skip a stray operator char *)
      else begin
        toks := String.sub s !i (!j - !i) :: !toks;
        i := !j
      end
    end
  done;
  List.rev !toks

let parse_src_term (s : string) : term =
  let toks = ref (tokenize_src s) in
  let rec p depth : term =
    if depth > max_parse_depth then
      raise (Parse_error "source annotation exceeds max_parse_depth");
    match !toks with
    | [] -> Atom ""
    | "[" :: rest ->
      toks := rest;
      let items = plist depth in
      Tlist items
    | tok :: rest ->
      toks := rest;
      (match !toks with
       | "(" :: rest2 ->
         toks := rest2;
         let args = pargs depth in
         App (tok, args)
       | _ -> Atom tok)
  and pargs depth : term list =
    match !toks with
    | ")" :: rest -> toks := rest; []
    | _ ->
      let first = p (depth + 1) in
      let rec more acc =
        match !toks with
        | "," :: rest -> toks := rest; more (p (depth + 1) :: acc)
        | ")" :: rest -> toks := rest; List.rev acc
        | [] -> List.rev acc
        | _ :: rest -> toks := rest; more acc
      in
      more [ first ]
  and plist depth : term list =
    match !toks with
    | "]" :: rest -> toks := rest; []
    | _ ->
      let first = p (depth + 1) in
      let rec more acc =
        match !toks with
        | "," :: rest -> toks := rest; more (p (depth + 1) :: acc)
        | "]" :: rest -> toks := rest; List.rev acc
        | [] -> List.rev acc
        | _ :: rest -> toks := rest; more acc
      in
      more [ first ]
  in
  p 0

(* --- statement parsing ----------------------------------------------- *)

let lang_prefixes = [ "fof("; "cnf("; "tff("; "thf("; "tcf(" ]

(** Parse one statement string into a [node], or [None] if it is
    not a [LANG(name,role,formula[,source])] annotated formula. *)
let parse_statement (stmt : string) : node option =
  let lang =
    List.find_opt
      (fun p ->
         String.length stmt >= String.length p
         && String.sub stmt 0 (String.length p) = p)
      lang_prefixes
  in
  match lang with
  | None -> None
  | Some p ->
    (* Strip [LANG(] … the matching trailing [)]. *)
    let inner_start = String.length p in
    let body = String.sub stmt inner_start
                 (String.length stmt - inner_start) in
    let body = String.trim body in
    let body =
      if String.length body > 0 && body.[String.length body - 1] = ')'
      then String.sub body 0 (String.length body - 1)
      else body
    in
    let args = split_top_commas body in
    (match args with
     | name :: role :: rest when rest <> [] ->
       (* rest = [formula] or [formula; source; …]; the formula is
          the first, the source the next if present (Vampire emits
          exactly one source arg; extra args, if any, are ignored). *)
       let formula, source =
         match rest with
         | [ f ] -> (String.trim f, Atom "")
         | f :: src :: _ -> (String.trim f, parse_src_term src)
         | [] -> ("", Atom "")
       in
       Some { name = String.trim name;
              role = String.trim role;
              formula; source }
     | _ -> None)

(* --- top-level ------------------------------------------------------- *)

let parse (stdout : string) : proof =
  try
    let block = extract_block stdout in
    let stmts = split_statements block in
    let nodes = List.filter_map parse_statement stmts in
    let by_name = Hashtbl.create 64 in
    List.iter (fun n -> Hashtbl.replace by_name n.name n) nodes;
    { nodes; by_name }
  with Stack_overflow ->
    raise (Parse_error "stack overflow while parsing TSTP output")

(* --- source accessors ------------------------------------------------ *)

(** The inference rule name, when the source is [inference(R,_,_)].
    [None] for [file(...)] / [introduced(...)] / absent sources. *)
let inference_rule (n : node) : string option =
  match n.source with
  | App ("inference", Atom r :: _) -> Some r
  | _ -> None

(** Parent node names cited by an [inference(_,_,[p1,p2,…])] source.
    Only the immediate atom children of the parent list are taken
    (Vampire occasionally nests a parent inside a term — those are
    conservatively ignored, which can only make the DAG check
    stricter, never looser). [] for non-inference sources. *)
let parents (n : node) : string list =
  match n.source with
  | App ("inference", [ _; _; Tlist ps ]) ->
    List.filter_map (function Atom a -> Some a | _ -> None) ps
  | _ -> []

(** The axiom/formula name a [file(SRC, NAME)] leaf cites — i.e. the
    name from our input problem (Vampire >= 5.1.0 echoes it by
    default; 5.0.x only under the since-removed
    [--output_axiom_names on]). [None] for non-[file] sources. *)
let file_name (n : node) : string option =
  match n.source with
  | App ("file", [ _; Atom name ]) -> Some name
  | _ -> None

(** True iff the node was introduced by the prover itself
    ([introduced(...)] — skolem definitions, AVATAR components,
    added theory axioms). Such a node injects something that is
    NOT one of our premises, so the provenance verifier must treat
    its presence in the refutation as a fall-through trigger. *)
let is_introduced (n : node) : bool =
  match n.source with
  | App ("introduced", _) -> true
  | _ -> false

(** True iff this node is a leaf: its truth comes from outside the
    derivation (an input [file] formula, or a prover-introduced
    formula), i.e. it has no [inference] parents. *)
let is_leaf (n : node) : bool =
  match n.source with
  | App ("inference", _) -> false
  | _ -> true

(** True iff [n]'s formula is the empty/false sink. Vampire prints
    it as the atom [$false] (sometimes parenthesized). *)
let is_false_sink (n : node) : bool =
  let f = String.trim n.formula in
  let strip s =
    let s = String.trim s in
    let len = String.length s in
    if len >= 2 && s.[0] = '(' && s.[len - 1] = ')'
    then String.trim (String.sub s 1 (len - 2)) else s
  in
  let f = strip (strip f) in
  f = "$false"

(** Distinct inference-rule names used across the proof, sorted —
    feeds [Tptp_passthrough]'s dialect-feature inventory. *)
let rule_inventory (p : proof) : string list =
  List.filter_map inference_rule p.nodes |> List.sort_uniq String.compare

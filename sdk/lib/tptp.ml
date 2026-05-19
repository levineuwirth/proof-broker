(** TPTP serializer (Phase 3 / spec v1.0 §7, roadmap §Phase 3
    deliverable 1).

    Converts an [Ir.t] into a TPTP problem file that asks an ATP
    (Vampire) whether the goal follows from the hypotheses. Unlike
    the SMT-LIB encoding ([Smtlib], which asserts [hyps ∧ ¬goal] and
    reads [unsat]), TPTP uses roles directly: each hypothesis is an
    [axiom], the goal is a [conjecture], and a [% SZS status Theorem]
    reply means the goal holds. The negation is Vampire's job, not
    ours.

    Dialect. Chosen from [ir.logic_classification.order], mirroring
    [Capability_match.check_order] and [Smtlib.pick_logic]:
    * [order <> "higher_order"] → [FOF] (untyped first-order form).
    * [order  = "higher_order"] → [THF] (typed higher-order form),
      the dialect the roadmap's "via Vampire-HOL" exit criterion
      and [examples/example2-function-composition.json] need.

    Identifier discipline. TPTP's lexis splits sharply:
    * Functors / constants / predicates / type names occupy
      lower-word position ([[a-z][A-Za-z0-9_]*]). Anything that
      isn't already a lower-word — [P], [Function.comp] — is
      emitted as a TPTP single-quoted atom ([ 'Function.comp' ]),
      which is lexically a functor and needs no mangling table.
    * Variables occupy upper-word position ([[A-Z][A-Za-z0-9_]*])
      and CANNOT be quoted. Bound variables are therefore
      alpha-renamed to fresh [X1, X2, …] through a scope
      environment, which is also collision-free under shadowing.

    Scope of M1 (this module). The FOF path covers the
    quantifier/connective/equality/uninterpreted-application
    fragment. The THF path additionally covers
    [Lambda]/[App]-as-[@]/typed binders, but requires every applied
    symbol to be a declared [context.free_vars] entry so a
    monomorphic THF type is available — the shape the Phase-3 (M3)
    higher-order reifier will produce. A symbol known only through
    [definitional_metadata] (e.g. [Function.comp] in the worked
    example, pre-unfolding) is reported as [Unsupported_symbol]
    rather than guessed at; this is the same fail-typed contract
    [Smtlib] uses. Arithmetic ([Num_lit], the [arith_target]
    symbols) is out of M1 Vampire scope: arithmetic goals route to
    the SMT adapters, and the Vampire manifest advertises
    non-arithmetic coverage so capability matching never sends one
    here.

    Refinement side-channel. Like [Smtlib], the serializer reports
    the [(source, target)] symbol renamings it applied so the
    adapter can build a [Refinement_record]; for the ATP path these
    correspond to [axiomatization] specializations (spec §7,
    roadmap §Phase 3 deliverable 1). *)

type error =
  | Unsupported_node of { node : string; detail : string }
  | Unsupported_symbol of { symbol : string; detail : string }
  | Unsupported_type of { ty : string; site : string }
  | Bad_arity of { symbol : string; expected : int; got : int }
  | Bad_literal of { value : string; ty : string }
  | Bad_identifier of { name : string; site : string }
  | Higher_order_in_fof of { detail : string }

let kind_of_error = function
  | Unsupported_node _ -> "unsupported_node"
  | Unsupported_symbol _ -> "unsupported_symbol"
  | Unsupported_type _ -> "unsupported_type"
  | Bad_arity _ -> "bad_arity"
  | Bad_literal _ -> "bad_literal"
  | Bad_identifier _ -> "bad_identifier"
  | Higher_order_in_fof _ -> "higher_order_in_fof"

let detail_of_error = function
  | Unsupported_node { node; detail } ->
    Printf.sprintf "%s: %s" node detail
  | Unsupported_symbol { symbol; detail } ->
    Printf.sprintf "%s: %s" symbol detail
  | Unsupported_type { ty; site } ->
    Printf.sprintf "%s at %s" ty site
  | Bad_arity { symbol; expected; got } ->
    Printf.sprintf "%s expects %d args, got %d" symbol expected got
  | Bad_literal { value; ty } ->
    Printf.sprintf "%s does not parse as %s" value ty
  | Bad_identifier { name; site } ->
    Printf.sprintf "%s at %s is not a usable TPTP identifier" name site
  | Higher_order_in_fof { detail } ->
    Printf.sprintf "higher-order construct in a first-order IR: %s" detail

(* --- lexis ----------------------------------------------------------- *)

let is_lower_word_head c = c >= 'a' && c <= 'z'

let is_word_tail c =
  (c >= 'a' && c <= 'z')
  || (c >= 'A' && c <= 'Z')
  || (c >= '0' && c <= '9')
  || c = '_'

(** A bare TPTP lower-word: [[a-z][A-Za-z0-9_]*]. Such names emit
    verbatim; everything else is single-quoted. *)
let is_lower_word (s : string) : bool =
  String.length s > 0
  && is_lower_word_head s.[0]
  && String.for_all is_word_tail s

(** Render a functor / constant / predicate / type name into TPTP
    atom position. Bare lower-words pass through; anything else
    becomes a single-quoted atom with [\\] and ['] escaped per the
    TPTP <single_quoted> grammar. The empty string is the one
    irreducible failure (no valid TPTP atom denotes it). *)
let atom_of_name ~site (name : string) : (string, error) result =
  if name = "" then Error (Bad_identifier { name; site })
  else if is_lower_word name then Ok name
  else begin
    let buf = Buffer.create (String.length name + 2) in
    Buffer.add_char buf '\'';
    String.iter
      (fun c ->
        if c = '\\' || c = '\'' then Buffer.add_char buf '\\';
        Buffer.add_char buf c)
      name;
    Buffer.add_char buf '\'';
    Ok (Buffer.contents buf)
  end

(* --- scope environment ----------------------------------------------- *)

(** Bound IR variables are alpha-renamed to fresh upper-words. The
    environment is an innermost-first assoc list (so shadowing is a
    prepend + first-match lookup) and [next] hands out [X1, X2, …]
    monotonically across the whole problem — fresh per problem, not
    per binder, which keeps names globally unique and the output
    diffable. *)
type env = {
  mutable bound : (string * string) list;
  mutable next : int;
}

let new_env () = { bound = []; next = 0 }

let fresh_var (e : env) : string =
  e.next <- e.next + 1;
  Printf.sprintf "X%d" e.next

(** Push [ir_name ↦ fresh] for the duration of [k]; pop on exit so
    sibling binders don't see each other's locals. *)
let with_bound (e : env) (ir_name : string) (k : string -> 'a) : 'a =
  let v = fresh_var e in
  let saved = e.bound in
  e.bound <- (ir_name, v) :: saved;
  let r = k v in
  e.bound <- saved;
  r

let lookup_bound (e : env) (ir_name : string) : string option =
  List.assoc_opt ir_name e.bound

(* --- specialization side-channel ------------------------------------- *)

type specialization = { source : string; target : string }

let add_spec (specs : specialization list ref) src tgt =
  let pair = { source = src; target = tgt } in
  if not (List.exists (fun s -> s.source = src && s.target = tgt) !specs)
  then specs := !specs @ [ pair ]

(* --- THF type references --------------------------------------------- *)

(** A parsed type reference. [Base] leaves are mapped to TPTP base
    types at emit time ([Prop]/[Bool] → [$o], everything else → a
    declared [$tType]). [Arrow] is right-associative. *)
type ty = Base of string | Arrow of ty * ty

(** Split [s] at the first top-level [->] (depth 0 w.r.t. parens),
    right-associating, after stripping one layer of matched outer
    parens. The IR's arrow type-refs are shallow and use [->] with
    optional surrounding spaces; this is a small hand parser rather
    than a dependency. *)
let rec parse_ty (s : string) : ty =
  let s = String.trim s in
  let s =
    let n = String.length s in
    if n >= 2 && s.[0] = '(' && s.[n - 1] = ')' then begin
      (* Only strip if the leading '(' matches the trailing ')'. *)
      let depth = ref 0 and matched = ref true in
      String.iteri
        (fun i c ->
          if c = '(' then incr depth
          else if c = ')' then begin
            decr depth;
            if !depth = 0 && i <> n - 1 then matched := false
          end)
        s;
      if !matched then String.trim (String.sub s 1 (n - 2)) else s
    end
    else s
  in
  (* Find first top-level "->". *)
  let n = String.length s in
  let depth = ref 0 in
  let split = ref (-1) in
  let i = ref 0 in
  while !split < 0 && !i < n - 1 do
    (match s.[!i] with
     | '(' -> incr depth
     | ')' -> decr depth
     | '-' when !depth = 0 && s.[!i + 1] = '>' -> split := !i
     | _ -> ());
    incr i
  done;
  if !split < 0 then Base (String.trim s)
  else
    let l = String.sub s 0 !split in
    let r = String.sub s (!split + 2) (n - !split - 2) in
    Arrow (parse_ty l, parse_ty r)

(** Base type name → TPTP type. [Prop]/[Bool] are the boolean type
    [$o]; any other base is a user [$tType] whose declaration the
    emitter collects. *)
let tptp_base_type ~site (b : string) : (string, error) result =
  match b with
  | "Prop" | "Bool" -> Ok "$o"
  | "" -> Error (Unsupported_type { ty = b; site })
  | other -> atom_of_name ~site:("type:" ^ site) other

let rec tptp_type ~site (t : ty) : (string, error) result =
  match t with
  | Base b -> tptp_base_type ~site b
  | Arrow (a, b) ->
    let ( let* ) = Result.bind in
    let* sa = tptp_type ~site a in
    let* sb = tptp_type ~site b in
    (* Parenthesize a left-arrow operand: [a > b] is right-assoc, so
       [(a) > b] only needs parens when [a] is itself an arrow. *)
    let sa = match a with Arrow _ -> "(" ^ sa ^ ")" | _ -> sa in
    Ok (Printf.sprintf "%s > %s" sa sb)

(** Collect distinct user base-type names (everything that maps to a
    [$tType], i.e. not [Prop]/[Bool]) reachable from a type-ref. *)
let rec base_names (t : ty) (acc : string list) : string list =
  match t with
  | Base ("Prop" | "Bool" | "") -> acc
  | Base b -> if List.mem b acc then acc else b :: acc
  | Arrow (a, b) -> base_names b (base_names a acc)

(* --- term / formula emission ----------------------------------------- *)

(* FOF distinguishes term position (functions, constants, variables)
   from formula position (predicates, connectives, quantifiers); an
   [App] is a predicate at formula position and a function at term
   position. THF is uniform: every node is a [$o]- or base-typed
   term combined with [@], [&], [!], [^], … so it needs no such
   split. We thread an explicit mode for FOF and ignore it for THF. *)

type mode = Formula | Term

(** The Lean reifier tags applied predicate/function free vars with
    a [UF.] prefix (an SMT-path convention; [Smtlib.emit_app]
    strips it too). The free-var *declaration* carries the bare
    name, so for TPTP — where the declared-symbol check and the
    emitted functor must agree — we strip [UF.] off application
    heads. Non-prefixed symbols pass through unchanged. *)
let strip_uf (sym : string) : string =
  let p = "UF." in
  let pl = String.length p in
  if String.length sym > pl && String.sub sym 0 pl = p
  then String.sub sym pl (String.length sym - pl)
  else sym

let var_or_const ~specs (e : env) ~site (name : string)
  : (string, error) result =
  match lookup_bound e name with
  | Some v -> Ok v
  | None ->
    (* A free [Var] is a 0-ary constant. Record the rename iff the
       atom form differs from the IR name (so the refinement record
       only carries genuine specializations). *)
    let ( let* ) = Result.bind in
    let* a = atom_of_name ~site name in
    if a <> name then add_spec specs name a;
    Ok a

let rec emit_fof ~specs (e : env) ~(mode : mode) (t : Ir.shell_term)
  : (string, error) result =
  let ( let* ) = Result.bind in
  match t with
  | Const { name = "True" } -> Ok "$true"
  | Const { name = "False" } -> Ok "$false"
  | Const { name } ->
    Error (Unsupported_node {
      node = "Const";
      detail = Printf.sprintf "constant %s has no TPTP mapping" name;
    })
  | Var { name } -> var_or_const ~specs e ~site:"Var" name
  | Num_lit { value; ty } -> Error (Bad_literal { value; ty })
  | Not { operand } ->
    let* o = emit_fof ~specs e ~mode:Formula operand in
    Ok (Printf.sprintf "~ (%s)" o)
  | And { left; right } -> emit_fof_bin ~specs e "&" left right
  | Or { left; right } -> emit_fof_bin ~specs e "|" left right
  | Implies { antecedent; consequent } ->
    emit_fof_bin ~specs e "=>" antecedent consequent
  | Eq { left; right; _ } ->
    let* l = emit_fof ~specs e ~mode:Term left in
    let* r = emit_fof ~specs e ~mode:Term right in
    Ok (Printf.sprintf "(%s = %s)" l r)
  | Forall { var; body; _ } -> emit_fof_quant ~specs e "!" var body
  | Exists { var; body; _ } -> emit_fof_quant ~specs e "?" var body
  | App { symbol; args; _ } ->
    let symbol = strip_uf symbol in
    let* fsym = atom_of_name ~site:("App:" ^ symbol) symbol in
    if fsym <> symbol then add_spec specs symbol fsym;
    (match args with
     | [] -> Ok fsym
     | _ ->
       let* sargs =
         List.fold_left
           (fun acc a ->
             let* acc = acc in
             let* sa = emit_fof ~specs e ~mode:Term a in
             Ok (sa :: acc))
           (Ok []) args
       in
       let sargs = List.rev sargs in
       (* Same surface syntax for predicate (formula) and function
          (term) application in TPTP; [mode] only documents intent
          and guards the higher-order rejections below. *)
       ignore mode;
       Ok (Printf.sprintf "%s(%s)" fsym (String.concat ", " sargs)))
  | Lambda _ ->
    Error (Higher_order_in_fof { detail = "Lambda" })
  | Opaque { payload_id } ->
    Error (Unsupported_node {
      node = "Opaque"; detail = "opaque payload " ^ payload_id;
    })

and emit_fof_bin ~specs e op a b =
  let ( let* ) = Result.bind in
  let* sa = emit_fof ~specs e ~mode:Formula a in
  let* sb = emit_fof ~specs e ~mode:Formula b in
  Ok (Printf.sprintf "(%s %s %s)" sa op sb)

and emit_fof_quant ~specs e q var body =
  let ( let* ) = Result.bind in
  with_bound e var (fun v ->
    let* sb = emit_fof ~specs e ~mode:Formula body in
    Ok (Printf.sprintf "%s [%s] : (%s)" q v sb))

(* THF: uniform applicative syntax. [@] is left-associative
   application; connectives and (in)equality are the usual ones;
   binders carry their type. *)
let rec emit_thf ~specs (e : env) (t : Ir.shell_term)
  : (string, error) result =
  let ( let* ) = Result.bind in
  match t with
  | Const { name = "True" } -> Ok "$true"
  | Const { name = "False" } -> Ok "$false"
  | Const { name } ->
    Error (Unsupported_node {
      node = "Const";
      detail = Printf.sprintf "constant %s has no TPTP mapping" name;
    })
  | Var { name } -> var_or_const ~specs e ~site:"Var" name
  | Num_lit { value; ty } -> Error (Bad_literal { value; ty })
  | Not { operand } ->
    let* o = emit_thf ~specs e operand in
    Ok (Printf.sprintf "(~ %s)" o)
  | And { left; right } -> emit_thf_bin ~specs e "&" left right
  | Or { left; right } -> emit_thf_bin ~specs e "|" left right
  | Implies { antecedent; consequent } ->
    emit_thf_bin ~specs e "=>" antecedent consequent
  | Eq { left; right; _ } -> emit_thf_bin ~specs e "=" left right
  | Forall { var; ty; body } -> emit_thf_quant ~specs e "!" var ty body
  | Exists { var; ty; body } -> emit_thf_quant ~specs e "?" var ty body
  | Lambda { binders; body } ->
    let rec go = function
      | [] -> emit_thf ~specs e body
      | (b : Ir.binder) :: rest ->
        let* sty = tptp_type ~site:("lambda:" ^ b.var) (parse_ty b.ty) in
        with_bound e b.var (fun v ->
          let* sb = go rest in
          Ok (Printf.sprintf "(^ [%s : %s] : %s)" v sty sb))
    in
    go binders
  | App { symbol; args; _ } ->
    let symbol = strip_uf symbol in
    let* fsym = atom_of_name ~site:("App:" ^ symbol) symbol in
    if fsym <> symbol then add_spec specs symbol fsym;
    let* sargs =
      List.fold_left
        (fun acc a ->
          let* acc = acc in
          let* sa = emit_thf ~specs e a in
          Ok (sa :: acc))
        (Ok []) args
    in
    let sargs = List.rev sargs in
    (match sargs with
     | [] -> Ok fsym
     | _ ->
       Ok (Printf.sprintf "(%s @ %s)" fsym (String.concat " @ " sargs)))
  | Opaque { payload_id } ->
    Error (Unsupported_node {
      node = "Opaque"; detail = "opaque payload " ^ payload_id;
    })

and emit_thf_bin ~specs e op a b =
  let ( let* ) = Result.bind in
  let* sa = emit_thf ~specs e a in
  let* sb = emit_thf ~specs e b in
  Ok (Printf.sprintf "(%s %s %s)" sa op sb)

and emit_thf_quant ~specs e q var ty body =
  let ( let* ) = Result.bind in
  let* sty = tptp_type ~site:("quant:" ^ var) (parse_ty ty) in
  with_bound e var (fun v ->
    let* sb = emit_thf ~specs e body in
    Ok (Printf.sprintf "(%s [%s : %s] : %s)" q v sty sb))

(* --- problem assembly ------------------------------------------------ *)

type dialect = Fof | Thf

let dialect_string = function Fof -> "fof" | Thf -> "thf"

(** [dialect_of_ir] mirrors [Capability_match.check_order]:
    higher-order IRs go THF, everything else FOF. *)
let dialect_of_ir (ir : Ir.t) : dialect =
  if ir.logic_classification.order = "higher_order" then Thf else Fof

type script = {
  body : string;
  specializations : specialization list;
  dialect : dialect;
}

(** THF requires a monomorphic type for every symbol. M1 sources
    those exclusively from [context.free_vars]; a constant/functor
    used in the goal/hypotheses that is neither a declared free var
    nor introduced by a binder (e.g. a defined function still
    folded in [definitional_metadata]) is reported as
    [Unsupported_symbol] so the failure is typed, not a guess.

    Returns [(applied_or_referenced_names, binder_names)]: the
    first is every [App] head and free-position [Var] name, the
    second every name introduced by a [Forall]/[Exists]/[Lambda]
    binder anywhere in the problem. A name in the first set that is
    in neither [free_vars] nor the second set is undeclared. *)
let collect_symbols (ir : Ir.t) : string list * string list =
  let used = ref [] and binders = ref [] in
  let add r s = if not (List.mem s !r) then r := s :: !r in
  let rec walk = function
    | Ir.App { symbol; args; _ } ->
      add used (strip_uf symbol); List.iter walk args
    | Var { name } -> add used name
    | Forall { var; body; _ } | Exists { var; body; _ } ->
      add binders var; walk body
    | Lambda { binders = bs; body } ->
      List.iter (fun (b : Ir.binder) -> add binders b.var) bs; walk body
    | Implies { antecedent; consequent } -> walk antecedent; walk consequent
    | And { left; right } | Or { left; right }
    | Eq { left; right; _ } -> walk left; walk right
    | Not { operand } -> walk operand
    | Const _ | Num_lit _ | Opaque _ -> ()
  in
  walk ir.goal.shell;
  List.iter (fun (h : Ir.hypothesis) -> walk h.shell) ir.context.hypotheses;
  (List.rev !used, List.rev !binders)

let emit (ir : Ir.t) : (script, error) result =
  let ( let* ) = Result.bind in
  let dialect = dialect_of_ir ir in
  let specs = ref [] in
  let e = new_env () in
  let buf = Buffer.create 256 in
  let* () =
    match dialect with
    | Fof -> Ok ()
    | Thf ->
      (* 1. Every constant/functor must be a declared free var or a
         binder-introduced name; nothing is type-inferred in M1. *)
      let declared =
        List.map (fun (fv : Ir.free_var) -> fv.name) ir.context.free_vars
      in
      let used, binders = collect_symbols ir in
      let undeclared =
        List.filter
          (fun s -> not (List.mem s declared) && not (List.mem s binders))
          used
      in
      let* () =
        match undeclared with
        | [] -> Ok ()
        | s :: _ ->
          Error (Unsupported_symbol {
            symbol = s;
            detail =
              "THF symbol has no context.free_vars declaration; the M1 \
               serializer does not infer types from definitional_metadata \
               or usage (Phase-3 reifier territory)";
          })
      in
      (* 2. Declare user base types ($tType) once each, in first-seen
         order, then the typed constants. Declaration names are
         positional so two emits of the same IR are byte-identical. *)
      let all_bases =
        List.fold_left
          (fun acc (fv : Ir.free_var) -> base_names (parse_ty fv.ty) acc)
          [] ir.context.free_vars
        |> List.rev
      in
      let* () =
        List.fold_left
          (fun acc b ->
            let* i = acc in
            let* a = atom_of_name ~site:("type:" ^ b) b in
            Buffer.add_string buf
              (Printf.sprintf "thf(ty_%d, type, %s: $tType).\n" i a);
            Ok (i + 1))
          (Ok 0) all_bases
        |> Result.map ignore
      in
      List.fold_left
        (fun acc (fv : Ir.free_var) ->
          let* i = acc in
          let* sym = atom_of_name ~site:("free_var:" ^ fv.name) fv.name in
          if sym <> fv.name then add_spec specs fv.name sym;
          let* sty =
            tptp_type ~site:("free_var:" ^ fv.name) (parse_ty fv.ty)
          in
          Buffer.add_string buf
            (Printf.sprintf "thf(decl_%d, type, %s: %s).\n" i sym sty);
          Ok (i + 1))
        (Ok 0) ir.context.free_vars
      |> Result.map ignore
  in
  let emit_formula t =
    match dialect with
    | Fof -> emit_fof ~specs e ~mode:Formula t
    | Thf -> emit_thf ~specs e t
  in
  let lang = dialect_string dialect in
  let* () =
    let rec go = function
      | [] -> Ok ()
      | (h : Ir.hypothesis) :: rest ->
        let* s = emit_formula h.shell in
        (* TPTP formula names share the functor lexis, so a
           non-lower-word hypothesis name (e.g. with a dot) is
           single-quoted by [atom_of_name] just like a symbol. *)
        let* nm = atom_of_name ~site:("hyp:" ^ h.name) h.name in
        Buffer.add_string buf
          (Printf.sprintf "%s(%s, axiom, %s).\n" lang nm s);
        go rest
    in
    go ir.context.hypotheses
  in
  let* g = emit_formula ir.goal.shell in
  Buffer.add_string buf
    (Printf.sprintf "%s(goal, conjecture, %s).\n" lang g);
  Ok { body = Buffer.contents buf; specializations = !specs; dialect }

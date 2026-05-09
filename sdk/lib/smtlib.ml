(** SMT-LIB v2.6 serializer for the LIA fragment.

    Converts an [Ir.t] into an SMT-LIB script that asks an SMT
    solver whether the goal is *provable* — concretely, whether
    [hypotheses ∧ ¬goal] is unsatisfiable. The script ends with
    [(check-sat)] and the convention is that [unsat] from the
    solver means the original goal holds.

    Scope. LIA only:
    * Sorts: [Int], [Real], [Bool], [Prop] (mapped to SMT-LIB
      [Int]/[Real]/[Bool]/[Bool]).
    * Boolean connectives: [And], [Or], [Not], [Implies], [Eq] at
      [Bool/Prop], constants [True]/[False].
    * Arithmetic: [HAdd.hAdd]/[Int.add]/[Add.add]/[+],
      [HSub.hSub]/[Int.sub]/[Sub.sub]/[-],
      [HMul.hMul]/[Int.mul]/[Mul.mul]/[*]
      (linear use only — at least one arg constant),
      [Neg.neg]/[Int.neg], [LE.le]/[<=], [LT.lt]/[<],
      [GE.ge]/[>=], [GT.gt]/[>], [Eq] at [Int/Real].
    * Variables: [Var { name }] becomes a bare identifier; free
      vars are declared via [(declare-const name sort)] using the
      type tags in [ir.context.free_vars].
    * Numeric literals: [Num_lit { value }] emits the number
      verbatim, with negative literals wrapped as [(- N)] per
      SMT-LIB grammar.

    Out of scope. Quantifiers ([Forall]/[Exists]),
    [Lambda]/[Opaque], type-class methods that haven't been
    refined to primitives ([HAdd.hAdd] is accepted but indicates
    pre-refinement IR — adapter callers usually want a refined
    IR), bitvector/string/array sorts, uninterpreted functions.

    Refinement record. The serializer reports which method
    specializations it applied — e.g., [HAdd.hAdd] → [+] — so the
    adapter can record them in the certificate's
    [refinement_record]. The reporting is a side channel
    ([emitted_specializations]); the script string itself does not
    encode the original symbol names. *)

type error =
  | Unsupported_node of { node : string; detail : string }
  | Unsupported_symbol of { symbol : string; detail : string }
  | Unsupported_type of { ty : string; site : string }
  | Bad_arity of { symbol : string; expected : int; got : int }
  | Bad_literal of { value : string; ty : string }
  | Bad_identifier of { name : string; site : string }

let kind_of_error = function
  | Unsupported_node _ -> "unsupported_node"
  | Unsupported_symbol _ -> "unsupported_symbol"
  | Unsupported_type _ -> "unsupported_type"
  | Bad_arity _ -> "bad_arity"
  | Bad_literal _ -> "bad_literal"
  | Bad_identifier _ -> "bad_identifier"

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
    Printf.sprintf "%s at %s is not a SMT-LIB simple symbol; \
                    rename or alpha-convert before serialization \
                    (quoted symbols not supported by the proof-trace \
                    round trip)"
      name site

(* --- identifier quoting ---------------------------------------------- *)

(** SMT-LIB 2.6 reserved words that look like symbols and must be
    quoted to be safely usable as identifiers. Only the keywords
    that can plausibly collide with an IR variable / constant name
    are listed; commands like [check-sat] never appear in identifier
    position so there's no ambiguity. *)
let smtlib_reserved =
  [ "let"; "forall"; "exists"; "match"; "as"; "par"; "_";
    "Bool"; "Int"; "Real" ]

(** Allowed characters in an SMT-LIB simple symbol after the first.
    Spec §3.1: alphanumeric plus a fixed set of punctuation. *)
let is_simple_symbol_tail_char (c : char) =
  (c >= 'a' && c <= 'z')
  || (c >= 'A' && c <= 'Z')
  || (c >= '0' && c <= '9')
  || (match c with
      | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*'
      | '_' | '-' | '+' | '=' | '<' | '>' | '.' | '?' | '/' -> true
      | _ -> false)

let is_simple_symbol_head_char (c : char) =
  is_simple_symbol_tail_char c && not (c >= '0' && c <= '9')

let is_simple_symbol (s : string) : bool =
  String.length s > 0
  && is_simple_symbol_head_char s.[0]
  && String.for_all is_simple_symbol_tail_char s
  && not (List.mem s smtlib_reserved)

(** Render an identifier (variable name, free-var name) safely.

    Names that parse as an SMT-LIB simple symbol (and aren't
    reserved words) pass through verbatim. Anything else is
    rejected with [Bad_identifier]. SMT-LIB does have a quoted
    symbol form ([|...|]) we could fall back to, and an earlier
    iteration of this function did so. We've since removed that
    fallback because it breaks the proof-trace round trip: cvc5
    echoes the name as-is in its Alethe output, but [Alethe.parse]
    tokenizes on whitespace alone and has no special-case for
    [|...|], so a quoted name in the script makes the resulting
    proof unparseable on the verifier side. Until the Alethe lexer
    grows quoted-symbol support, the conservative policy is to
    refuse names that would need quoting at serialization time —
    callers must pre-rename or alpha-convert non-simple identifiers
    before handing the IR to the adapter. *)
let format_identifier ~site (name : string) : (string, error) result =
  if name = "" then Error (Bad_identifier { name; site })
  else if is_simple_symbol name then Ok name
  else Error (Bad_identifier { name; site })

(* --- type mapping ---------------------------------------------------- *)

(** Parse a [BitVec(N)] type-ref into its width. Mirrors the form
    documented in [Ir.type_ref]; returns [None] for any other shape. *)
let parse_bitvec_width (t : Ir.type_ref) : int option =
  let prefix = "BitVec(" in
  let plen = String.length prefix in
  let tlen = String.length t in
  if tlen > plen
     && String.sub t 0 plen = prefix
     && t.[tlen - 1] = ')'
  then
    match int_of_string_opt (String.sub t plen (tlen - plen - 1)) with
    | Some n when n > 0 -> Some n
    | _ -> None
  else None

let sort_of_type_ref ~site (t : Ir.type_ref) : (string, error) result =
  match t with
  | "Int" -> Ok "Int"
  | "Real" -> Ok "Real"
  | "Bool" | "Prop" -> Ok "Bool"
  | other ->
    (match parse_bitvec_width other with
     | Some n -> Ok (Printf.sprintf "(_ BitVec %d)" n)
     | None -> Error (Unsupported_type { ty = other; site }))

(** Parse an arrow-type ref ["T1->T2->...->R"] into [(arg_types,
    return_type)]. Returns [None] for any non-arrow shape (the
    plain primitive types fall through). The arrow separator is
    [->] without surrounding whitespace; the convention is set by
    the bridge reifiers (Lean uses [->] in its IR.TypeRef strings;
    Rocq mirrors). Reused by free-var emission ([declare-fun] when
    arity > 0) and by [pick_logic]'s UF-presence detector. *)
let parse_arrow_type (t : Ir.type_ref) : (string list * string) option =
  let parts = String.split_on_char '>' t in
  (* Crude: split on '>' then post-process the trailing '-'. A
     two-pass approach is more legible than threading a state
     machine — UF type-refs are always shallow (one or two arrows),
     so the cost is O(n). *)
  let stripped = List.map (fun p ->
    let n = String.length p in
    if n > 0 && p.[n - 1] = '-' then String.sub p 0 (n - 1) else p)
    parts
  in
  match List.rev stripped with
  | last :: rest_rev when List.length stripped >= 2 ->
    Some (List.rev rest_rev, last)
  | _ -> None

(* --- specialization side-channel ------------------------------------- *)

(** A method specialization the serializer applied: ["HAdd.hAdd"] →
    ["+"], etc. Reported once per distinct [(source, target)] pair
    in encounter order so the adapter can construct a
    [Refinement_record] without duplication. *)
type specialization = { source : string; target : string }

let add_spec (specs : specialization list ref) src tgt =
  let pair = { source = src; target = tgt } in
  if not (List.exists (fun s -> s.source = src && s.target = tgt) !specs)
  then specs := !specs @ [ pair ]

(* --- term emission --------------------------------------------------- *)

(** Map a shell-symbol to its SMT-LIB primitive. Booleans go through
    a separate path (the IR uses [App] for arithmetic predicates but
    structural variants for [And]/[Or]/etc.), so this table is
    arithmetic-and-relational only. Returns the SMT-LIB primitive
    plus the "source" name to record in the specialization log. *)
let arith_target = function
  | "HAdd.hAdd" | "Int.add" | "Add.add" | "+" -> Some ("+", "HAdd.hAdd")
  | "HSub.hSub" | "Int.sub" | "Sub.sub" | "-" -> Some ("-", "HSub.hSub")
  | "HMul.hMul" | "Int.mul" | "Mul.mul" | "*" -> Some ("*", "HMul.hMul")
  | "Neg.neg" | "Int.neg" -> Some ("-", "Neg.neg")
  | "LE.le" | "<=" -> Some ("<=", "LE.le")
  | "LT.lt" | "<"  -> Some ("<", "LT.lt")
  | "GE.ge" | ">=" -> Some (">=", "GE.ge")
  | "GT.gt" | ">"  -> Some (">", "GT.gt")
  | _ -> None

(** BV-flavored symbol mapping. Same shape as [arith_target] but for
    QF_BV operators. Comparisons follow SMT-LIB's split between
    unsigned and signed: [bvult] / [bvule] interpret the operands
    as non-negative integers, [bvslt] / [bvsle] as 2's-complement
    signed. The Lean side's typeclass [<] / [<=] over BitVec
    resolves to the unsigned variants by default; signed
    comparisons need to be written with [BitVec.slt] / [BitVec.sle]
    directly. The reverse direction symbols ([>], [>=]) get
    flipped to the [<] / [<=] form by the reifier rather than
    needing dedicated [bvugt] / [bvuge] etc. mappings here, mirroring
    how [arith_target] handles [GT.gt] / [GE.ge]. *)
let bv_target = function
  | "BV.add" -> Some ("bvadd", "BV.add")
  | "BV.sub" -> Some ("bvsub", "BV.sub")
  | "BV.mul" -> Some ("bvmul", "BV.mul")
  | "BV.and" -> Some ("bvand", "BV.and")
  | "BV.or"  -> Some ("bvor",  "BV.or")
  | "BV.xor" -> Some ("bvxor", "BV.xor")
  | "BV.ult" -> Some ("bvult", "BV.ult")
  | "BV.ule" -> Some ("bvule", "BV.ule")
  | "BV.slt" -> Some ("bvslt", "BV.slt")
  | "BV.sle" -> Some ("bvsle", "BV.sle")
  | _ -> None

(** Format a numeric literal value string into SMT-LIB grammar.

    SMT-LIB's [<numeral>] is a non-negative decimal sequence; a
    negative integer like [-3] is the application [(- 3)]. SMT-LIB
    [<decimal>] is [<numeral>.<digit>+] (e.g. [0.5]). Rationals like
    [3/4] are not directly part of SMT-LIB's literal grammar and are
    emitted as the binary application [(/ 3 4)].

    The IR's [Num_lit.value] follows the schema's NumLit pattern,
    which permits an optional minus, a decimal/integer/rational
    body, and an optional decimal-point or exponent suffix. We
    parse via Zarith ([Linear_arith.rat_of_string]) so arbitrarily
    large numerators and denominators round-trip exactly — neither
    [int_of_string] nor [float_of_string] are sound for the Int /
    Rat cases the IR is allowed to produce post-Zarith graduation
    (e.g., a 25-digit integer or [10^18 / 7] as a hypothesis
    coefficient). Exponent notation ([1e6], [3.14e-2]) is rejected
    here as out of scope; the rewriter is expected to canonicalize
    such literals upstream.

    Behavior by type:
    * [Int]: must parse as an integer (no [/], no [.]). Emitted as
      a numeral, with a leading minus wrapped as [(- N)].
    * [Real]: accepts integer, rational ([N/M]), or decimal
      ([N.M]). Rationals are emitted as [(/ N M)]; decimals are
      emitted verbatim. Negative values are wrapped in [(- ...)].
    * Anything else: rejected as [Bad_literal]. *)
let format_numeric ~(ty : string) (value : string) : (string, error) result =
  let bad () = Error (Bad_literal { value; ty }) in
  if value = "" then bad ()
  else if String.contains value 'e' || String.contains value 'E' then
    bad ()
  else
    let has_slash = String.contains value '/' in
    let has_dot = String.contains value '.' in
    let neg = value.[0] = '-' in
    let mag =
      if neg then String.sub value 1 (String.length value - 1) else value
    in
    let wrap_neg s = if neg then Printf.sprintf "(- %s)" s else s in
    match ty, has_slash, has_dot with
    | "Int", false, false ->
      (try
         let _z = Z.of_string mag in
         Ok (wrap_neg mag)
       with _ -> bad ())
    | "Int", _, _ -> bad ()
    | "Real", false, false ->
      (try
         let _z = Z.of_string mag in
         Ok (wrap_neg mag)
       with _ -> bad ())
    | "Real", true, false ->
      (* [N/M]: parse via Zarith and emit as [(/ N M)]. *)
      (match Linear_arith.rat_of_string mag with
       | Some r when not (Z.equal r.den Z.zero) ->
         let num_s = Z.to_string r.num in
         let den_s = Z.to_string r.den in
         Ok (wrap_neg (Printf.sprintf "(/ %s %s)" num_s den_s))
       | _ -> bad ())
    | "Real", false, true ->
      (* [N.M] decimal. Validate that the body parses as a SMT-LIB
         decimal: digit+ '.' digit+, no other dots. *)
      let dot = String.index mag '.' in
      let int_part = String.sub mag 0 dot in
      let frac_part = String.sub mag (dot + 1) (String.length mag - dot - 1) in
      let all_digits s =
        String.length s > 0
        && String.for_all (fun c -> c >= '0' && c <= '9') s
      in
      if all_digits int_part && all_digits frac_part
         && not (String.contains frac_part '.')
      then Ok (wrap_neg mag)
      else bad ()
    | "Real", true, true ->
      (* The schema technically allows both [/] and [.] together,
         but no SMT-LIB grammar accommodates it; refuse rather than
         guess. *)
      bad ()
    | bvty, false, false when Option.is_some (parse_bitvec_width bvty) ->
      (* [BitVec(N)] literal: SMT-LIB grammar is [(_ bvK W)] where K is
         a non-negative decimal numeral and W is the width. Negative
         IR literals over BV are 2's-complement-translated to the
         non-negative representative in the OCaml side; we don't try
         to do that here — the reifier is expected to emit
         non-negative decimals. *)
      let w = Option.get (parse_bitvec_width bvty) in
      if neg then bad ()
      else
        (try
           let z = Z.of_string mag in
           if Z.sign z < 0 then bad ()
           else Ok (Printf.sprintf "(_ bv%s %d)" (Z.to_string z) w)
         with _ -> bad ())
    | _ -> bad ()

let rec emit_term ~specs (t : Ir.shell_term) : (string, error) result =
  match t with
  | Var { name } -> format_identifier ~site:"Var" name
  | Const { name = "True" } -> Ok "true"
  | Const { name = "False" } -> Ok "false"
  | Const { name } ->
    Error (Unsupported_node {
      node = "Const";
      detail = Printf.sprintf "constant %s has no SMT-LIB mapping" name;
    })
  | Num_lit { value; ty } -> format_numeric ~ty value
  | And { left; right } -> emit_bin_op ~specs "and" left right
  | Or  { left; right } -> emit_bin_op ~specs "or"  left right
  | Implies { antecedent; consequent } ->
    emit_bin_op ~specs "=>" antecedent consequent
  | Not { operand } ->
    let ( let* ) = Result.bind in
    let* o = emit_term ~specs operand in
    Ok (Printf.sprintf "(not %s)" o)
  | Eq { left; right; _ } ->
    emit_bin_op ~specs "=" left right
  | App { symbol; args; _ } -> emit_app ~specs symbol args
  | Forall _ ->
    Error (Unsupported_node {
      node = "Forall";
      detail = "quantifiers not supported in Phase 2.1";
    })
  | Exists _ ->
    Error (Unsupported_node {
      node = "Exists";
      detail = "quantifiers not supported in Phase 2.1";
    })
  | Lambda _ ->
    Error (Unsupported_node {
      node = "Lambda";
      detail = "lambdas not supported";
    })
  | Opaque _ ->
    Error (Unsupported_node {
      node = "Opaque";
      detail = "opaque payloads not supported";
    })

and emit_bin_op ~specs op a b =
  let ( let* ) = Result.bind in
  let* sa = emit_term ~specs a in
  let* sb = emit_term ~specs b in
  Ok (Printf.sprintf "(%s %s %s)" op sa sb)

and emit_app ~specs symbol args =
  (* UF.<name> symbols correspond to declared uninterpreted
     functions; strip the prefix and emit a generic application.
     The free-var declaration ([emit_decls]) handles the matching
     [declare-fun]. *)
  let uf_prefix = "UF." in
  let plen = String.length uf_prefix in
  let slen = String.length symbol in
  let uf_name =
    if slen > plen && String.sub symbol 0 plen = uf_prefix
    then Some (String.sub symbol plen (slen - plen))
    else None
  in
  match uf_name with
  | Some name ->
    let ( let* ) = Result.bind in
    let* sname = format_identifier ~site:("UF:" ^ name) name in
    add_spec specs symbol ("uf:" ^ name);
    let rec emit_args acc = function
      | [] -> Ok (List.rev acc)
      | a :: rest ->
        let* sa = emit_term ~specs a in
        emit_args (sa :: acc) rest
    in
    let* arg_strs = emit_args [] args in
    Ok (Printf.sprintf "(%s %s)" sname (String.concat " " arg_strs))
  | None ->
  let target_lookup =
    match arith_target symbol with
    | Some _ as r -> r
    | None -> bv_target symbol
  in
  match target_lookup with
  | None ->
    Error (Unsupported_symbol {
      symbol;
      detail = "no SMT-LIB mapping; expected refined LIA / LRA / BV \
                primitive, a UF.<name> uninterpreted-function symbol, \
                or one of the recognized typeclass methods";
    })
  | Some (target, source) ->
    add_spec specs source target;
    let ( let* ) = Result.bind in
    (match symbol, args with
     | ("Neg.neg" | "Int.neg"), [ a ] ->
       let* sa = emit_term ~specs a in
       Ok (Printf.sprintf "(- %s)" sa)
     | _, [ a; b ] ->
       let* sa = emit_term ~specs a in
       let* sb = emit_term ~specs b in
       Ok (Printf.sprintf "(%s %s %s)" target sa sb)
     | _, args ->
       let n = List.length args in
       let expected =
         match symbol with
         | "Neg.neg" | "Int.neg" -> 1
         | _ -> 2
       in
       Error (Bad_arity { symbol; expected; got = n }))

(* --- script assembly ------------------------------------------------- *)

(** The result of serializing an [Ir.t]: the SMT-LIB script body
    (without [(check-sat)]/[(exit)] — those are appended by the
    adapter), plus the list of specializations applied. *)
type script = {
  body : string;
  specializations : specialization list;
  logic : string;
}

(** Choose an SMT-LIB logic from the IR's actual term types.

    A free-var-only scan misses closed Real-arithmetic goals
    where every operand is a Real numeric literal or a
    Real-typed equality — those would emit under QF_LIA, and
    cvc5/cvc4 would either reject the script as ill-sorted or
    quietly run it under integer semantics. The rule mirrors
    [Farkas.effective_fragment]: any [Real]-typed free var or
    any [Real] type tag inside any hypothesis or goal shell
    selects QF_LRA; otherwise QF_LIA. We're QF-only in Phase
    2.1; quantifiers would lift to LIA / LRA. *)
(** True iff any subterm carries a [BitVec(N)] type tag, on a
    Num_lit or an Eq's [ty] field. App symbols that are BV ops
    don't carry types; their BV-ness propagates from the operands.
    Mirrors [Farkas.shell_mentions_real]. *)
let rec shell_mentions_bv (t : Ir.shell_term) : bool =
  match t with
  | Var _ | Const _ -> false
  | Num_lit { ty; _ } -> Option.is_some (parse_bitvec_width ty)
  | Eq { ty; left; right } ->
    Option.is_some (parse_bitvec_width ty)
    || shell_mentions_bv left || shell_mentions_bv right
  | App { args; _ } -> List.exists shell_mentions_bv args
  | And { left; right } | Or { left; right } ->
    shell_mentions_bv left || shell_mentions_bv right
  | Implies { antecedent; consequent } ->
    shell_mentions_bv antecedent || shell_mentions_bv consequent
  | Not { operand } -> shell_mentions_bv operand
  | Forall { body; _ } | Exists { body; _ } -> shell_mentions_bv body
  | Lambda { body; _ } -> shell_mentions_bv body
  | Opaque _ -> false

(** True iff any subterm carries a [UF.<name>] App-symbol (the
    convention for uninterpreted functions). The corresponding
    function declaration lives in [free_vars] with an arrow-type
    [ty]; [pick_logic] consults both. *)
let rec shell_mentions_uf (t : Ir.shell_term) : bool =
  match t with
  | Var _ | Const _ | Num_lit _ -> false
  | Eq { left; right; _ } ->
    shell_mentions_uf left || shell_mentions_uf right
  | App { symbol; args; _ } ->
    let prefix = "UF." in
    let plen = String.length prefix in
    let slen = String.length symbol in
    (slen > plen && String.sub symbol 0 plen = prefix)
    || List.exists shell_mentions_uf args
  | And { left; right } | Or { left; right } ->
    shell_mentions_uf left || shell_mentions_uf right
  | Implies { antecedent; consequent } ->
    shell_mentions_uf antecedent || shell_mentions_uf consequent
  | Not { operand } -> shell_mentions_uf operand
  | Forall { body; _ } | Exists { body; _ } -> shell_mentions_uf body
  | Lambda { body; _ } -> shell_mentions_uf body
  | Opaque _ -> false

let pick_logic (ir : Ir.t) : string =
  let any_bv_free_var =
    List.exists
      (fun (fv : Ir.free_var) -> Option.is_some (parse_bitvec_width fv.ty))
      ir.context.free_vars
  in
  let any_bv_term =
    shell_mentions_bv ir.goal.shell
    || List.exists (fun (h : Ir.hypothesis) -> shell_mentions_bv h.shell)
       ir.context.hypotheses
  in
  if any_bv_free_var || any_bv_term then "QF_BV"
  else
    let any_uf_free_var =
      List.exists
        (fun (fv : Ir.free_var) -> Option.is_some (parse_arrow_type fv.ty))
        ir.context.free_vars
    in
    let any_uf_term =
      shell_mentions_uf ir.goal.shell
      || List.exists (fun (h : Ir.hypothesis) -> shell_mentions_uf h.shell)
         ir.context.hypotheses
    in
    let any_real_free_var =
      List.exists (fun (fv : Ir.free_var) -> fv.ty = "Real")
        ir.context.free_vars
    in
    let any_real_term =
      Farkas.shell_mentions_real ir.goal.shell
      || List.exists (fun (h : Ir.hypothesis) ->
           Farkas.shell_mentions_real h.shell)
         ir.context.hypotheses
    in
    let real = any_real_free_var || any_real_term in
    let uf = any_uf_free_var || any_uf_term in
    (* Composition rules — SMT-LIB's logic alphabet uses positional
       prefixes; we just produce the relevant 2-3 of them. Adding
       a non-LIA arithmetic fragment alongside UF (or arrays etc.)
       expands this match exhaustively; in scope today, just
       LIA / LRA crossed with UF presence. *)
    match uf, real with
    | true,  true  -> "QF_UFLRA"
    | true,  false -> "QF_UFLIA"
    | false, true  -> "QF_LRA"
    | false, false -> "QF_LIA"

(** Assemble the SMT-LIB script. Order:
    1. [(set-logic ...)] — picked from free-var sorts.
    2. [(declare-const v sort)] for each free var.
    3. [(assert h)] for each hypothesis.
    4. [(assert (not goal))]
    The closing [(check-sat)] is appended by the adapter so it can
    add solver-specific directives in between. *)
let emit (ir : Ir.t) : (script, error) result =
  let ( let* ) = Result.bind in
  let specs = ref [] in
  let logic = pick_logic ir in
  let buf = Buffer.create 256 in
  Buffer.add_string buf (Printf.sprintf "(set-logic %s)\n" logic);
  let* () =
    let rec emit_decls = function
      | [] -> Ok ()
      | (fv : Ir.free_var) :: rest ->
        let* name =
          format_identifier ~site:("free_var:" ^ fv.name) fv.name
        in
        (match parse_arrow_type fv.ty with
         | Some (arg_tys, ret_ty) ->
           (* Function-typed free var: emit (declare-fun f (T1 T2) R).
              The IR convention is that arrow-typed free_vars
              correspond to UF.* App symbols at use sites; the
              serializer uses the same name (sans "UF." prefix —
              [emit_app] handles the strip). *)
           let* arg_sorts =
             List.fold_left (fun acc t ->
               let* acc = acc in
               let* sort =
                 sort_of_type_ref ~site:("free_var:" ^ fv.name ^ ":arg") t
               in
               Ok (acc @ [ sort ]))
               (Ok []) arg_tys
           in
           let* ret_sort =
             sort_of_type_ref ~site:("free_var:" ^ fv.name ^ ":ret") ret_ty
           in
           Buffer.add_string buf
             (Printf.sprintf "(declare-fun %s (%s) %s)\n"
                name (String.concat " " arg_sorts) ret_sort);
           emit_decls rest
         | None ->
           let* sort = sort_of_type_ref ~site:("free_var:" ^ fv.name) fv.ty in
           Buffer.add_string buf
             (Printf.sprintf "(declare-const %s %s)\n" name sort);
           emit_decls rest)
    in
    emit_decls ir.context.free_vars
  in
  let* () =
    let rec emit_hyps = function
      | [] -> Ok ()
      | (h : Ir.hypothesis) :: rest ->
        let* s = emit_term ~specs h.shell in
        Buffer.add_string buf (Printf.sprintf "(assert %s)\n" s);
        emit_hyps rest
    in
    emit_hyps ir.context.hypotheses
  in
  let* g = emit_term ~specs ir.goal.shell in
  Buffer.add_string buf (Printf.sprintf "(assert (not %s))\n" g);
  Ok {
    body = Buffer.contents buf;
    specializations = !specs;
    logic;
  }

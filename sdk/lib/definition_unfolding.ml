(** Definition unfolding pass.

    Unfolds [App] use sites whose symbol's [definitional_metadata]
    has [kind = "defined_function"] and a [concept_tag] in the
    configured allow-list. Configuration is read from the IR's
    [user_directives.rewriter_preferences.enable_definition_unfolding]
    field, matching the example2 reference fixture's shape.

    Soundness obligation. The pass replaces each matched [App] with
    its definitional equation's right-hand side, instantiated with
    the use-site arguments via capture-avoiding substitution. Logical
    equivalence is by definitional unfolding in the home system's
    foundational logic; the lifting layer reverses the substitution
    using the recorded inversion data plus the original
    [definitional_metadata]. The pass never unfolds across symbol
    boundaries that would require beta reduction; those are skipped
    silently rather than miscompiled.

    See [sdk/lib/substitution.ml] for the substitution discipline,
    including capture avoidance and the [App]-symbol-position rule
    (substitute only when the parameter is bound to [Var] or [Const]). *)

module SS = Set.Make (String)

(* --- DefinitionalMetadata field readers ------------------------------ *)

let json_string_field (j : Yojson.Safe.t) (key : string) : string option =
  match j with
  | `Assoc pairs ->
    (match List.assoc_opt key pairs with
     | Some (`String s) -> Some s
     | _ -> None)
  | _ -> None

let json_field (j : Yojson.Safe.t) (key : string) : Yojson.Safe.t option =
  match j with
  | `Assoc pairs -> List.assoc_opt key pairs
  | _ -> None

(** [unfoldable_equation_opt meta] returns the parsed definitional
    equation (a shell term) iff [meta]'s kind is ["defined_function"]
    and the [definitional_equation] field is present and well-formed.
    Anything off-shape returns [None] — the pass falls back to "no
    unfold" rather than failing. *)
let unfoldable_equation_opt (meta : Yojson.Safe.t) : Ir.shell_term option =
  match json_string_field meta "kind" with
  | Some "defined_function" ->
    (match json_field meta "definitional_equation" with
     | None -> None
     | Some eq ->
       (try Some (Codec.shell_of_json eq)
        with Codec.Decode_error _ -> None))
  | _ -> None

let concept_tag_opt (meta : Yojson.Safe.t) : string option =
  json_string_field meta "concept_tag"

(* --- Equation parsing ------------------------------------------------- *)

(** [strip_foralls t] peels outer [Forall] binders and returns the
    list of (var, type) pairs together with the body. The order of
    the returned list matches the order of [Forall] nesting from
    outside in. *)
let rec strip_foralls (t : Ir.shell_term) : (string * Ir.type_ref) list * Ir.shell_term =
  match t with
  | Forall { var; ty; body } ->
    let more, deepest = strip_foralls body in
    (var, ty) :: more, deepest
  | _ -> [], t

(** [parse_equation eq target_symbol] matches the canonical equation
    shape ["Forall* (Eq T (App target_symbol [Var p1, ..., Var pn]) body)"]
    and returns [(params, body)] when matched, otherwise [None].

    Equations whose left-hand side has [type_args] are accepted;
    equations whose [App] arguments are not all simple parameter
    [Var] occurrences are rejected (the pass relies on this shape to
    build the substitution map). *)
let parse_equation (eq : Ir.shell_term) (target_symbol : string)
  : (string list * Ir.shell_term) option =
  let _params, body = strip_foralls eq in
  match body with
  | Eq { left; right; _ } ->
    (match left with
     | App { symbol; args; _ } when symbol = target_symbol ->
       let param_names =
         List.map
           (fun (a : Ir.shell_term) ->
             match a with Var { name } -> Some name | _ -> None)
           args
       in
       if List.for_all Option.is_some param_names then
         Some (List.map Option.get param_names, right)
       else None
     | _ -> None)
  | _ -> None

(* --- Unfold attempt at one App use site ------------------------------- *)

(** Decide whether [v] is a value our [Substitution] module can
    safely flow into an [App] symbol position (only [Var] and [Const]
    are first-class symbol-like in the shell calculus). Args that
    fail this check force the unfold to be skipped at this site to
    avoid silently miscompiling cases that would need beta reduction. *)
let is_first_class_symbol_value : Ir.shell_term -> bool = function
  | Var _ | Const _ -> true
  | _ -> false

(** [referenced_in_app_position params body] is the set of parameter
    names that appear as [App] symbols in [body]. The unfold may
    only flow [Var]/[Const] arguments into these positions. *)
let rec referenced_in_app_position (params : SS.t) (t : Ir.shell_term) : SS.t =
  let union = List.fold_left SS.union SS.empty in
  match t with
  | Forall { body; _ } | Exists { body; _ } | Lambda { body; _ } ->
    referenced_in_app_position params body
  | Implies { antecedent; consequent } ->
    SS.union (referenced_in_app_position params antecedent)
             (referenced_in_app_position params consequent)
  | And { left; right } | Or { left; right } | Eq { left; right; _ } ->
    SS.union (referenced_in_app_position params left)
             (referenced_in_app_position params right)
  | Not { operand } -> referenced_in_app_position params operand
  | App { symbol; args; _ } ->
    let here = if SS.mem symbol params then SS.singleton symbol else SS.empty in
    SS.union here (union (List.map (referenced_in_app_position params) args))
  | Var _ | Const _ | Num_lit _ | Opaque _ -> SS.empty

(** [try_unfold_app concept_tags defn_meta app] attempts to unfold
    one [App] node. Returns [Some (rewritten_term, symbol)] when the
    unfold proceeded, [None] otherwise (no metadata, wrong kind,
    concept_tag not enabled, equation off-shape, or higher-order
    args needed). *)
let try_unfold_app
      (concept_tags : SS.t)
      (defn_meta : (string * Yojson.Safe.t) list)
      (use : Ir.shell_term)
  : (Ir.shell_term * string) option =
  match use with
  | App { symbol; type_args = _; args } ->
    let ( let* ) = Option.bind in
    let* meta = List.assoc_opt symbol defn_meta in
    let* tag = concept_tag_opt meta in
    if not (SS.mem tag concept_tags) then None
    else
      let* eq = unfoldable_equation_opt meta in
      let* params, body = parse_equation eq symbol in
      if List.length params <> List.length args then None
      else
        let app_pos = referenced_in_app_position (SS.of_list params) body in
        (* Skip the unfold if any arg flowing into an App-symbol
           position is not Var/Const (would require beta reduction). *)
        let rec safe (ps : string list) (xs : Ir.shell_term list) =
          match ps, xs with
          | [], [] -> true
          | p :: ps', x :: xs' ->
            if SS.mem p app_pos && not (is_first_class_symbol_value x) then false
            else safe ps' xs'
          | _ -> false
        in
        if not (safe params args) then None
        else
          let env =
            List.fold_left2
              (fun acc p a -> Substitution.StringMap.add p a acc)
              Substitution.StringMap.empty params args
          in
          Some (Substitution.subst env body, symbol)
  | _ -> None

(* --- Recursive bottom-up unfold over a shell term --------------------- *)

let rec unfold_step
          (concept_tags : SS.t)
          (defn_meta : (string * Yojson.Safe.t) list)
          (t : Ir.shell_term)
  : Ir.shell_term * string list =
  let go = unfold_step concept_tags defn_meta in
  let go_list ts =
    let pairs = List.map go ts in
    List.map fst pairs, List.concat_map snd pairs
  in
  let with_acc t' acc = (t', acc) in
  match t with
  | Forall { var; ty; body } ->
    let body', rs = go body in
    with_acc (Ir.Forall { var; ty; body = body' }) rs
  | Exists { var; ty; body } ->
    let body', rs = go body in
    with_acc (Ir.Exists { var; ty; body = body' }) rs
  | Lambda { binders; body } ->
    let body', rs = go body in
    with_acc (Ir.Lambda { binders; body = body' }) rs
  | Implies { antecedent; consequent } ->
    let a', ra = go antecedent in
    let c', rc = go consequent in
    with_acc (Ir.Implies { antecedent = a'; consequent = c' }) (ra @ rc)
  | And { left; right } ->
    let l', rl = go left in
    let r', rr = go right in
    with_acc (Ir.And { left = l'; right = r' }) (rl @ rr)
  | Or { left; right } ->
    let l', rl = go left in
    let r', rr = go right in
    with_acc (Ir.Or { left = l'; right = r' }) (rl @ rr)
  | Not { operand } ->
    let p, rp = go operand in
    with_acc (Ir.Not { operand = p }) rp
  | Eq { ty; left; right } ->
    let l', rl = go left in
    let r', rr = go right in
    with_acc (Ir.Eq { ty; left = l'; right = r' }) (rl @ rr)
  | App { symbol; type_args; args } ->
    let args', child_rs = go_list args in
    let here = Ir.App { symbol; type_args; args = args' } in
    (match try_unfold_app concept_tags defn_meta here with
     | None -> with_acc here child_rs
     | Some (replaced, sym) -> (replaced, child_rs @ [ sym ]))
  | Var _ | Const _ | Num_lit _ | Opaque _ -> (t, [])

let fixpoint_iteration_cap = 64

let unfold_to_fixpoint
      (concept_tags : SS.t)
      (defn_meta : (string * Yojson.Safe.t) list)
      (t : Ir.shell_term)
  : Ir.shell_term * string list =
  let rec loop t acc i =
    if i >= fixpoint_iteration_cap then
      failwith "definition_unfolding: fixpoint cap exceeded — \
                possible mutually recursive definitional equations"
    else
      let t', rs = unfold_step concept_tags defn_meta t in
      if rs = [] then t, acc
      else loop t' (acc @ rs) (i + 1)
  in
  loop t [] 0

(* --- Pass entry point ------------------------------------------------- *)

let configured_concept_tags (ir : Ir.t) : SS.t =
  match ir.user_directives with
  | Some { rewriter_preferences = Some { enable_definition_unfolding = Some xs; _ }; _ } ->
    SS.of_list xs
  | _ -> SS.empty

(** Build the inversion-data list at one site: a list of
    [{symbol, via, site}] objects. [via] is hard-coded to
    ["definitional_equation"] for v1 — when alternative unfolding
    sources land (extensional axioms, beta reduction, ...), [via]
    will distinguish them. *)
let inversion_entries (site : string) (symbols : string list) : Yojson.Safe.t list =
  List.map
    (fun s ->
      `Assoc [
        "symbol", `String s;
        "via", `String "definitional_equation";
        "site", `String site;
      ])
    symbols

type result = {
  ir : Ir.t;
  trace : Trace.entry;
}

let run (ir : Ir.t) : result =
  let before_hash = Hash.sha256_of_json (Codec.to_json ir) in
  let concept_tags = configured_concept_tags ir in
  let defn_meta = ir.definitional_metadata in
  let unfold_at site t = unfold_to_fixpoint concept_tags defn_meta t |> fun (t', rs) ->
                         t', inversion_entries site rs in
  let goal_shell, goal_inv = unfold_at "goal" ir.goal.shell in
  let new_goal : Ir.goal = { ir.goal with shell = goal_shell } in
  let hyps_with_inv =
    List.mapi
      (fun i (h : Ir.hypothesis) ->
        let site = Printf.sprintf "hypothesis[%d]" i in
        let shell', inv = unfold_at site h.shell in
        ({ h with shell = shell' } : Ir.hypothesis), inv)
      ir.context.hypotheses
  in
  let new_hypotheses = List.map fst hyps_with_inv in
  let hyp_inv = List.concat_map snd hyps_with_inv in
  let all_inv = goal_inv @ hyp_inv in
  let new_context : Ir.context = { ir.context with hypotheses = new_hypotheses } in
  let new_ir : Ir.t = { ir with goal = new_goal; context = new_context } in
  let after_hash = Hash.sha256_of_json (Codec.to_json new_ir) in
  let outcome : Trace.outcome =
    if SS.is_empty concept_tags then Skipped_preconditions
    else if all_inv = [] then No_op
    else Applied
  in
  let inversion_data : Yojson.Safe.t =
    `Assoc [ "unfolded_symbols", `List all_inv ]
  in
  let trace : Trace.entry = {
    pass = "definition_unfolding";
    version = "1.0";
    before_hash;
    after_hash;
    configuration = (
      if SS.is_empty concept_tags then None
      else Some (`Assoc [
        "concepts",
        `List (List.map (fun s -> `String s) (SS.elements concept_tags))
      ])
    );
    outcome = Some outcome;
    inversion_data = Some inversion_data;
    diagnostics = None;
  } in
  { ir = new_ir; trace }

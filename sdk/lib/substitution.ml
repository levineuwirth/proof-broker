(** Capture-avoiding substitution over shell terms.

    Used by [Definition_unfolding] to substitute parameters of a
    definitional equation with use-site arguments. The substitution
    must avoid capture: if a binder in the equation body shares a
    name with a free variable of any substituted-in argument, the
    binder is alpha-renamed before descending. Without this discipline
    the pass would silently miscompile definitions whose bodies use
    common binder names like [a], [x], [n].

    [App] symbol-position substitution. The shell calculus carries the
    function symbol of an [App] as a string, not as a sub-term. When
    the substitution maps a parameter to a [Var] or [Const], we
    substitute the name into [App] symbol positions; for any other
    value (notably [Lambda]) we leave the [App] symbol untouched —
    flowing a [Lambda] into a symbol position would require beta
    reduction, which is out of scope for v1 of [Definition_unfolding].
    Callers can detect this case in advance by checking whether their
    arguments are all [Var]/[Const] before invoking the unfold. *)

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

(** [free_vars t] is the set of variable names appearing free in [t].
    Used to compute capture-avoidance avoid sets. *)
let rec free_vars (t : Ir.shell_term) : StringSet.t =
  match t with
  | Var { name } -> StringSet.singleton name
  | Const _ | Num_lit _ | Opaque _ -> StringSet.empty
  | Forall { var; body; _ } | Exists { var; body; _ } ->
    StringSet.remove var (free_vars body)
  | Lambda { binders; body } ->
    let bound = List.fold_left
                  (fun s (b : Ir.binder) -> StringSet.add b.var s)
                  StringSet.empty binders in
    StringSet.diff (free_vars body) bound
  | Implies { antecedent; consequent } ->
    StringSet.union (free_vars antecedent) (free_vars consequent)
  | And { left; right } | Or { left; right } | Eq { left; right; _ } ->
    StringSet.union (free_vars left) (free_vars right)
  | Not { operand } -> free_vars operand
  | App { args; _ } ->
    List.fold_left
      (fun s arg -> StringSet.union s (free_vars arg))
      StringSet.empty args

(** [fresh avoid base] returns a name not in [avoid]. If [base] is
    free in [avoid], suffixes [_1], [_2], ... until a clear name is
    found. Deterministic given its inputs. *)
let fresh (avoid : StringSet.t) (base : string) : string =
  if not (StringSet.mem base avoid) then base
  else
    let rec loop i =
      let candidate = Printf.sprintf "%s_%d" base i in
      if StringSet.mem candidate avoid then loop (i + 1) else candidate
    in
    loop 1

(** Free vars of all values in an environment — these are the
    capture-risky names when descending under binders. *)
let env_free_vars (env : Ir.shell_term StringMap.t) : StringSet.t =
  StringMap.fold
    (fun _ v acc -> StringSet.union acc (free_vars v))
    env StringSet.empty

(** [subst env t] applies substitution [env] (var-name → shell_term)
    to [t] with capture avoidance. *)
let subst (initial_env : Ir.shell_term StringMap.t) (root : Ir.shell_term)
  : Ir.shell_term =
  let rec go (env : Ir.shell_term StringMap.t) (t : Ir.shell_term)
    : Ir.shell_term =
    match t with
    | Var { name } ->
      (match StringMap.find_opt name env with
       | Some t' -> t'
       | None -> t)
    | Const _ | Num_lit _ | Opaque _ -> t
    | Forall { var; ty; body } ->
      let env', var' = rename_binder env var in
      Forall { var = var'; ty; body = go env' body }
    | Exists { var; ty; body } ->
      let env', var' = rename_binder env var in
      Exists { var = var'; ty; body = go env' body }
    | Lambda { binders; body } ->
      let env_after, binders' =
        List.fold_left_map
          (fun env (b : Ir.binder) ->
            let env', var' = rename_binder env b.var in
            env', ({ var = var'; ty = b.ty } : Ir.binder))
          env binders
      in
      Lambda { binders = binders'; body = go env_after body }
    | Implies { antecedent; consequent } ->
      Implies { antecedent = go env antecedent; consequent = go env consequent }
    | And { left; right } ->
      And { left = go env left; right = go env right }
    | Or { left; right } ->
      Or { left = go env left; right = go env right }
    | Not { operand } -> Not { operand = go env operand }
    | Eq { ty; left; right } ->
      Eq { ty; left = go env left; right = go env right }
    | App { symbol; type_args; args } ->
      let symbol' =
        match StringMap.find_opt symbol env with
        | Some (Var { name } | Const { name }) -> name
        | Some _ | None -> symbol
      in
      App { symbol = symbol'; type_args; args = List.map (go env) args }
  (* rename_binder env bound:
       - if bound is a key of env, drop it (binder shadows our
         substitution for that name);
       - else if bound is a free var of env's codomain, alpha-rename
         to avoid capturing the substituted-in term, and record the
         rename in env so Var bound in the body picks up the new name;
       - else descend with env unchanged.
     Body's own free vars are *not* a capture risk and are not part
     of the avoid set; renaming on body-fvs would produce gratuitous
     renames whenever a binder name happens to recur free in its body.
     Returns (updated_env, possibly_renamed_binder_name). *)
  and rename_binder env bound =
    if StringMap.mem bound env then
      (StringMap.remove bound env, bound)
    else
      let env_fvs = env_free_vars env in
      if not (StringSet.mem bound env_fvs) then (env, bound)
      else
        let bound' = fresh env_fvs bound in
        let env' = StringMap.add bound (Ir.Var { name = bound' }) env in
        (env', bound')
  in
  go initial_env root

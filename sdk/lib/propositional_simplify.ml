(** Propositional simplification pass.

    Bottom-up rewrite of the goal and each hypothesis under a fixed
    set of propositional unit-law and double-negation rules. Iterates
    to a syntactic fixpoint per term so that rewrites that open up
    further opportunities (e.g. [Not (And True P)] → [Not P]) cascade
    in a single pass invocation.

    Records every applied rule in [TraceEntry.inversion_data] under
    the shape [{ "simplifications": [ { "rule": ..., "site": ... }
    ] }] matching the example3 reference fixture
    ([examples/rewrite-trace-example3.json]).

    Soundness obligation. Every rule preserves provability: each is
    a propositional tautology (under the standard semantics of [True],
    [False], [And], [Or], [Not], [Implies]). The lifting layer must
    invert each rule from the recorded site; locality is preserved
    because the bottom-up traversal applies rules in a deterministic
    order, so re-traversing the simplified term in parallel with the
    inverse rule list yields the original term shape.

    Conventions: [True] and [False] are encoded as
    [Const { name = "True" }] / [Const { name = "False" }] in the IR.
    Other propositional constants (e.g., the home system's own [⊤] /
    [⊥] under different names) are not recognized; serializers should
    canonicalize before invoking this pass. *)

(** v1 rule set. Keep this enumerated explicitly: the Python validator,
    the Lean replayer, and the lifting layer all key off these names. *)
type rule =
  | And_True_left
  | And_True_right
  | And_False_left
  | And_False_right
  | Or_True_left
  | Or_True_right
  | Or_False_left
  | Or_False_right
  | Not_True
  | Not_False
  | Not_Not
  | Implies_True_left
  | Implies_False_left
  | Implies_True_right

let rule_to_string = function
  | And_True_left -> "And_True_left"
  | And_True_right -> "And_True_right"
  | And_False_left -> "And_False_left"
  | And_False_right -> "And_False_right"
  | Or_True_left -> "Or_True_left"
  | Or_True_right -> "Or_True_right"
  | Or_False_left -> "Or_False_left"
  | Or_False_right -> "Or_False_right"
  | Not_True -> "Not_True"
  | Not_False -> "Not_False"
  | Not_Not -> "Not_Not"
  | Implies_True_left -> "Implies_True_left"
  | Implies_False_left -> "Implies_False_left"
  | Implies_True_right -> "Implies_True_right"

let true_const : Ir.shell_term = Const { name = "True" }
let false_const : Ir.shell_term = Const { name = "False" }

let is_true (t : Ir.shell_term) =
  match t with Const { name = "True" } -> true | _ -> false

let is_false (t : Ir.shell_term) =
  match t with Const { name = "False" } -> true | _ -> false

(** [simplify_step t] rewrites at the top level of [t] using the v1
    rules, after first simplifying children. Returns the rewritten
    term and the list of rules applied at this node and below. Does
    not iterate at the top — that's [simplify_to_fixpoint]'s job. *)
let rec simplify_step (t : Ir.shell_term) : Ir.shell_term * rule list =
  match t with
  | Forall { var; ty; body } ->
    let body', rs = simplify_step body in
    Forall { var; ty; body = body' }, rs
  | Exists { var; ty; body } ->
    let body', rs = simplify_step body in
    Exists { var; ty; body = body' }, rs
  | Lambda { binders; body } ->
    let body', rs = simplify_step body in
    Lambda { binders; body = body' }, rs
  | Implies { antecedent; consequent } ->
    let a, ra = simplify_step antecedent in
    let c, rc = simplify_step consequent in
    let acc = ra @ rc in
    if is_true a then c, acc @ [ Implies_True_left ]
    else if is_false a then true_const, acc @ [ Implies_False_left ]
    else if is_true c then true_const, acc @ [ Implies_True_right ]
    else Implies { antecedent = a; consequent = c }, acc
  | And { left; right } ->
    let l, rl = simplify_step left in
    let r, rr = simplify_step right in
    let acc = rl @ rr in
    if is_true l then r, acc @ [ And_True_left ]
    else if is_true r then l, acc @ [ And_True_right ]
    else if is_false l then false_const, acc @ [ And_False_left ]
    else if is_false r then false_const, acc @ [ And_False_right ]
    else And { left = l; right = r }, acc
  | Or { left; right } ->
    let l, rl = simplify_step left in
    let r, rr = simplify_step right in
    let acc = rl @ rr in
    if is_true l then true_const, acc @ [ Or_True_left ]
    else if is_true r then true_const, acc @ [ Or_True_right ]
    else if is_false l then r, acc @ [ Or_False_left ]
    else if is_false r then l, acc @ [ Or_False_right ]
    else Or { left = l; right = r }, acc
  | Not { operand } ->
    let p, rp = simplify_step operand in
    if is_true p then false_const, rp @ [ Not_True ]
    else if is_false p then true_const, rp @ [ Not_False ]
    else (match p with
          | Not { operand = q } -> q, rp @ [ Not_Not ]
          | _ -> Not { operand = p }, rp)
  | Eq { ty; left; right } ->
    let l, rl = simplify_step left in
    let r, rr = simplify_step right in
    Eq { ty; left = l; right = r }, rl @ rr
  | App { symbol; type_args; args } ->
    let pairs = List.map simplify_step args in
    let args' = List.map fst pairs in
    let rs = List.concat_map snd pairs in
    App { symbol; type_args; args = args' }, rs
  | Var _ | Const _ | Num_lit _ | Opaque _ -> t, []

(** Bound on the number of fixpoint iterations. Each iteration is
    bottom-up linear in term size; with the v1 rule set, every rule
    strictly reduces some structural measure (count of [And]/[Or]/
    [Not]/[Implies] nodes), so termination is guaranteed at a small
    bound in practice. The cap exists to fail fast if a future rule
    addition accidentally introduces non-termination. *)
let fixpoint_iteration_cap = 64

let simplify_to_fixpoint (t : Ir.shell_term) : Ir.shell_term * rule list =
  let rec loop t acc i =
    if i >= fixpoint_iteration_cap then
      failwith "propositional_simplify: fixpoint cap exceeded — likely a non-terminating rule"
    else
      let t', rs = simplify_step t in
      if rs = [] then t, acc
      else loop t' (acc @ rs) (i + 1)
  in
  loop t [] 0

(** Per-site rewrite: returns the new term plus a list of
    [(rule_name, site)] pairs ready to populate [inversion_data]. *)
let simplify_at (site : string) (t : Ir.shell_term)
  : Ir.shell_term * (string * string) list =
  let t', rules = simplify_to_fixpoint t in
  t', List.map (fun r -> (rule_to_string r, site)) rules

type result = {
  ir : Ir.t;
  trace : Trace.entry;
}

(** Run the pass on a whole IR document. Simplifies the goal and each
    hypothesis in order; the resulting trace entry's [inversion_data]
    enumerates every rewrite with its site name ([goal] or
    [hypothesis[N]]) so the lifting layer can replay them in reverse. *)
let run (ir : Ir.t) : result =
  let before_hash = Hash.sha256_of_json (Codec.to_json ir) in
  let goal_shell, goal_rules = simplify_at "goal" ir.goal.shell in
  let new_goal : Ir.goal = { ir.goal with shell = goal_shell } in
  let hyps_with_rules =
    List.mapi
      (fun i (h : Ir.hypothesis) ->
        let site = Printf.sprintf "hypothesis[%d]" i in
        let shell', rules = simplify_at site h.shell in
        ({ h with shell = shell' } : Ir.hypothesis), rules)
      ir.context.hypotheses
  in
  let new_hypotheses = List.map fst hyps_with_rules in
  let hyp_rules = List.concat_map snd hyps_with_rules in
  let all_rules = goal_rules @ hyp_rules in
  let new_context : Ir.context = { ir.context with hypotheses = new_hypotheses } in
  let new_ir : Ir.t = { ir with goal = new_goal; context = new_context } in
  let after_hash = Hash.sha256_of_json (Codec.to_json new_ir) in
  let outcome : Trace.outcome = if all_rules = [] then No_op else Applied in
  let inversion_data : Yojson.Safe.t =
    `Assoc [
      "simplifications",
      `List (List.map
               (fun (rule, site) ->
                 `Assoc [ "rule", `String rule; "site", `String site ])
               all_rules)
    ]
  in
  let trace : Trace.entry = {
    pass = "propositional_simplification";
    version = "1.0";
    before_hash;
    after_hash;
    configuration = None;
    outcome = Some outcome;
    inversion_data = Some inversion_data;
    diagnostics = None;
  } in
  { ir = new_ir; trace }

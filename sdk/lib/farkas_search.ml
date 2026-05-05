(** Internal Farkas closer.

    Given an IR, try to discover a Farkas witness over its
    hypotheses + [neg_goal] without invoking an external solver.
    On success, returns a JSON witness consumable by [Farkas.verify]
    and addressable by [Farkas.lookup_hypothesis], so the caller can
    drop it directly into a Tier 1 cert payload.

    Why this exists. cvc5 closes some real Farkas problems via
    theory rewrites and emits an Alethe proof with no [la_generic]
    step ([example1-lia-typeclass.json] is the canonical one). The
    cvc5 adapter falls through to a Tier 0 oracle cert in those
    cases, even though the IR is genuinely Farkas-shaped. Running
    this closer between the Alethe extractors and the Tier 0
    fallback rescues those into Tier 1 — so the cert tier reflects
    the IR's structure, not the solver's proof shape.

    Algorithm. Bounded integer-coefficient enumeration. Compile
    every hypothesis (and [neg_goal]) into [Farkas.compiled] form;
    search small integer coefficients in
    [{0, …, bound}] for [Le]/[Lt] inputs and [{-bound, …, bound}]
    for [Eq] inputs; the first combination whose weighted sum is a
    constant satisfying the fragment's Farkas contradiction
    condition wins. The search space scales as
    [(bound+1)^l × (2*bound+1)^e] for [l] inequalities and [e]
    equalities; with the default [bound = 3] this is sub-millisecond
    for typical IR sizes.

    Limits. The search is bounded — coefficients above [bound] or
    coefficients with non-trivial denominators are not found. This
    is intentional: the closer is a fast Tier 1 fallback, not a
    general LP solver. Cases beyond its reach fall through to the
    oracle as before. *)

type input = {
  name : string;
  compiled : Farkas.compiled;
}

type error =
  | No_compilable_inputs
  | Search_exhausted

let kind_of_error = function
  | No_compilable_inputs -> "no_compilable_inputs"
  | Search_exhausted -> "search_exhausted"

let detail_of_error = function
  | No_compilable_inputs ->
    "no IR hypothesis (or neg_goal) compiled to a Farkas-amenable form"
  | Search_exhausted ->
    "no Farkas witness found within the bounded coefficient search"

(** Compile every hypothesis plus [neg_goal] into [Farkas.compiled]
    form. Hypotheses that fail to compile (non-linear, unsupported
    shape) are silently skipped — they can't participate in a
    Farkas witness anyway. The [neg_goal] entry uses the reserved
    name [Farkas.lookup_hypothesis] expects, so the witness JSON
    is directly verifier-ready. *)
let compile_inputs (ir : Ir.t) : input list =
  let fragment = ir.logic_classification.first_order_fragment in
  let from_hyps =
    List.filter_map (fun (h : Ir.hypothesis) ->
      match Farkas.compile_hypothesis ~fragment h.shell with
      | Ok c -> Some { name = h.name; compiled = c }
      | Error _ -> None)
      ir.context.hypotheses
  in
  let neg_goal_input =
    let neg = Ir.Not { operand = ir.goal.shell } in
    match Farkas.compile_hypothesis ~fragment neg with
    | Ok c -> Some { name = "neg_goal"; compiled = c }
    | Error _ -> None
  in
  match neg_goal_input with
  | None -> from_hyps
  | Some ng -> from_hyps @ [ ng ]

(** Try a single coefficient assignment. Returns [Some witness] if
    the weighted sum is a contradictory constant for the fragment;
    [None] otherwise. The integer coefficients ride a sign discipline
    matching [Farkas.verify]: nonneg on [Le]/[Lt], free on [Eq]. *)
let try_assignment ~(lra : bool) (inputs : input list) (coefs : int list)
  : Yojson.Safe.t option =
  let pairs = List.combine inputs coefs in
  let nonzero = List.exists (fun (_, c) -> c <> 0) pairs in
  if not nonzero then None
  else
    let rec sum_up acc has_strict = function
      | [] -> Some (acc, has_strict)
      | (input, c) :: rest ->
        if c = 0 then sum_up acc has_strict rest
        else
          let f, contributes_strict, sign_ok =
            match input.compiled with
            | Farkas.Le f -> f, false, c > 0
            | Farkas.Lt f -> f, c > 0, c > 0
            | Farkas.Eq f -> f, false, true
          in
          if not sign_ok then None
          else
            let r = Linear_arith.mk_rat c 1 in
            let term = Linear_arith.scale r f in
            sum_up
              (Linear_arith.add acc term)
              (has_strict || contributes_strict)
              rest
    in
    match sum_up Linear_arith.zero false pairs with
    | None -> None
    | Some (sum, has_strict) ->
      if not (Linear_arith.is_constant sum) then None
      else
        let k = Linear_arith.constant_value sum in
        let valid =
          if lra
          then Linear_arith.rat_is_pos k
            || (Linear_arith.rat_is_zero k && has_strict)
          else Linear_arith.rat_is_pos k
        in
        if not valid then None
        else
          let entries = List.filter_map (fun (input, c) ->
            if c = 0 then None
            else Some (`Assoc [
              "hypothesis", `String input.name;
              "coefficient", `String (string_of_int c);
            ])) pairs
          in
          Some (`Assoc [ "coefficients", `List entries ])

(** Cartesian product of [ranges]. Materialized rather than
    streamed because the search bound caps the total size — at
    [bound = 3] with up to ~8 inputs we have well under 100k
    candidates and short-circuit on first hit anyway. *)
let cartesian (ranges : int list list) : int list list =
  List.fold_right (fun r acc ->
    List.concat_map (fun c -> List.map (fun t -> c :: t) acc) r)
    ranges
    [ [] ]

(** Per-input integer range under sign discipline: nonneg for
    [Le]/[Lt], two-sided for [Eq]. *)
let range_for ~(bound : int) (input : input) : int list =
  match input.compiled with
  | Farkas.Eq _ -> List.init (2 * bound + 1) (fun i -> i - bound)
  | Farkas.Le _ | Farkas.Lt _ -> List.init (bound + 1) (fun i -> i)

(** Run the bounded search. [bound] caps the absolute value of
    integer coefficients per input. The default ([3]) handles the
    cases this closer is meant to rescue without exploding the
    search; raise it for unusual IRs at the cost of latency. *)
let try_close ?(bound = 3) (ir : Ir.t) : (Yojson.Safe.t, error) result =
  let inputs = compile_inputs ir in
  if inputs = [] then Error No_compilable_inputs
  else
    let lra = String.equal
      ir.logic_classification.first_order_fragment "LRA"
    in
    let ranges = List.map (range_for ~bound) inputs in
    let candidates = cartesian ranges in
    let result = List.find_map
      (fun coefs -> try_assignment ~lra inputs coefs)
      candidates
    in
    match result with
    | Some json -> Ok json
    | None -> Error Search_exhausted

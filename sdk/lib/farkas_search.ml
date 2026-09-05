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

(** Hard cap on the coefficient-space size the search will attempt.
    Beyond it the search is SKIPPED, not attempted; callers treat
    any [Error _] as fall-through to the Tier 0 oracle, so exceeding
    the cap degrades tier, never availability.

    Since the enumeration STREAMS (see [search_first]), this is a
    TIME budget, not a memory one — live memory is O(inputs) at any
    size. The value is measured, not inherited (C4 ROUND 2 (a),
    2026-09-03, 16-core/58GB machine, witness-free k-input IRs so
    the whole space is swept): 4^10 = 1,048,576 candidates cost
    0.77s CPU / 1.3MB live; the D1/70 demo obligation's space is
    exactly that, and 2,000,000 admits it while keeping worst-case
    exhaustion at ~1.3s measured on this fallback path (which only runs
    after solver proof extraction has already failed). The next
    step up (4^11 ≈ 4.2M, ~3s) buys no known goal. Anyone changing
    this constant should re-derive the sweep cost, not carry the
    number forward. *)
let max_candidates = 2_000_000

type input = {
  name : string;
  compiled : Farkas.compiled;
}

type error =
  | No_compilable_inputs
  | Search_exhausted
  | Search_space_exceeded of { saturated : int; range_lengths : int list }
  | Sparse_search_exhausted of { max_support : int; candidates : int }

let kind_of_error = function
  | No_compilable_inputs -> "no_compilable_inputs"
  | Search_exhausted -> "search_exhausted"
  | Search_space_exceeded _ -> "search_space_exceeded"
  | Sparse_search_exhausted _ -> "sparse_search_exhausted"

let detail_of_error = function
  | No_compilable_inputs ->
    "no IR hypothesis (or neg_goal) compiled to a Farkas-amenable form"
  | Search_exhausted ->
    "no Farkas witness found within the bounded coefficient search"
  | Search_space_exceeded { saturated = _; range_lengths } ->
    (* Exact size in float for the MESSAGE only (the saturating int
       cannot tell "just over" from "astronomically over" — C4
       ROUND 2 finding 5; float is exact up to 2^53 and the order of
       magnitude is what the reader needs beyond that). *)
    let exact =
      List.fold_left (fun acc l -> acc *. float_of_int l) 1. range_lengths
    in
    Printf.sprintf
      "coefficient space is %.4g candidates over %d inputs, above \
       the %d cap, and the sparse-support rescue's space is above it \
       too — search skipped (fall through to the oracle tier)"
      exact (List.length range_lengths) max_candidates
  | Sparse_search_exhausted { max_support; candidates } ->
    Printf.sprintf
      "dense coefficient space above the cap; the sparse-support rescue \
       (support <= %d, %d candidates) found no Farkas witness"
      max_support candidates

(** Compile every hypothesis plus [neg_goal] into [Farkas.compiled]
    form. Hypotheses that fail to compile (non-linear, unsupported
    shape) are silently skipped — they can't participate in a
    Farkas witness anyway. The [neg_goal] entry uses the reserved
    name [Farkas.lookup_hypothesis] expects, so the witness JSON
    is directly verifier-ready. *)
let compile_inputs (ir : Ir.t) : input list =
  let fragment = Farkas.effective_fragment ir in
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

(** Streamed enumeration of the coefficient space: for each
    assignment in the cartesian product of [ranges] (first range
    varying slowest — the exact order the materialized product had),
    call [try_coefs] and short-circuit on the first [Some]. Live
    memory is O(number of inputs): nothing is materialized. The
    predecessor of this function built the whole product as a list
    first ("the search bound caps the total size — well under 100k
    candidates"), an assumption nothing enforced; at 13 inputs that
    list was 4^13 ≈ 67M candidates ≈ 4.7GB, and the demo's
    14–15-input goals OOM'd a 58GB machine (C4 ROUND 1 finding 1).
    The size assumption is now enforced by [space_size] in
    [try_close]. *)
let search_first (ranges : int list list)
    ~(try_coefs : int list -> Yojson.Safe.t option)
  : Yojson.Safe.t option =
  let rec go ranges prefix_rev =
    match ranges with
    | [] -> try_coefs (List.rev prefix_rev)
    | r :: rest ->
      List.find_map (fun c -> go rest (c :: prefix_rev)) r
  in
  go ranges []

(** Saturating size of the coefficient space: the product of range
    lengths, computed only until it exceeds [max_candidates] (so no
    overflow at any input count). *)
let space_size (ranges : int list list) : int =
  List.fold_left
    (fun acc r ->
      if acc > max_candidates then acc else acc * List.length r)
    1 ranges

(** Sparse-support rescue (R4 continuation, 2026-09-05).

    The dense enumeration above is exponential in the NUMBER OF
    INPUTS, but a Farkas witness for a real goal is supported on very
    few of them: the verinf `D1/70` obligation needs `hZ` and
    `neg_goal` (support 2) out of 18 compiled inputs, and its dense
    space (4^17) is far above the cap. Before the R4-continuation
    context fix the reifier silently DROPPED five of those inputs
    (assigned-but-uninstantiated metavariable types, see the bridge's
    `normalizeGoalForBroker`), which is the only reason the dense
    space ever fit — "D1/70 (4^10) is rescued" in delta §5.7 was true
    of a context the tactic could not actually see.

    So when the dense space exceeds the cap, enumerate instead by
    SUPPORT: every subset of at most [max_support] inputs, each
    carrying a NONZERO coefficient from its range (the other inputs
    stay 0). The candidate count is sum_{k <= max_support} of
    (products of nonzero-range lengths over k-subsets) — e.g. 66,378
    for 13 inequality inputs at bound 3, against 4^13 ≈ 67M dense —
    and it is held under the SAME [max_candidates] time budget
    (saturating count first, refusal above it), so the worst case
    stays the measured ~1.3 s. Order: support ascending, subsets in
    lexicographic index order, coefficients in range order — the
    first hit is deterministic. The dense path is UNCHANGED whenever
    it fits (its first-hit order is pinned by the streaming tests):
    the rescue runs only where the old code refused, so no witness
    the old code produced can change. Completeness: a witness with
    support above [max_support] or a coefficient above [bound] is not
    found — the named [Sparse_search_exhausted] says so. *)
let max_support = 4

(** Nonzero part of [range_for]: [1..bound] for inequalities, both
    signs for equalities. *)
let nonzero_range_for ~(bound : int) (input : input) : int list =
  match input.compiled with
  | Farkas.Eq _ ->
    List.filter (fun c -> c <> 0)
      (List.init (2 * bound + 1) (fun i -> i - bound))
  | Farkas.Le _ | Farkas.Lt _ -> List.init bound (fun i -> i + 1)

(** Saturating count of sparse candidates: the coefficient of x^k in
    the product of (1 + r_i x) over inputs, summed for 1 <= k <=
    [max_support]; every partial sum saturates at [max_candidates + 1]
    so nothing overflows. *)
let sparse_space_size (nz_lengths : int list) : int =
  let sat x = if x > max_candidates then max_candidates + 1 else x in
  let dp = Array.make (max_support + 1) 0 in
  dp.(0) <- 1;
  List.iter (fun r ->
    for k = max_support downto 1 do
      dp.(k) <- sat (dp.(k) + sat (dp.(k - 1) * r))
    done) nz_lengths;
  let total = ref 0 in
  for k = 1 to max_support do total := sat (!total + dp.(k)) done;
  !total

(** Streamed sparse enumeration; see [max_support]. [nz_ranges] is
    the per-input nonzero range (same order as [inputs]). *)
let search_sparse ~(n : int) ~(nz_ranges : int list array)
    ~(try_coefs : int list -> Yojson.Safe.t option)
  : Yojson.Safe.t option =
  let coefs = Array.make n 0 in
  let rec assign = function
    | [] -> try_coefs (Array.to_list coefs)
    | i :: rest ->
      List.find_map (fun c ->
        coefs.(i) <- c;
        let r = assign rest in
        coefs.(i) <- 0;
        r) nz_ranges.(i)
  in
  let rec subsets k start acc_rev =
    if k = 0 then assign (List.rev acc_rev)
    else
      let rec go i =
        if i > n - k then None
        else match subsets (k - 1) (i + 1) (i :: acc_rev) with
          | Some w -> Some w
          | None -> go (i + 1)
      in
      go start
  in
  let rec by_support k =
    if k > max_support || k > n then None
    else match subsets k 0 [] with
      | Some w -> Some w
      | None -> by_support (k + 1)
  in
  by_support 1

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
    let lra = String.equal (Farkas.effective_fragment ir) "LRA" in
    let ranges = List.map (range_for ~bound) inputs in
    let size = space_size ranges in
    if size > max_candidates then
      (* Dense space above the cap: the sparse-support rescue, under
         the same budget. *)
      let nz_ranges = List.map (nonzero_range_for ~bound) inputs in
      let sparse = sparse_space_size (List.map List.length nz_ranges) in
      if sparse > max_candidates then
        Error (Search_space_exceeded
                 { saturated = size;
                   range_lengths = List.map List.length ranges })
      else
        match
          search_sparse ~n:(List.length inputs)
            ~nz_ranges:(Array.of_list nz_ranges)
            ~try_coefs:(fun coefs -> try_assignment ~lra inputs coefs)
        with
        | Some json -> Ok json
        | None ->
          Error (Sparse_search_exhausted { max_support; candidates = sparse })
    else
      match
        search_first ranges
          ~try_coefs:(fun coefs -> try_assignment ~lra inputs coefs)
      with
      | Some json -> Ok json
      | None -> Error Search_exhausted

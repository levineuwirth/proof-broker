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

(* --- exact recovery: budget constants --------------------------------- *)

(** Largest support the EXACT recovery below examines. Deliberately the same
    value as [max_support] for the sparse rescue: exact recovery is the same
    "few inputs carry the witness" bet, with the magnitude guess removed. It
    is a bound on the size of the support, never on the size of a
    coefficient — recovering a multiplier of 2^18 is what it exists for. *)
let max_exact_support = 4

(** Hard cap on the number of SUPPORT SETS exact recovery will examine.
    Beyond it the search is SKIPPED, not attempted, exactly as
    [max_candidates] governs the enumerating search: exceeding the cap
    degrades tier, never availability.

    The unit here is a support set, not a coefficient assignment, and the two
    are not interchangeable — one support costs an exact rational
    row-reduction of a |vars| x k matrix with k <= [max_exact_support],
    not a constant-time weighted sum. So the value is MEASURED, on
    witness-free IRs so the whole space is swept (R6 checkpoint 2,
    2026-09-06, 16-core machine; `exact_budget.exe` in
    `experiments/c1-cert-recovery/diag/`, output in that campaign's
    `logs/exact_budget.txt`): 48 columns is the first refusal, so
    the cap admits IRs up to 47 columns; the largest in the RMSNorm
    carry-stage corpus has 22.

    This cap bounds the SIZE OF THE SPACE, not the running time — see
    [max_exact_work], which bounds the latter. The two sweeps in that
    campaign's `logs/exact_budget.txt` are what the numbers come from, and
    anyone changing either constant should re-run both rather than carry a
    number forward. Exceeding this cap is a NAMED refusal
    ([Exact_search_space_exceeded]), never a silent truncation. *)
let max_exact_supports = 200_000

(** Hard cap on the WORK exact recovery will do, in units of
    (rows + 1) x k^2 x bit-weight — Gaussian elimination on the support's
    variable matrix, weighted by the size of the numbers in it.

    [max_exact_supports] alone does NOT bound the running time, and the
    checkpoint-2 benchmark did not show that it did: it swept IRs whose forms
    carry few variables each, so every support's matrix was small. An IR with
    46 columns whose forms each mention 64 variables is under the support cap
    and ran for over 30 seconds (R6 checkpoint-2 review, finding 2). Rows are
    the missing dimension, so the budget counts them.

    Deterministic by construction — no wall clock — so a witness is found or
    refused identically on every machine and every run.

    Measured on both shapes (R6 checkpoint 2, `logs/exact_budget.txt` in that
    campaign; 16-core machine). At 12,000,000 the WORST OBSERVED wall time
    across both sweeps is 387 ms, against >30 s for the dense shape with no
    work guard at all. Shape A (few variables per form) sweeps its whole space
    up to 44 columns and is work-refused at 46; shape B (64 variables per
    form) is work-refused from 32 columns on. Both stay well inside the
    enumerating search's own measured ~1.3 s, on a path that runs only after
    BOTH solver proof extraction and that search have already failed.

    387 ms is the maximum MEASURED on these two shapes, not a proof of a
    ceiling: NOT captured is coefficient growth DURING elimination, which
    [bit_weight] estimates from the input coefficients only. A shape whose
    intermediate rationals blow up far beyond its inputs would cost more per
    work unit than either sweep shows. Exceeding the cap is the named refusal
    [Exact_search_work_exceeded]. *)
let max_exact_work = 12_000_000

type input = {
  name : string;
  compiled : Farkas.compiled;
}

type error =
  | No_compilable_inputs
  | Search_exhausted
  | Search_space_exceeded of { saturated : int; range_lengths : int list }
  | Sparse_search_exhausted of { max_support : int; candidates : int }
  | Exact_search_exhausted of { max_support : int; supports : int }
  | Exact_search_space_exceeded of { max_support : int; supports : int }
  | Exact_search_work_exceeded of { supports_examined : int; work : int }

let kind_of_error = function
  | No_compilable_inputs -> "no_compilable_inputs"
  | Search_exhausted -> "search_exhausted"
  | Search_space_exceeded _ -> "search_space_exceeded"
  | Sparse_search_exhausted _ -> "sparse_search_exhausted"
  | Exact_search_exhausted _ -> "exact_search_exhausted"
  | Exact_search_space_exceeded _ -> "exact_search_space_exceeded"
  | Exact_search_work_exceeded _ -> "exact_search_work_exceeded"

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
  | Exact_search_exhausted { max_support; supports } ->
    Printf.sprintf
      "exact recovery examined %d support set(s) of size <= %d and found no \
       Farkas witness: on every one the variable-cancellation system was \
       either full rank (only the zero multiplier) or rank-deficient by more \
       than one (no extreme ray has exactly that support), or the ray it \
       pinned failed the sign or contradiction condition"
      supports max_support
  | Exact_search_space_exceeded { max_support; supports } ->
    Printf.sprintf
      "exact recovery skipped: %d support set(s) of size <= %d is above the \
       %d cap"
      supports max_support max_exact_supports
  | Exact_search_work_exceeded { supports_examined; work } ->
    Printf.sprintf
      "exact recovery stopped after %d support set(s): the variable matrices \
       are large enough that %d work unit(s) were spent, above the %d cap \
       (fall through to the oracle tier)"
      supports_examined work max_exact_work

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
    `neg_goal` (support 2) out of 19 compiled inputs (the corrected
    fixture — CONTINUATION ROUND 1 Low 4 — has 18 hypotheses +
    neg_goal; its sparse space is 493,983, its dense space far above
    the cap). Before the R4-continuation
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

(* ====================================================================== *)
(* Exact recovery (R6 / checkpoint 2)                                      *)
(* ====================================================================== *)

(** Exact-coefficient Farkas recovery: bounded in SUPPORT, unbounded in
    COEFFICIENT MAGNITUDE.

    Why. The enumerating search above cannot reach a witness whose multiplier
    is large — the RMSNorm carry-stage bound `2^18 * g < P` needs 262144, five
    orders of magnitude above [bound = 3], and no bound reaches it: at
    262144 the dense space for that four-input IR is 4.7e21 and the sparse
    rescue's is the same, both astronomically above [max_candidates]
    (`experiments/c1-cert-recovery/reports/checkpoint-1.md` §5). The multiplier
    is not something to guess. Once a SUPPORT is fixed, the requirement that
    every variable cancel is a homogeneous linear system, and the multipliers
    are its solution — so solve for them.

    STRICTLY ADDITIVE. This never runs instead of the enumerating search;
    [try_close_then_exact] runs it only where [try_close] returned [Error _].
    No witness the enumerating search produces can change, and in particular
    the witnesses it finds with support ABOVE [max_exact_support] — the dense
    path has no support limit at all — are untouched (C1 review, finding 1:
    `x0 <= x1 <= x2 <= x3 <= 0 |- x0 <= 0` needs all five inputs at
    coefficient 1, and the dense path finds it today).

    ## The algorithm

    1. COLUMNS. Each [Le]/[Lt] input becomes one column with multiplier
       >= 0. Each [Eq] input becomes TWO columns, carrying `+f` and `-f`,
       both with multiplier >= 0 — that is how the freely-signed equality
       multiplier is handled: it is recovered at the end as the difference
       `mu_plus - mu_minus`. Everything downstream then lives in the
       nonnegative cone `C = { mu >= 0 : A mu = 0 }`, where the rows of `A`
       are the variables and `A[v][j]` is column j's coefficient on `v`.

    2. SUPPORTS. Enumerate subsets S of the columns with |S| <=
       [max_exact_support], support size ascending and lexicographic within a
       size, so the first hit is deterministic.

    3. SOLVE. For each S, row-reduce `A_S` exactly over the rationals and
       read off its null space.
       * nullity 0 — only the zero multiplier; skip.
       * nullity 1 — the null space is a single line; take its generator `u`,
         clear denominators and divide out the gcd (a positive rescaling
         changes nothing that follows), and test `u` and `-u`.
       * nullity >= 2 — SKIPPED BY DESIGN, not by omission. An extreme ray of
         `C` whose support is exactly S forces `nullity(A_S) = 1`; a support
         with nullity >= 2 therefore carries no extreme ray of its own, and
         the rays inside it live on proper subsets, which this enumeration
         also visits (up to the bound). Skipping them loses no witness that
         the bound admits.

    4. ACCEPT. A candidate `u` must have every coordinate >= 0 (the cone's
       sign discipline; this is the check that would be vacuous if equality
       multipliers had not been split), and its constant part must satisfy the
       fragment's contradiction condition — THE SAME ONE [try_assignment] and
       [Farkas.verify] apply: `k > 0`, or, under LRA only, `k = 0` with a
       positively-weighted strict input. Dropping the LRA clause would
       regress goals the enumerating search closes today.

    ## Completeness, stated exactly

    If any Farkas witness exists over the compiled inputs, then some extreme
    ray of `C` is itself a witness: writing a witness `mu = sum_j nu_j r_j`
    over extreme rays with `nu_j >= 0`, the constant part is
    `sum_j nu_j (c . r_j)`, so either some `c . r_j > 0` — that ray is a
    witness — or all the positively-weighted ones have `c . r_j = 0`, in
    which case the ray carrying the strict input is an LRA witness. So the
    only incompleteness is the SUPPORT BOUND: a witness all of whose extreme
    rays need more than [max_exact_support] columns is not found, and
    [Exact_search_exhausted] says so by name. *)

module L = Linear_arith

type column = {
  col_input : int;          (* index into the [input list] *)
  col_sign : int;           (* +1, or -1 for an [Eq] input's negative half *)
  col_form : L.t;           (* the linear form, sign already applied *)
  col_strict : bool;        (* an [Lt] input (LRA only; LIA folds Lt into Le) *)
}

let columns_of_inputs (inputs : input list) : column list =
  List.concat
    (List.mapi (fun i (inp : input) ->
       match inp.compiled with
       | Farkas.Le f ->
         [ { col_input = i; col_sign = 1; col_form = f; col_strict = false } ]
       | Farkas.Lt f ->
         [ { col_input = i; col_sign = 1; col_form = f; col_strict = true } ]
       | Farkas.Eq f ->
         [ { col_input = i; col_sign = 1; col_form = f; col_strict = false };
           { col_input = i; col_sign = -1; col_form = L.neg f;
             col_strict = false } ])
       inputs)

(** Exact reduced row echelon form, in place. Returns the pivot columns in
    increasing order. Pure rational arithmetic — no rounding anywhere, which
    is the point: a witness coefficient of 262144 must come out as 262144. *)
let rref (a : L.rational array array) (nrows : int) (ncols : int) : int list =
  let pivots = ref [] in
  let r = ref 0 in
  for c = 0 to ncols - 1 do
    if !r < nrows then begin
      let p = ref (-1) in
      for i = nrows - 1 downto !r do
        if not (L.rat_is_zero a.(i).(c)) then p := i
      done;
      if !p >= 0 then begin
        let tmp = a.(!r) in a.(!r) <- a.(!p); a.(!p) <- tmp;
        let inv = L.rat_inv a.(!r).(c) in
        for j = 0 to ncols - 1 do
          a.(!r).(j) <- L.rat_mul inv a.(!r).(j)
        done;
        for i = 0 to nrows - 1 do
          if i <> !r && not (L.rat_is_zero a.(i).(c)) then begin
            let f = a.(i).(c) in
            for j = 0 to ncols - 1 do
              a.(i).(j) <- L.rat_sub a.(i).(j) (L.rat_mul f a.(!r).(j))
            done
          end
        done;
        pivots := c :: !pivots;
        incr r
      end
    end
  done;
  List.rev !pivots

(** Null-space basis of [a] (destroyed). One vector per free column. *)
let nullspace (a : L.rational array array) (nrows : int) (ncols : int)
  : L.rational array list =
  let pivots = rref a nrows ncols in
  let pivot_arr = Array.of_list pivots in
  let is_pivot = Array.make ncols false in
  List.iter (fun c -> is_pivot.(c) <- true) pivots;
  let free = List.filter (fun c -> not is_pivot.(c))
      (List.init ncols (fun i -> i)) in
  List.map (fun f ->
    let v = Array.make ncols L.rat_zero in
    v.(f) <- L.rat_one;
    Array.iteri (fun i p -> v.(p) <- L.rat_neg a.(i).(f)) pivot_arr;
    v) free

(** Clear denominators and divide out the gcd: the primitive integer vector on
    the same ray. [None] only for the zero vector. Positive rescaling changes
    neither the sign discipline nor the sign of the constant part, so this
    normalization is free. *)
let primitive (v : L.rational array) : Z.t array option =
  let den = Array.fold_left
      (fun acc (r : L.rational) -> Z.lcm acc r.den) Z.one v in
  let ints = Array.map
      (fun (r : L.rational) -> Z.divexact (Z.mul r.num den) r.den) v in
  let g = Array.fold_left (fun acc z -> Z.gcd acc z) Z.zero ints in
  if Z.equal g Z.zero then None
  else Some (Array.map (fun z -> Z.divexact z g) ints)

(** Count of support sets of size 1..[max_exact_support] over [n] columns,
    SATURATED AT [max_exact_supports + 1] and overflow-safe at every [n].

    The predecessor saturated the running total but kept building the exact
    binomial `C(n,k)` in machine integers, so a large column count wrapped:
    `support_count 80000` returned -599304339613513951, which then passed the
    `> max_exact_supports` admission check and let the search run with no cap
    at all (R6 checkpoint-2 review, finding 1). Every multiplication is now
    guarded BEFORE it happens, and the loop stops the moment the count is
    known to exceed the cap — there is never a reason to compute the exact
    size of a space we have already refused. *)
let support_count (n : int) : int =
  let cap = max_exact_supports in
  let over = ref false in
  let total = ref 0 in
  let c = ref 1 in                       (* C(n, k-1) *)
  let k = ref 1 in
  while (not !over) && !k <= max_exact_support && !k <= n do
    let factor = n - !k + 1 in
    if factor > 0 && !c > max_int / factor then over := true
    else begin
      c := !c * factor / !k;             (* exact: C(n,k-1)*(n-k+1) = C(n,k)*k *)
      if !c > cap then over := true
      else begin
        total := !total + !c;
        if !total > cap then over := true
      end
    end;
    incr k
  done;
  if !over then cap + 1 else !total

(** Test one candidate ray against the sign discipline and the fragment's
    contradiction condition, and, if it passes, recombine the split equality
    columns into per-input coefficients and emit the witness JSON. *)
let ray_to_witness ~(lra : bool) ~(inputs : input list)
    ~(cols : column array) ~(support : int array) (u : Z.t array)
  : Yojson.Safe.t option =
  let n = Array.length support in
  let ok = ref true in
  for j = 0 to n - 1 do
    if Z.sign u.(j) < 0 then ok := false
  done;
  if not !ok then None
  else begin
    let k = ref L.rat_zero in
    let has_strict = ref false in
    for j = 0 to n - 1 do
      if Z.sign u.(j) > 0 then begin
        let col = cols.(support.(j)) in
        if col.col_strict then has_strict := true;
        k := L.rat_add !k
            (L.rat_mul (L.mk_rat_z u.(j) Z.one) col.col_form.L.const)
      end
    done;
    let contradictory =
      if lra then L.rat_is_pos !k || (L.rat_is_zero !k && !has_strict)
      else L.rat_is_pos !k
    in
    if not contradictory then None
    else begin
      (* mu_plus - mu_minus per input; an Eq input whose two halves cancel
         drops out entirely. *)
      let per_input = Array.make (List.length inputs) Z.zero in
      for j = 0 to n - 1 do
        let col = cols.(support.(j)) in
        let signed =
          if col.col_sign >= 0 then u.(j) else Z.neg u.(j) in
        per_input.(col.col_input) <- Z.add per_input.(col.col_input) signed
      done;
      let names = Array.of_list (List.map (fun (i : input) -> i.name) inputs) in
      let entries = ref [] in
      Array.iteri (fun i z ->
        if not (Z.equal z Z.zero) then
          entries := `Assoc [
            "hypothesis", `String names.(i);
            "coefficient", `String (Z.to_string z) ] :: !entries)
        per_input;
      match List.rev !entries with
      | [] -> None
      | es -> Some (`Assoc [ "coefficients", `List es ])
    end
  end

(** Rows of [A_S]: the variables occurring in the support's columns, with the
    row index each one gets. Built with a hash table and one pass over each
    column's (already sorted, already sparse) coefficient list.

    The predecessor collected variables with [List.mem] and then filled the
    matrix with [List.assoc_opt] per (row, column) — O(rows x k x |coeffs|)
    per support, which on forms carrying 64 variables each is ~16,000 list
    steps per support and, over a 180,000-support sweep, the difference
    between a fraction of a second and half a minute (R6 checkpoint-2 review,
    finding 2). *)
let support_rows ~(cols : column array) (support : int array)
  : (string, int) Hashtbl.t * int =
  let tbl = Hashtbl.create 32 in
  let n = ref 0 in
  Array.iter (fun ci ->
    List.iter (fun (v, _) ->
      if not (Hashtbl.mem tbl v) then begin
        Hashtbl.replace tbl v !n; incr n
      end) cols.(ci).col_form.L.coeffs) support;
  tbl, !n

(** One support set: build [A_S], take its null space, and test the ray when
    the nullity is exactly 1. See the header for why other nullities are
    skipped. Returns the witness (if any) and the WORK this support cost, in
    the units [max_exact_work] is denominated in. *)
let try_support ~(lra : bool) ~(inputs : input list) ~(cols : column array)
    ~(bit_weight : int) (support : int array)
  : Yojson.Safe.t option * int =
  let k = Array.length support in
  let row_of, nrows = support_rows ~cols support in
  (* Gaussian elimination on an nrows x k matrix is ~nrows*k^2 field
     operations, and each operation's cost grows with the operands' size;
     [bit_weight] carries the latter. *)
  let work = (nrows + 1) * k * k * bit_weight in
  let a = Array.init (max nrows 1) (fun _ -> Array.make k L.rat_zero) in
  Array.iteri (fun j ci ->
    List.iter (fun (v, c) ->
      match Hashtbl.find_opt row_of v with
      | Some r -> a.(r).(j) <- c
      | None -> ()) cols.(ci).col_form.L.coeffs) support;
  let basis = if nrows = 0
    then (* no variables at all: every multiplier is free *)
      List.init k (fun f ->
        let v = Array.make k L.rat_zero in v.(f) <- L.rat_one; v)
    else nullspace a nrows k in
  let found = match basis with
    | [ u ] ->
      (match primitive u with
       | None -> None
       | Some ints ->
         (match ray_to_witness ~lra ~inputs ~cols ~support ints with
          | Some w -> Some w
          | None ->
            let neg = Array.map Z.neg ints in
            ray_to_witness ~lra ~inputs ~cols ~support neg))
    | _ -> None
  in
  found, work

(** Exact recovery over [ir]. See the header for the algorithm and for what
    "complete" means here. Returns the same witness JSON shape as
    [try_close], so callers are unchanged. *)
let try_close_exact (ir : Ir.t) : (Yojson.Safe.t, error) result =
  let inputs = compile_inputs ir in
  if inputs = [] then Error No_compilable_inputs
  else
    let lra = String.equal (Farkas.effective_fragment ir) "LRA" in
    let cols = Array.of_list (columns_of_inputs inputs) in
    let n = Array.length cols in
    let budget = support_count n in
    if budget > max_exact_supports then
      Error (Exact_search_space_exceeded
               { max_support = max_exact_support; supports = budget })
    else begin
      (* Size of the numbers the elimination will be carrying, from the inputs.
         One pass, before any support is examined. *)
      let bit_weight =
        let maxbits = ref 1 in
        let note (z : Z.t) =
          let b = Z.numbits (Z.abs z) in if b > !maxbits then maxbits := b in
        Array.iter (fun c ->
          List.iter (fun (_, (r : L.rational)) -> note r.num; note r.den)
            c.col_form.L.coeffs;
          note c.col_form.L.const.num; note c.col_form.L.const.den) cols;
        1 + !maxbits / 64
      in
      let examined = ref 0 in
      let work = ref 0 in
      let found = ref None in
      let exhausted_budget = ref false in
      let buf = Array.make max_exact_support 0 in
      let stop () = !found <> None || !exhausted_budget in
      let rec choose k start depth =
        if stop () then ()
        else if depth = k then begin
          incr examined;
          let support = Array.sub buf 0 k in
          let w, cost = try_support ~lra ~inputs ~cols ~bit_weight support in
          work := !work + cost;
          (match w with Some w -> found := Some w | None -> ());
          if !found = None && !work > max_exact_work then
            exhausted_budget := true
        end else
          for i = start to n - k + depth do
            if not (stop ()) then begin
              buf.(depth) <- i;
              choose k (i + 1) (depth + 1)
            end
          done
      in
      let k = ref 1 in
      while not (stop ()) && !k <= max_exact_support && !k <= n do
        choose !k 0 0;
        incr k
      done;
      match !found with
      | Some w -> Ok w
      | None when !exhausted_budget ->
        Error (Exact_search_work_exceeded
                 { supports_examined = !examined; work = !work })
      | None ->
        Error (Exact_search_exhausted
                 { max_support = max_exact_support; supports = !examined })
    end

(** The enumerating search, then exact recovery where it came up empty.
    THIS is what the adapters call. [try_close] itself is untouched, so the
    unit tests that pin its first-hit order still pin exactly that. *)
let try_close_then_exact ?bound (ir : Ir.t) : (Yojson.Safe.t, error) result =
  match try_close ?bound ir with
  | Ok w -> Ok w
  | Error _ -> try_close_exact ir

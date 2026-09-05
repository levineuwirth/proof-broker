(** Unit tests for [Farkas_search].

    Coverage:
    * Closes the example1 LIA shape ([n + m = 10, 0 <= m, ⊢ n <= 10])
      that cvc5 closes via theory rewrites with no la_generic. The
      witness must verify under [Farkas.verify] against the same IR.
    * Closes a similar LRA shape ([0 <= x, x <= -1] is inconsistent).
    * Returns [Search_exhausted] on a satisfiable IR.
    * Returns [No_compilable_inputs] when no hypothesis (and no
      neg_goal) compiles to a Farkas-amenable form.
    * Pinned bound: [bound = 0] never finds anything. *)

open Proof_broker

let lia_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LIA";
  decidable_theory = None;
}

let lra_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LRA";
  decidable_theory = None;
}

let mk_ir ?(logic = lia_logic) ?(free_vars = []) ?(hypotheses = [])
          (goal_shell : Ir.shell_term) : Ir.t = {
  ir_version = "1.0";
  source_system = { name = "test"; version = "0.0" };
  tier = "goal";
  logic_classification = logic;
  goal = { shell = goal_shell; payloads = None };
  context = { type_vars = []; free_vars; hypotheses; library_slice = None };
  type_metadata = [];
  definitional_metadata = [];
  library_provenance = [];
  user_directives = None;
}

(** [n + m = 10, 0 <= m, ⊢ n <= 10] — example1's Farkas shape, with
    typeclass-flavored symbols [HAdd.hAdd] / [LE.le] that
    [Linear_arith.linearize] already recognizes. *)
let example1_like_ir () =
  let n : Ir.shell_term = Var { name = "n" } in
  let m : Ir.shell_term = Var { name = "m" } in
  let zero : Ir.shell_term = Num_lit { value = "0"; ty = "Int" } in
  let ten : Ir.shell_term = Num_lit { value = "10"; ty = "Int" } in
  let n_plus_m : Ir.shell_term =
    App { symbol = "HAdd.hAdd"; type_args = []; args = [ n; m ] }
  in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = Eq { ty = "Int"; left = n_plus_m; right = ten };
  } in
  let h3 : Ir.hypothesis = {
    name = "h3";
    shell = App { symbol = "LE.le"; type_args = []; args = [ zero; m ] };
  } in
  mk_ir
    ~free_vars:[ { name = "n"; ty = "Int" }; { name = "m"; ty = "Int" } ]
    ~hypotheses:[ h1; h3 ]
    (App { symbol = "LE.le"; type_args = []; args = [ n; ten ] })

(** [x <= 0, x >= 1, ⊢ False] — needs a strict-witness path under
    LRA. *)
let lra_inconsistent_ir () =
  let x : Ir.shell_term = Var { name = "x" } in
  let zero : Ir.shell_term = Num_lit { value = "0"; ty = "Real" } in
  let one : Ir.shell_term = Num_lit { value = "1"; ty = "Real" } in
  let h_low : Ir.hypothesis = {
    name = "h_low";
    shell = App { symbol = "<="; type_args = []; args = [ x; zero ] };
  } in
  let h_high : Ir.hypothesis = {
    name = "h_high";
    shell = App { symbol = ">="; type_args = []; args = [ x; one ] };
  } in
  mk_ir
    ~logic:lra_logic
    ~free_vars:[ { name = "x"; ty = "Real" } ]
    ~hypotheses:[ h_low; h_high ]
    (Const { name = "False" })

(** No useful hypotheses, satisfiable goal: [⊢ x <= 10] with no
    constraints on [x]. *)
let satisfiable_lia_ir () =
  let n : Ir.shell_term = Var { name = "n" } in
  let ten : Ir.shell_term = Num_lit { value = "10"; ty = "Int" } in
  mk_ir
    ~free_vars:[ { name = "n"; ty = "Int" } ]
    (App { symbol = "LE.le"; type_args = []; args = [ n; ten ] })

(** A non-arithmetic goal whose shell can't compile to a Farkas
    form, with no compilable hypotheses either. *)
let non_arithmetic_ir () =
  mk_ir (Const { name = "P" })

(* --- tests --------------------------------------------------------- *)

let test_close_example1_like () =
  let ir = example1_like_ir () in
  match Farkas_search.try_close ir with
  | Error e ->
    Alcotest.fail (Printf.sprintf "expected Ok witness, got %s — %s"
                     (Farkas_search.kind_of_error e)
                     (Farkas_search.detail_of_error e))
  | Ok witness ->
    (match Farkas.verify ir witness with
     | Verified -> ()
     | other ->
       let kind = match other with
         | Verified -> "Verified"
         | Unknown_hypothesis _ -> "Unknown_hypothesis"
            | Duplicate_hypothesis _ -> "Duplicate_hypothesis"
         | Nonlinear _ -> "Nonlinear"
         | Bad_coefficient _ -> "Bad_coefficient"
         | Negative_coefficient _ -> "Negative_coefficient"
         | Not_contradictory _ -> "Not_contradictory"
         | Malformed_witness _ -> "Malformed_witness"
       in
       Alcotest.fail
         (Printf.sprintf "Farkas.verify rejected the discovered \
                          witness: %s; witness=%s"
            kind (Yojson.Safe.to_string witness)))

let test_close_lra_inconsistent () =
  let ir = lra_inconsistent_ir () in
  match Farkas_search.try_close ir with
  | Error e ->
    Alcotest.fail (Printf.sprintf "expected Ok witness, got %s — %s"
                     (Farkas_search.kind_of_error e)
                     (Farkas_search.detail_of_error e))
  | Ok witness ->
    (match Farkas.verify ir witness with
     | Verified -> ()
     | other ->
       let kind = match other with
         | Verified -> "Verified"
         | _ -> "<other>"
       in
       Alcotest.fail
         (Printf.sprintf "Farkas.verify rejected LRA witness: %s; \
                          witness=%s"
            kind (Yojson.Safe.to_string witness)))

let test_satisfiable_returns_search_exhausted () =
  let ir = satisfiable_lia_ir () in
  match Farkas_search.try_close ir with
  | Ok w ->
    Alcotest.fail (Printf.sprintf "expected Error, got Ok witness=%s"
                     (Yojson.Safe.to_string w))
  | Error Search_exhausted -> ()
  | Error e ->
    Alcotest.fail (Printf.sprintf "expected Search_exhausted, got %s"
                     (Farkas_search.kind_of_error e))

let test_no_compilable_inputs () =
  let ir = non_arithmetic_ir () in
  match Farkas_search.try_close ir with
  | Ok _ -> Alcotest.fail "expected Error, got Ok"
  | Error No_compilable_inputs -> ()
  | Error e ->
    Alcotest.fail (Printf.sprintf "expected No_compilable_inputs, got %s"
                     (Farkas_search.kind_of_error e))

let test_search_uses_effective_fragment_on_real_typed_lia_label () =
  (* Mint-then-verify round trip: build a Real-typed counterexample
     IR mislabeled "LIA". Goal: x <= 0, h: x = 1/2. Over the reals
     this isn't provable. The search must consult the effective
     fragment (LRA, derived from term types) and refuse to mint a
     witness that exploits the +1 trick — otherwise the verifier,
     which now uses effective_fragment too, would reject the
     minted cert. Either both sides agree it's unprovable, or both
     agree on a sound witness; never search-says-yes /
     verify-says-no. *)
  let x = Ir.Var { name = "x" } in
  let zero = Ir.Num_lit { value = "0"; ty = "Real" } in
  let half = Ir.Num_lit { value = "1/2"; ty = "Real" } in
  let h1 : Ir.hypothesis = {
    name = "h1";
    shell = Eq { ty = "Real"; left = x; right = half };
  } in
  let ir : Ir.t = {
    ir_version = "1.0";
    source_system = { name = "test"; version = "0.0" };
    tier = "goal";
    logic_classification = {
      order = "first_order"; features_used = [];
      first_order_fragment = "LIA";  (* mislabeled *)
      decidable_theory = None;
    };
    goal = {
      shell = App { symbol = "LE.le"; type_args = []; args = [ x; zero ] };
      payloads = None;
    };
    context = { type_vars = [];
                free_vars = [ { name = "x"; ty = "Real" } ];
                hypotheses = [ h1 ];
                library_slice = None };
    type_metadata = []; definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  } in
  match Farkas_search.try_close ir with
  | Error Search_exhausted -> ()
  | Ok witness ->
    (* If the search ever yields a witness here, the verifier MUST
       accept it — otherwise mint and verify disagree. *)
    (match Farkas.verify ir witness with
     | Verified -> ()
     | other ->
       Alcotest.fail (Printf.sprintf
         "search produced witness verifier rejects: %s" (
         match other with
         | Verified -> "verified"
         | Not_contradictory _ -> "not_contradictory"
         | Bad_coefficient _ -> "bad_coefficient"
         | Negative_coefficient _ -> "negative_coefficient"
         | Unknown_hypothesis _ -> "unknown_hypothesis"
            | Duplicate_hypothesis _ -> "duplicate_hypothesis"
         | Nonlinear _ -> "nonlinear"
         | Malformed_witness _ -> "malformed_witness")))
  | Error e ->
    Alcotest.fail (Printf.sprintf "unexpected error %s"
                     (Farkas_search.kind_of_error e))

let test_bound_zero_finds_nothing () =
  let ir = example1_like_ir () in
  match Farkas_search.try_close ~bound:0 ir with
  | Ok _ -> Alcotest.fail "bound=0 should never find a witness"
  | Error Search_exhausted -> ()
  | Error e ->
    Alcotest.fail (Printf.sprintf "expected Search_exhausted, got %s"
                     (Farkas_search.kind_of_error e))

(** [k] Le hypotheses [xi <= i] with goal [y <= 100] over a FRESH
    [y] no hypothesis mentions — every input Farkas-compiles and no
    witness exists (nothing cancels [y] in [neg_goal], so no
    combination is a constant), so a search that runs must sweep the
    whole 4^(k+1) space. The first version of this helper bounded
    [x0] instead, which made the IR REFUTABLE (h0 + neg_goal, both
    coefficient 1) and the cap test's stated rationale false — C4
    ROUND 2 finding 4(b). *)
let many_le_ir (k : int) : Ir.t =
  let hundred : Ir.shell_term = Num_lit { value = "100"; ty = "Int" } in
  let y : Ir.shell_term = Var { name = "y" } in
  let var i : Ir.shell_term = Var { name = Printf.sprintf "x%d" i } in
  let hyps = List.init k (fun i -> ({
    name = Printf.sprintf "h%d" i;
    shell = App { symbol = "LE.le"; type_args = [];
                  args = [ var i;
                           Num_lit { value = string_of_int i; ty = "Int" } ] };
  } : Ir.hypothesis)) in
  let fvs =
    ({ name = "y"; ty = "Int" } : Ir.free_var)
    :: List.init k (fun i ->
        ({ name = Printf.sprintf "x%d" i; ty = "Int" } : Ir.free_var)) in
  mk_ir ~free_vars:fvs ~hypotheses:hyps
    (App { symbol = "LE.le"; type_args = []; args = [ y; hundred ] })

(** The C4 ROUND 1 regression: 13 Farkas-compilable inputs (4^13 ≈
    67M candidates, above the cap) must never be enumerated densely.
    Since the R4-continuation sparse rescue, an over-cap dense space
    is followed by the SPARSE sweep (support ≤ 4: here exactly
    39 + 702 + 7,722 + 57,915 = 66,378 candidates, pinned below), so
    the irrefutable IR now returns the named
    [Sparse_search_exhausted] — still far under a second of CPU,
    which is what catches a regression to dense enumeration. The
    hard refusal (both spaces above the cap) is pinned separately by
    [test_sparse_space_is_capped]. *)
let test_large_input_space_is_capped () =
  let ir = many_le_ir 12 (* + neg_goal = 13 inputs *) in
  let t0 = Sys.time () in
  let result = Farkas_search.try_close ir in
  let dt = Sys.time () -. t0 in
  (match result with
   | Error (Sparse_search_exhausted { max_support; candidates }) ->
     Alcotest.(check int) "support bound" Farkas_search.max_support max_support;
     Alcotest.(check int) "sparse candidate count for 13 inputs at bound 3"
       66378 candidates
   | Ok w -> Alcotest.fail (Printf.sprintf
       "irrefutable 13-input shape found a witness: %s"
       (Yojson.Safe.to_string w))
   | Error e ->
     Alcotest.fail (Printf.sprintf "expected sparse_search_exhausted, got %s"
                      (Farkas_search.kind_of_error e)));
  Alcotest.(check bool)
    (Printf.sprintf "returned in %.3fs CPU (must be << 1s: capped, not enumerated)" dt)
    true (dt < 1.0)

(** Both spaces above the cap: 61 inputs give a sparse space of
    C(61,4)·81 ≈ 42M > 2M, so the search is refused outright with the
    named cap error, immediately. *)
let test_sparse_space_is_capped () =
  let ir = many_le_ir 60 (* + neg_goal = 61 inputs *) in
  let t0 = Sys.time () in
  let result = Farkas_search.try_close ir in
  let dt = Sys.time () -. t0 in
  (match result with
   | Error (Search_space_exceeded { saturated; range_lengths }) ->
     Alcotest.(check bool) "saturating size exceeds the cap"
       true (saturated > Farkas_search.max_candidates);
     Alcotest.(check int) "one range length per input"
       61 (List.length range_lengths)
   | Ok w -> Alcotest.fail (Printf.sprintf
       "irrefutable 61-input shape found a witness: %s"
       (Yojson.Safe.to_string w))
   | Error e ->
     Alcotest.fail (Printf.sprintf "expected search_space_exceeded, got %s"
                      (Farkas_search.kind_of_error e)));
  Alcotest.(check bool)
    (Printf.sprintf "returned in %.3fs CPU (refused, not enumerated)" dt)
    true (dt < 1.0)

(** [many_le_ir k] plus ONE relevant hypothesis [hx : x <= 5] under
    the goal [x <= 10]: the witness is [hx + neg_goal] (support 2)
    buried in k irrelevant bounds. *)
let sparse_rescue_ir (k : int) : Ir.t =
  let base = many_le_ir k in
  let x : Ir.shell_term = Var { name = "x" } in
  let five : Ir.shell_term = Num_lit { value = "5"; ty = "Int" } in
  let ten : Ir.shell_term = Num_lit { value = "10"; ty = "Int" } in
  let hx : Ir.hypothesis = {
    name = "hx";
    shell = App { symbol = "LE.le"; type_args = []; args = [ x; five ] };
  } in
  { base with
    goal = { shell = App { symbol = "LE.le"; type_args = []; args = [ x; ten ] };
             payloads = None };
    context = { base.context with
                free_vars = ({ name = "x"; ty = "Int" } : Ir.free_var)
                            :: base.context.free_vars;
                hypotheses = base.context.hypotheses @ [ hx ] } }

let check_verifies (ir : Ir.t) (witness : Yojson.Safe.t) =
  match Farkas.verify ir witness with
  | Verified -> ()
  | _ ->
    Alcotest.fail
      (Printf.sprintf "Farkas.verify rejected the discovered witness: %s"
         (Yojson.Safe.to_string witness))

(** Names carrying a nonzero coefficient in a search witness. *)
let support_of (witness : Yojson.Safe.t) : string list =
  let open Yojson.Safe.Util in
  witness |> member "coefficients" |> to_list
  |> List.filter_map (fun e ->
      let c = e |> member "coefficient" |> to_string in
      if c = "0" then None
      else Some (e |> member "hypothesis" |> to_string))

(** The rescue on a synthetic 17-input IR (dense space 4^17-scale,
    refused by the dense pass) — the support-2 witness is found,
    verifies, and is exactly [hx; neg_goal]: the first hit is the
    MINIMAL support, by construction of the order. (The live-fixture
    numbers live on the fixture tests below; this one's inputs are
    its own.) *)
let test_sparse_rescue_finds_witness () =
  let ir = sparse_rescue_ir 15 (* 15 irrelevant + hx + neg_goal = 17 *) in
  let inputs = Farkas_search.compile_inputs ir in
  Alcotest.(check int) "17 compiled inputs" 17 (List.length inputs);
  Alcotest.(check bool) "dense space is above the cap (the rescue path)"
    true (Farkas_search.space_size
            (List.map (Farkas_search.range_for ~bound:3) inputs)
          > Farkas_search.max_candidates);
  match Farkas_search.try_close ir with
  | Error e ->
    Alcotest.fail (Printf.sprintf "expected Ok witness, got %s — %s"
                     (Farkas_search.kind_of_error e)
                     (Farkas_search.detail_of_error e))
  | Ok witness ->
    check_verifies ir witness;
    Alcotest.(check (list string)) "support is exactly hx + neg_goal"
      [ "hx"; "neg_goal" ] (List.sort compare (support_of witness))

(** Real verinf context (fixture written by the bridge's own reifier
    on 2026-09-05 from the spike's `lift_cell`, post-normalization):
    the `D1/70` obligation `2^24 + 2·Zmax ≤ P` under all 19
    hypotheses the tactic actually sees. Run through the dispatch
    pipeline (the numeral-definition unfold of `P`), its dense space
    is above the cap and the rescue finds the [hZ + neg_goal] witness
    — before the rescue, every adapter fell to Tier 0 here. *)
let fixture_ir (name : string) : Ir.t =
  let path =
    Filename.concat (Sys.getcwd ()) ("../../../../sdk/test/fixtures/" ^ name)
  in
  Codec.of_json (Yojson.Safe.from_file path)

let test_d1_70_fixture_closes_via_sparse_rescue () =
  let ir, _trace, _hash =
    Dispatch.run_dispatch_pipeline (fixture_ir "ir-verinf-d1-70.json") in
  let inputs = Farkas_search.compile_inputs ir in
  Alcotest.(check bool) "dense space is above the cap"
    true (Farkas_search.space_size
            (List.map (Farkas_search.range_for ~bound:3) inputs)
          > Farkas_search.max_candidates);
  match Farkas_search.try_close ir with
  | Error e ->
    Alcotest.fail (Printf.sprintf "expected Ok witness, got %s — %s"
                     (Farkas_search.kind_of_error e)
                     (Farkas_search.detail_of_error e))
  | Ok witness ->
    check_verifies ir witness;
    Alcotest.(check (list string)) "support is hZ + neg_goal"
      [ "hZ"; "neg_goal" ] (List.sort compare (support_of witness));
    (* Pin the COEFFICIENTS, not just the support — WRITEUP.md's
       worked example states "hZ:2, neg_goal:1" and its preamble
       promises every number a committed artifact (CONTINUATION
       ROUND 3 finding 4b). *)
    let coef name =
      Yojson.Safe.Util.(
        witness |> member "coefficients" |> to_list
        |> List.find_map (fun e ->
             if member "hypothesis" e |> to_string = name
             then Some (member "coefficient" e |> to_string)
             else None))
    in
    Alcotest.(check (option string)) "hZ coefficient" (Some "2") (coef "hZ");
    Alcotest.(check (option string)) "neg_goal coefficient"
      (Some "1") (coef "neg_goal")

(** The STREAMING half of the C4 fix, pinned by memory (C4 ROUND 2
    finding 4(a): restoring materialization with the cap kept left
    every prior test green). A 10-input irrefutable IR (4^10 ≈ 1M
    candidates, under the cap) forces a FULL sweep; streamed, the
    live heap stays O(inputs), where the pre-fix materialized
    product at this size allocates ~30M words of list cells, of which
    ~10M words of high-water growth was OBSERVED under the restored
    mutation (9,871,360 — GC reclaims some mid-build); the 4M-word
    bound sits between that and streaming's noise floor. *)
let test_full_sweep_is_streamed () =
  let ir = many_le_ir 9 (* + neg_goal = 10 inputs, 4^10 space *) in
  Gc.compact ();
  let before = (Gc.quick_stat ()).top_heap_words in
  let t0 = Sys.time () in
  (match Farkas_search.try_close ir with
   | Error Search_exhausted -> ()
   | Ok w -> Alcotest.fail (Printf.sprintf
       "irrefutable 10-input shape found a witness: %s"
       (Yojson.Safe.to_string w))
   | Error e ->
     Alcotest.fail (Printf.sprintf
       "expected a full-sweep Search_exhausted, got %s"
       (Farkas_search.kind_of_error e)));
  let dt = Sys.time () -. t0 in
  let grown = (Gc.quick_stat ()).top_heap_words - before in
  Alcotest.(check bool)
    (Printf.sprintf "heap high-water grew %d words (mutation-observed ~9.9M)" grown)
    true (grown < 4_000_000);
  Alcotest.(check bool)
    (Printf.sprintf "swept 4^10 in %.3fs CPU" dt)
    true (dt < 10.0)

(** Reference oracle for the enumeration ORDER (C4 ROUND 2 finding
    4(c): the order-equivalence claim had no in-repo artifact). This
    is the pre-fix [cartesian], verbatim; the streamed search must
    try assignments in exactly this sequence, so the first-hit
    witness can never change. *)
let cartesian_oracle (ranges : int list list) : int list list =
  List.fold_right (fun r acc ->
    List.concat_map (fun c -> List.map (fun t -> c :: t) acc) r)
    ranges
    [ [] ]

let test_streaming_order_matches_cartesian () =
  let collect ranges =
    let acc = ref [] in
    ignore (Farkas_search.search_first ranges
              ~try_coefs:(fun coefs -> acc := coefs :: !acc; None));
    List.rev !acc
  in
  let cases = [
    [];
    [ [ 0; 1; 2; 3 ] ];
    [ [ -3; -2; -1; 0; 1; 2; 3 ]; [ 0; 1; 2; 3 ]; [ 0; 1; 2; 3 ] ];
    List.init 8 (fun _ -> [ 0; 1; 2; 3 ]);  (* 4^8 = 65536, exhaustive *)
  ] in
  List.iter (fun ranges ->
    let a = cartesian_oracle ranges and b = collect ranges in
    Alcotest.(check bool)
      (Printf.sprintf "order identical over %d candidates" (List.length a))
      true (a = b))
    cases

(** Streaming preserved the materialized product's order (first
    range slowest), so the witness found on the example1 shape is
    bit-identical to what the list-based search returned. *)
let test_streaming_preserves_witness () =
  let ir = example1_like_ir () in
  match Farkas_search.try_close ir with
  | Error e ->
    Alcotest.fail (Printf.sprintf "example1 shape stopped closing: %s"
                     (Farkas_search.kind_of_error e))
  | Ok witness ->
    (match Farkas.verify ir witness with
     | Verified -> ()
     | _ -> Alcotest.fail "witness no longer verifies");
    Alcotest.(check string) "first-hit witness unchanged by streaming"
      {|{"coefficients":[{"hypothesis":"h1","coefficient":"1"},{"hypothesis":"h3","coefficient":"1"},{"hypothesis":"neg_goal","coefficient":"1"}]}|}
      (Yojson.Safe.to_string witness)

let () =
  Alcotest.run "farkas_search" [
    "close", [
      Alcotest.test_case "example1 LIA closes" `Quick test_close_example1_like;
      Alcotest.test_case "LRA inconsistent closes" `Quick test_close_lra_inconsistent;
    ];
    "non-close", [
      Alcotest.test_case "satisfiable returns search_exhausted"
        `Quick test_satisfiable_returns_search_exhausted;
      Alcotest.test_case "no compilable inputs"
        `Quick test_no_compilable_inputs;
      Alcotest.test_case "bound=0 finds nothing"
        `Quick test_bound_zero_finds_nothing;
      Alcotest.test_case "Real-typed IR mislabeled LIA: search agrees with verify"
        `Quick test_search_uses_effective_fragment_on_real_typed_lia_label;
      Alcotest.test_case "sparse rescue finds the buried witness (17 inputs)"
        `Quick test_sparse_rescue_finds_witness;
      Alcotest.test_case "both spaces above the cap: refused (61 inputs)"
        `Quick test_sparse_space_is_capped;
      Alcotest.test_case "verinf D1/70 fixture closes via the sparse rescue"
        `Quick test_d1_70_fixture_closes_via_sparse_rescue;
      Alcotest.test_case "13-input space is capped, not enumerated"
        `Quick test_large_input_space_is_capped;
      Alcotest.test_case "full sweep under the cap is streamed (memory pin)"
        `Quick test_full_sweep_is_streamed;
      Alcotest.test_case "streaming order == cartesian oracle (exhaustive to 4^8)"
        `Quick test_streaming_order_matches_cartesian;
      Alcotest.test_case "streaming preserves the first-hit witness"
        `Quick test_streaming_preserves_witness;
    ];
  ]

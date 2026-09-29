(** Measure the cost of exact recovery, so [max_exact_supports] is a measured
    number rather than an inherited one.

    DIAGNOSTIC ONLY. The unit that matters is the SUPPORT SET, and a support
    is not interchangeable with an enumerated coefficient assignment: it costs
    an exact rational row-reduction of a |vars| x k matrix, not a
    constant-time weighted sum. So the sweep is over witness-free IRs, where
    the search is forced to examine every support it is allowed to.

    The synthetic IRs pair every variable with two hypotheses, so 2-supports
    are rank-deficient and the ray, its primitive normalization, and the sign
    and contradiction checks all actually run — a diagonal system would make
    every support nullity-0 and understate the cost.

    usage: exact_budget.exe [max_inputs]
*)

open Proof_broker
module J = Yojson.Safe

let hyp name shell : Ir.hypothesis = { name; shell }

let num s : Ir.shell_term = Num_lit { value = s; ty = "Int" }
let var n : Ir.shell_term = Var { name = n }
let le a b : Ir.shell_term = App { symbol = "LE.le"; type_args = []; args = [ a; b ] }

let trivial_logic : Ir.logic_classification = {
  order = "first_order";
  first_order_fragment = "LIA";
  features_used = [];
  decidable_theory = None;
}

let add a b : Ir.shell_term =
  App { symbol = "Int.add"; type_args = []; args = [ a; b ] }

(* SHAPE A ("sparse"): n hypotheses `k <= x_j`, two per variable, goal `False`.
   Few variables per form, so every support's matrix is tiny.
   SHAPE B ("dense"): the same count, but each form is a sum of [width]
   variables — the shape the checkpoint-2 review used to show that the support
   cap alone bounds nothing. Both are witness-free, so the whole admitted
   space is swept. *)
let witness_free_ir ?(width = 1) (n : int) : Ir.t =
  let nvars = if width > 1 then width else (n + 1) / 2 in
  let body i =
    if width <= 1 then var (Printf.sprintf "x%d" (i / 2))
    else
      let rec go j acc =
        if j >= width then acc
        else go (j + 1) (add acc (var (Printf.sprintf "x%d" j))) in
      go 1 (var "x0")
  in
  let hyps = List.init n (fun i ->
    hyp (Printf.sprintf "h%d" i) (le (num (string_of_int (- i))) (body i)))
  in
  let free = List.init nvars (fun i ->
    ({ name = Printf.sprintf "x%d" i; ty = "Int" } : Ir.free_var)) in
  {
    ir_version = "1.0";
    source_system = { name = "budget"; version = "0.0" };
    tier = "goal";
    logic_classification = trivial_logic;
    goal = { shell = Const { name = "False" }; payloads = None };
    context = { type_vars = []; free_vars = free; hypotheses = hyps;
                library_slice = None };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

let () =
  let max_n =
    if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 32 in
  Printf.printf "# exact-recovery cost sweep (witness-free IRs, whole space swept)\n";
  Printf.printf "# max_exact_support = %d, max_exact_supports = %d\n\n"
    Farkas_search.max_exact_support Farkas_search.max_exact_supports;
  Printf.printf "%6s %8s %10s %10s %12s  %s\n"
    "inputs" "columns" "supports" "ms" "ms/support" "outcome";
  let width = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 1 in
  Printf.printf "# form width (variables per hypothesis): %d\n" width;
  let n = ref 2 in
  while !n <= max_n do
    let ir = witness_free_ir ~width !n in
    let inputs = Farkas_search.compile_inputs ir in
    let cols = List.length (Farkas_search.columns_of_inputs inputs) in
    let supports = Farkas_search.support_count cols in
    let t0 = Unix.gettimeofday () in
    let r = Farkas_search.try_close_exact ir in
    let ms = (Unix.gettimeofday () -. t0) *. 1000. in
    let outcome = match r with
      | Ok _ -> "UNEXPECTED witness (the IR is meant to be witness-free)"
      | Error e -> Farkas_search.kind_of_error e in
    Printf.printf "%6d %8d %10d %10.1f %12.4f  %s\n"
      !n cols supports ms
      (if supports > 0 then ms /. float_of_int supports else 0.) outcome;
    flush stdout;
    n := !n + 2
  done

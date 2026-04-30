(** Rational arithmetic and linear forms over named variables.

    Supports Tier 1 Farkas verification (spec §6.4): a Farkas
    certificate is a list of nonnegative coefficients (possibly
    rational) on hypotheses, and verification reduces to summing
    [coef * (lhs - rhs)] across hypotheses and checking that the
    residual is a positive constant. Both the coefficients and the
    sum are rationals.

    Rationals are stored canonically: positive denominator, gcd of
    [|num|] and [den] is one, and [zero] is the unique representation
    of 0. Equality is structural.

    Overflow. We use OCaml's native [int], which on 64-bit is 63-bit
    signed. Coefficients in real Farkas certificates are typically
    small integers; pathological certificates with huge numerators
    can overflow. A future graduation to Zarith would lift this
    limitation; for now [Linear_arith.add]/[mul] silently wrap on
    overflow, and Farkas verification of overflowing certificates
    will misreport. Acceptable for v1. *)

(* --- rationals ------------------------------------------------------- *)

type rational = { num : int; den : int }

let rec gcd a b = if b = 0 then a else gcd b (a mod b)

let mk_rat n d =
  if d = 0 then invalid_arg "Linear_arith.mk_rat: zero denominator";
  let n, d = if d < 0 then (-n, -d) else (n, d) in
  let g = gcd (abs n) d in
  if g = 0 then { num = 0; den = 1 }
  else { num = n / g; den = d / g }

let rat_zero = { num = 0; den = 1 }
let rat_one = { num = 1; den = 1 }

let rat_neg r = { r with num = -r.num }

let rat_add a b =
  mk_rat (a.num * b.den + b.num * a.den) (a.den * b.den)

let rat_sub a b = rat_add a (rat_neg b)

let rat_mul a b =
  mk_rat (a.num * b.num) (a.den * b.den)

let rat_is_zero r = r.num = 0
let rat_is_pos r = r.num > 0
let rat_is_neg r = r.num < 0
let rat_is_nonneg r = r.num >= 0

let rat_to_string r =
  if r.den = 1 then string_of_int r.num
  else Printf.sprintf "%d/%d" r.num r.den

(** Parse a rational from a decimal string ["1"], ["-3"], ["1/2"],
    ["-3/4"]. Returns [None] on any parse failure (including a zero
    denominator). Whitespace is not stripped — callers should
    pre-trim. *)
let rat_of_string (s : string) : rational option =
  match String.index_opt s '/' with
  | None ->
    (try Some (mk_rat (int_of_string s) 1)
     with _ -> None)
  | Some i ->
    let n_str = String.sub s 0 i in
    let d_str = String.sub s (i + 1) (String.length s - i - 1) in
    (try
       let n_i = int_of_string n_str in
       let d_i = int_of_string d_str in
       if d_i = 0 then None
       else Some (mk_rat n_i d_i)
     with _ -> None)

(* --- linear forms ---------------------------------------------------- *)

(** A linear form: [Σ c_i * x_i + k] where [x_i] are named variables
    and [c_i], [k] are rationals. [coeffs] is sorted by variable name
    and contains no zero-coefficient entries — the canonical form
    makes structural equality match arithmetic equality. *)
type t = {
  coeffs : (string * rational) list;
  const : rational;
}

let zero = { coeffs = []; const = rat_zero }

let var name = { coeffs = [ (name, rat_one) ]; const = rat_zero }

let const k = { coeffs = []; const = k }

(** Merge two sorted-assoc-list coefficient maps; drop zero entries. *)
let rec merge_coeffs la lb =
  match la, lb with
  | [], _ -> lb
  | _, [] -> la
  | (na, ca) :: ta, (nb, cb) :: tb ->
    let c = String.compare na nb in
    if c < 0 then (na, ca) :: merge_coeffs ta lb
    else if c > 0 then (nb, cb) :: merge_coeffs la tb
    else
      let s = rat_add ca cb in
      if rat_is_zero s then merge_coeffs ta tb
      else (na, s) :: merge_coeffs ta tb

let add a b = {
  coeffs = merge_coeffs a.coeffs b.coeffs;
  const = rat_add a.const b.const;
}

let neg a = {
  coeffs = List.map (fun (n, c) -> (n, rat_neg c)) a.coeffs;
  const = rat_neg a.const;
}

let sub a b = add a (neg b)

let scale k a =
  if rat_is_zero k then zero
  else {
    coeffs = List.map (fun (n, c) -> (n, rat_mul k c)) a.coeffs;
    const = rat_mul k a.const;
  }

let is_constant a = a.coeffs = []

let constant_value a = a.const

let to_string a =
  let parts =
    List.map (fun (n, c) ->
      if c = rat_one then n
      else if c = rat_neg rat_one then "-" ^ n
      else rat_to_string c ^ "*" ^ n)
      a.coeffs
  in
  let parts = parts @
    (if rat_is_zero a.const then []
     else [ rat_to_string a.const ])
  in
  match parts with
  | [] -> "0"
  | xs -> String.concat " + " xs

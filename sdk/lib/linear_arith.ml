(** Rational arithmetic and linear forms over named variables.

    Supports Tier 1 Farkas verification (spec §6.4): a Farkas
    certificate is a list of nonnegative coefficients (possibly
    rational) on hypotheses, and verification reduces to summing
    [coef * (lhs - rhs)] across hypotheses and checking that the
    residual is a positive constant. Both the coefficients and the
    sum are rationals.

    Rationals are stored canonically: positive denominator, gcd of
    [|num|] and [den] is one, and [zero] is the unique representation
    of 0. Equality is structural — Zarith's [Z.t] interoperates
    cleanly with OCaml's polymorphic [(=)].

    Numerator and denominator are arbitrary-precision integers
    ([Zarith.Z.t]). Real Farkas certificates almost always use small
    coefficients, but pathological inputs (e.g. a synthetic IR with
    a huge constant, or a backend that scales its witness through
    a 100-digit multiplier) used to overflow OCaml's 63-bit native
    int and silently misreport. With Z.t backing, [add], [mul], and
    [scale] are exact at any magnitude. The price is a small
    constant-factor allocation overhead, which is below noise for
    Farkas-shaped certs (a few hundred operations per cert). *)

(* --- rationals ------------------------------------------------------- *)

type rational = { num : Z.t; den : Z.t }

(** Internal canonicalizer: ensure den is positive, drop the gcd of
    |num| and den, and normalize the representation of zero to
    [{num = 0; den = 1}]. Raises [Invalid_argument] on a zero
    denominator. *)
let mk_rat_z (n : Z.t) (d : Z.t) : rational =
  if Z.equal d Z.zero then
    invalid_arg "Linear_arith.mk_rat: zero denominator";
  let n, d = if Z.sign d < 0 then (Z.neg n, Z.neg d) else (n, d) in
  if Z.equal n Z.zero then { num = Z.zero; den = Z.one }
  else
    let g = Z.gcd (Z.abs n) d in
    { num = Z.div n g; den = Z.div d g }

(** Convenience constructor from native int operands. Most callers
    use small integer coefficients ([mk_rat 3 1], [mk_rat (-1) 2]),
    so keeping the int-input signature avoids a [Z.of_int] sprinkle
    at every call site. Big-integer construction (e.g. parsing a
    100-digit numerator from JSON) goes through [mk_rat_z]. *)
let mk_rat (n : int) (d : int) : rational =
  mk_rat_z (Z.of_int n) (Z.of_int d)

let rat_zero = { num = Z.zero; den = Z.one }
let rat_one = { num = Z.one; den = Z.one }

let rat_neg (r : rational) : rational = { r with num = Z.neg r.num }

let rat_add (a : rational) (b : rational) : rational =
  mk_rat_z
    (Z.add (Z.mul a.num b.den) (Z.mul b.num a.den))
    (Z.mul a.den b.den)

let rat_sub (a : rational) (b : rational) : rational = rat_add a (rat_neg b)

let rat_mul (a : rational) (b : rational) : rational =
  mk_rat_z (Z.mul a.num b.num) (Z.mul a.den b.den)

(** Multiplicative inverse. Raises on zero, since [1/0] is undefined
    and surfacing the error eagerly is preferable to silently
    producing a malformed [{num = 1; den = 0}]. Used by the
    Farkas-witness scaling step in [Alethe_farkas] and [Verifier]
    to recover an IR coefficient from a cvc5-side scale factor. *)
let rat_inv (r : rational) : rational =
  if Z.equal r.num Z.zero then invalid_arg "Linear_arith.rat_inv: zero"
  else mk_rat_z r.den r.num

let rat_is_zero (r : rational) : bool = Z.equal r.num Z.zero
let rat_is_pos (r : rational) : bool = Z.sign r.num > 0
let rat_is_neg (r : rational) : bool = Z.sign r.num < 0
let rat_is_nonneg (r : rational) : bool = Z.sign r.num >= 0

let rat_to_string (r : rational) : string =
  if Z.equal r.den Z.one then Z.to_string r.num
  else Printf.sprintf "%s/%s" (Z.to_string r.num) (Z.to_string r.den)

(** Parse a rational from one of the SMT-LIB-flavored formats:
    integer ["1"], ["-3"]; explicit rational ["1/2"], ["-3/4"]; or
    SMT-LIB Real decimal ["3.0"], ["-1.25"]. Returns [None] on any
    parse failure (including a zero denominator). Whitespace is
    not stripped — callers should pre-trim. Magnitudes are
    arbitrary (Zarith [Z.of_string]); a 100-digit literal parses
    cleanly.

    Decimal handling: [I.F] is read as [(I·10^|F| + F) / 10^|F|],
    with the sign hoisted from [I]. This means [3.0] returns
    [3/1], [-1.25] returns [-5/4], and [.5] returns [1/2].
    Without this, z3-emitted Real-typed atoms ([(<= x 3.0)])
    silently parse as variable names rather than constants on the
    Alethe-Sexp side, which broke alignment against Real-typed IR
    hypotheses. *)
let rat_of_string (s : string) : rational option =
  match String.index_opt s '/' with
  | Some i ->
    let n_str = String.sub s 0 i in
    let d_str = String.sub s (i + 1) (String.length s - i - 1) in
    (try
       let n = Z.of_string n_str in
       let d = Z.of_string d_str in
       if Z.equal d Z.zero then None
       else Some (mk_rat_z n d)
     with _ -> None)
  | None ->
    (match String.index_opt s '.' with
     | None ->
       (try Some (mk_rat_z (Z.of_string s) Z.one)
        with _ -> None)
     | Some j ->
       let int_part = String.sub s 0 j in
       let frac_part = String.sub s (j + 1) (String.length s - j - 1) in
       (* Sign-hoist: leading '-' (or '+') belongs on the whole rational,
          not on the fractional digits. We strip it from int_part and
          re-apply at the end. *)
       let sign, int_digits =
         if String.length int_part > 0 && int_part.[0] = '-' then
           (Z.minus_one, String.sub int_part 1 (String.length int_part - 1))
         else if String.length int_part > 0 && int_part.[0] = '+' then
           (Z.one, String.sub int_part 1 (String.length int_part - 1))
         else
           (Z.one, int_part)
       in
       (try
          let int_z =
            if int_digits = "" then Z.zero else Z.of_string int_digits
          in
          let frac_len = String.length frac_part in
          let frac_z =
            if frac_len = 0 then Z.zero else Z.of_string frac_part
          in
          let den = Z.pow (Z.of_int 10) frac_len in
          let num_unsigned = Z.add (Z.mul int_z den) frac_z in
          let num = Z.mul sign num_unsigned in
          if Z.equal den Z.zero then None
          else Some (mk_rat_z num den)
        with _ -> None))

(** Clear denominators across a list of (label, rational) entries.
    Computes the LCM of all denominators, scales every numerator by
    (LCM / den), returning an integer-coefficient list and the LCM
    scale factor.

    Used by the term-mode closers to convert solver-emitted rational
    Farkas witnesses into the integer-coefficient form their
    universe-polymorphic builders expect. Soundness: multiplying
    every coefficient in a Farkas combination by a single positive
    constant [D] (a) preserves each premise's compiled non-positivity
    ([D * c_i >= 0] for [c_i >= 0]; products [D*c_i*a_i] still
    satisfy [<= 0]); (b) scales the linear sum by [D] uniformly
    ([D*K] has the same sign as [K]); (c) preserves strictness state
    in the strict-aware fold (premise strictness is independent of
    its coefficient). The closer's contradiction step uses the
    scaled K, which differs from the original only by a positive
    multiplicative factor.

    Returns [(scaled_entries, lcd)] where each [(label, n)] has
    [n = num * (lcd / den)] for the original entry's rational
    [num / den], and [lcd] is the LCM of all denominators. *)
let clear_denominators_list (entries : (string * rational) list)
  : (string * Z.t) list * Z.t =
  let lcd =
    List.fold_left
      (fun acc (_, r) -> Z.lcm acc r.den)
      Z.one entries
  in
  let scaled =
    List.map
      (fun (label, r) -> (label, Z.mul r.num (Z.div lcd r.den)))
      entries
  in
  (scaled, lcd)

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

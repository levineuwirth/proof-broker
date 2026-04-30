(** Tier 1 Farkas verification (spec §6.4).

    A Farkas certificate is a list of coefficients on hypotheses
    whose weighted sum produces a contradiction for [¬G]. Verification
    proceeds by:

    1. Parsing each cert coefficient as a rational.
    2. Looking up the named hypothesis in the IR (or, for the
       reserved name [neg_goal], constructing the negated goal).
    3. Compiling the hypothesis to a [Le] or [Eq] linear form.
    4. Multiplying each form by its coefficient and summing.
    5. Verifying the residual is a strictly-positive constant — that
       is, the weighted combination yields [c <= 0] with [c > 0],
       which is the contradiction.

    Sign convention. Coefficients on inequality (Le) hypotheses must
    be nonnegative — Farkas' lemma is unsound otherwise. Coefficients
    on equality (Eq) hypotheses may be any rational; multiplying an
    equality [a = b] by [-c] gives [c * (b - a) = 0], which is also
    a valid contribution. The spec text says "nonnegative" but that
    only constrains the inequality case; equalities are signed by
    convention. We surface a per-hypothesis violation
    ([Negative_coefficient]) only when the coefficient sign is wrong
    for that hypothesis's term shape.

    Fragment scope. The +1 trick for [¬(a <= b) ≡ b + 1 <= a] is
    Z-specific (LIA). For LRA we'd need strict-inequality witnesses,
    which require a slightly different residual check. v1 supports
    LIA only; LRA Farkas is a follow-up. We don't gate on the cert's
    [refinement_record.fragment] because the linearizer ignores
    types — but a future LRA Farkas verifier will need to dispatch
    on fragment.

    Linearization scope. The linearizer recognizes the LIA shell
    vocabulary: [HAdd.hAdd]/[Int.add]/[Add.add],
    [HSub.hSub]/[Int.sub]/[Sub.sub], [HMul.hMul]/[Int.mul]/[Mul.mul]
    (only when one factor is a constant — the form must stay
    linear), [Neg.neg]/[Int.neg], [Var], [NumLit]. Anything else
    yields [Nonlinear]. Under refinement, methods like [HAdd.hAdd]
    typically become primitive [Int.add]; we accept both so the
    verifier works pre- and post-refinement. *)

type verdict =
  | Verified
  | Unknown_hypothesis of { hypothesis : string }
  | Nonlinear of { hypothesis : string; detail : string }
  | Bad_coefficient of { hypothesis : string; raw : string }
  | Negative_coefficient of { hypothesis : string; value : string }
  | Not_contradictory of { residual : string }
  | Malformed_witness of { detail : string }

(* --- linearization --------------------------------------------------- *)

(** Linearize an arithmetic shell term to a [Linear_arith.t]. Returns
    [None] on any non-linear shape (a non-constant multiplication, an
    unknown function symbol, an unsupported node kind). *)
let rec linearize (t : Ir.shell_term) : Linear_arith.t option =
  match t with
  | Var { name } -> Some (Linear_arith.var name)
  | Num_lit { value; _ } ->
    (match Linear_arith.rat_of_string value with
     | Some r -> Some (Linear_arith.const r)
     | None -> None)
  | App { symbol; args; _ } -> linearize_app symbol args
  | _ -> None

and linearize_app symbol args =
  match symbol, args with
  | ("HAdd.hAdd" | "Int.add" | "Add.add" | "+"), [ a; b ] ->
    bin_lin Linear_arith.add a b
  | ("HSub.hSub" | "Int.sub" | "Sub.sub" | "-"), [ a; b ] ->
    bin_lin Linear_arith.sub a b
  | ("HMul.hMul" | "Int.mul" | "Mul.mul" | "*"), [ a; b ] ->
    (match linearize a, linearize b with
     | Some la, Some lb when Linear_arith.is_constant la ->
       Some (Linear_arith.scale (Linear_arith.constant_value la) lb)
     | Some la, Some lb when Linear_arith.is_constant lb ->
       Some (Linear_arith.scale (Linear_arith.constant_value lb) la)
     | _ -> None)
  | ("Neg.neg" | "Int.neg"), [ a ] ->
    (match linearize a with
     | Some la -> Some (Linear_arith.neg la)
     | _ -> None)
  | _ -> None

and bin_lin op a b =
  match linearize a, linearize b with
  | Some la, Some lb -> Some (op la lb)
  | _ -> None

(* --- compiled hypotheses --------------------------------------------- *)

(** A hypothesis compiled to one of the two Farkas-amenable forms.
    [Le f] means [f <= 0]; [Eq f] means [f = 0]. *)
type compiled =
  | Le of Linear_arith.t
  | Eq of Linear_arith.t

(** Compile a hypothesis shell to a [compiled] form. Returns the
    raw [Ir.shell_term] structure as a [Nonlinear] detail if anything
    fails to linearize; this lets the caller surface a useful error
    rather than a generic "couldn't parse". *)
let compile_hypothesis (shell : Ir.shell_term) : (compiled, string) result =
  let lift_pair op a b =
    match linearize a, linearize b with
    | Some la, Some lb -> Ok (op (Linear_arith.sub la lb))
    | _ -> Error "non-linear arithmetic operand"
  in
  match shell with
  | Eq { left; right; _ } ->
    lift_pair (fun f -> Eq f) left right
  | App { symbol = "LE.le"; args = [ a; b ]; _ }
  | App { symbol = "<="; args = [ a; b ]; _ } ->
    lift_pair (fun f -> Le f) a b
  | App { symbol = "GE.ge"; args = [ a; b ]; _ }
  | App { symbol = ">="; args = [ a; b ]; _ } ->
    lift_pair (fun f -> Le f) b a
  | App { symbol = "LT.lt"; args = [ a; b ]; _ }
  | App { symbol = "<"; args = [ a; b ]; _ } ->
    (match linearize a, linearize b with
     | Some la, Some lb ->
       let f = Linear_arith.add (Linear_arith.sub la lb)
                 (Linear_arith.const Linear_arith.rat_one) in
       Ok (Le f)
     | _ -> Error "non-linear arithmetic operand")
  | App { symbol = "GT.gt"; args = [ a; b ]; _ }
  | App { symbol = ">"; args = [ a; b ]; _ } ->
    (match linearize a, linearize b with
     | Some la, Some lb ->
       let f = Linear_arith.add (Linear_arith.sub lb la)
                 (Linear_arith.const Linear_arith.rat_one) in
       Ok (Le f)
     | _ -> Error "non-linear arithmetic operand")
  | Not { operand = App { symbol = "LE.le"; args = [ a; b ]; _ } }
  | Not { operand = App { symbol = "<="; args = [ a; b ]; _ } } ->
    (match linearize a, linearize b with
     | Some la, Some lb ->
       let f = Linear_arith.add (Linear_arith.sub lb la)
                 (Linear_arith.const Linear_arith.rat_one) in
       Ok (Le f)
     | _ -> Error "non-linear arithmetic operand")
  | Not { operand = App { symbol = "LT.lt"; args = [ a; b ]; _ } } ->
    lift_pair (fun f -> Le f) b a
  | _ -> Error "unsupported hypothesis shape"

(* --- main entry ------------------------------------------------------ *)

(** Look up a hypothesis in the IR by name, treating [neg_goal] as
    the negation of the IR's goal. Returns [None] if the name is
    unknown. *)
let lookup_hypothesis (ir : Ir.t) (name : string) : Ir.shell_term option =
  if name = "neg_goal" then
    Some (Ir.Not { operand = ir.goal.shell })
  else
    let rec find = function
      | [] -> None
      | (h : Ir.hypothesis) :: rest ->
        if h.name = name then Some h.shell else find rest
    in
    find ir.context.hypotheses

(** Parse the witness_data JSON into a list of (hypothesis name,
    coefficient string) pairs. The expected shape is
    [{"coefficients": [{"hypothesis": "...", "coefficient": "..."}, ...]}].
    Anything else raises a [Malformed_witness] result via the
    caller. *)
let parse_coefficients (witness : Yojson.Safe.t)
  : (string * string) list option =
  match witness with
  | `Assoc pairs ->
    (match List.assoc_opt "coefficients" pairs with
     | Some (`List xs) ->
       let parse_one (j : Yojson.Safe.t) =
         match j with
         | `Assoc fields ->
           let hyp =
             match List.assoc_opt "hypothesis" fields with
             | Some (`String s) -> Some s
             | _ -> None
           in
           let coef =
             match List.assoc_opt "coefficient" fields with
             | Some (`String s) -> Some s
             | _ -> None
           in
           (match hyp, coef with
            | Some h, Some c -> Some (h, c)
            | _ -> None)
         | _ -> None
       in
       let rec collect acc = function
         | [] -> Some (List.rev acc)
         | x :: xs ->
           (match parse_one x with
            | Some pair -> collect (pair :: acc) xs
            | None -> None)
       in
       collect [] xs
     | _ -> None)
  | _ -> None

(** Run Farkas verification. Returns [Verified] on a valid certificate,
    or one of the failure variants describing what went wrong. *)
let verify (ir : Ir.t) (witness : Yojson.Safe.t) : verdict =
  match parse_coefficients witness with
  | None ->
    Malformed_witness {
      detail = "expected witness_data.coefficients to be array of \
                {hypothesis, coefficient} pairs";
    }
  | Some [] ->
    Malformed_witness { detail = "empty coefficient list" }
  | Some entries ->
    let rec sum_up acc = function
      | [] -> Ok acc
      | (hyp_name, coef_str) :: rest ->
        (match Linear_arith.rat_of_string coef_str with
         | None ->
           Error (Bad_coefficient { hypothesis = hyp_name; raw = coef_str })
         | Some coef ->
           (match lookup_hypothesis ir hyp_name with
            | None ->
              Error (Unknown_hypothesis { hypothesis = hyp_name })
            | Some shell ->
              (match compile_hypothesis shell with
               | Error detail ->
                 Error (Nonlinear { hypothesis = hyp_name; detail })
               | Ok (Le f) ->
                 if not (Linear_arith.rat_is_nonneg coef) then
                   Error (Negative_coefficient {
                     hypothesis = hyp_name;
                     value = Linear_arith.rat_to_string coef;
                   })
                 else
                   let term = Linear_arith.scale coef f in
                   sum_up (Linear_arith.add acc term) rest
               | Ok (Eq f) ->
                 let term = Linear_arith.scale coef f in
                 sum_up (Linear_arith.add acc term) rest)))
    in
    (match sum_up Linear_arith.zero entries with
     | Error r -> r
     | Ok residual ->
       if Linear_arith.is_constant residual
       && Linear_arith.rat_is_pos (Linear_arith.constant_value residual)
       then Verified
       else
         Not_contradictory {
           residual = Linear_arith.to_string residual;
         })

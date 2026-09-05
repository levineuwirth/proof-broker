(** Tier 1 Farkas verification (spec §6.4).

    A Farkas certificate is a list of coefficients on hypotheses
    whose weighted sum produces a contradiction for [¬G]. Verification
    proceeds by:

    1. Parsing each cert coefficient as a rational.
    2. Looking up the named hypothesis in the IR (or, for the
       reserved name [neg_goal], constructing the negated goal).
    3. Compiling the hypothesis to a [Le], [Lt], or [Eq] linear form.
    4. Multiplying each form by its coefficient and summing.
    5. Verifying the residual is a contradictory constant — strictly
       positive in the loose case ([c <= 0] with [c > 0]), or
       non-negative when at least one strict ([Lt]) witness was
       weighted positively ([c < 0] with [c >= 0]).

    Sign convention. Coefficients on inequality ([Le], [Lt])
    hypotheses must be nonnegative — Farkas' lemma is unsound
    otherwise. Coefficients on equality ([Eq]) hypotheses may be any
    rational; multiplying an equality [a = b] by [-c] gives
    [c * (b - a) = 0], which is also a valid contribution. The spec
    text says "nonnegative" but that only constrains the inequality
    case; equalities are signed by convention. We surface a
    per-hypothesis violation ([Negative_coefficient]) only when the
    coefficient sign is wrong for that hypothesis's term shape.

    Fragment scope. Compilation of strict shapes ([LT.lt], [GT.gt],
    [Not(LE.le)]) depends on the fragment: in LIA we apply the +1
    trick ([¬(a <= b) ≡ b + 1 <= a]) which is sound only over Z;
    in LRA we keep strictness explicit as a [Lt] form. The verify
    entry derives the active fragment via [effective_fragment ir]
    rather than reading [logic_classification.first_order_fragment]
    directly: the label is documentation and a Real-typed IR
    mislabeled ["LIA"] would otherwise unlock the +1 trick on the
    reals, where it's unsound. [effective_fragment] returns ["LRA"]
    whenever any free var or numeric literal mentions a [Real]
    type tag, regardless of the declared fragment, and the
    declared fragment otherwise. The linearization vocabulary is
    the same in both modes — the difference is only in how strict
    inequalities compile and how the residual is judged
    contradictory.

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
  | Duplicate_hypothesis of { hypothesis : string }
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
  (* R3-M1: an [Opaque] node is an atomized subterm (the reifier's
     nonlinear-ℕ-product atomization) — a fresh variable keyed by its
     payload id. Sound for Farkas checking: the combination is valid
     for ALL integer values of the atom, in particular the value of
     the term it stands for; the atom's range constraints ride along
     as ordinary hypotheses (the reifier's [_pb_nonneg_*] and the
     user's bounds). *)
  | Opaque { payload_id } -> Some (Linear_arith.var payload_id)
  | App { symbol; args; _ } -> linearize_app symbol args
  | _ -> None

and linearize_app symbol args =
  match symbol, args with
  (* R3-M1 ℕ→ℤ cast transparency: [Int.ofNat t] denotes the same
     integer as its ℕ operand's image, so it linearizes to the
     operand's form. Both bridge reifiers normalize their surface
     cast heads (Lean [Int.ofNat]/[Nat.cast], Rocq [Z.of_nat]) to
     the single IR symbol ["Int.ofNat"]. Sound: the ℕ-ness of the
     atom is carried by the explicit [0 <= Int.ofNat x] nonneg
     hypotheses, not by the cast node — a Farkas combination over
     the atoms is valid over all of ℤ regardless. *)
  | "Int.ofNat", [ a ] -> linearize a
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

(** A hypothesis compiled to one of the three Farkas-amenable forms.
    [Le f] means [f <= 0]; [Lt f] means [f < 0]; [Eq f] means [f = 0]. *)
type compiled =
  | Le of Linear_arith.t
  | Lt of Linear_arith.t
  | Eq of Linear_arith.t

(** Walk a shell term looking for constructs that are well-formed IR
    but inherently outside Farkas's linear-arithmetic reach. Returns a
    short human-readable description of the first such construct found,
    or [None] if the term is structurally compatible (whether or not
    [linearize] currently succeeds on it). Used to enrich
    [compile_hypothesis]'s rejection diagnostic — "conditional
    expression (ite)" beats the generic "non-linear arithmetic operand"
    when something concrete is to blame. Extend the match arms here
    as new gap audits identify additional shapes worth diagnosing
    specifically. *)
let rec contains_unsupported_construct (t : Ir.shell_term) : string option =
  match t with
  | App { symbol = "ite" | "If.ite" | "if" | "ite_then_else"; _ } ->
    Some "conditional expression (ite)"
  | App { args; _ } -> List.find_map contains_unsupported_construct args
  | Not { operand } -> contains_unsupported_construct operand
  | Eq { left; right; _ } ->
    (match contains_unsupported_construct left with
     | Some _ as r -> r
     | None -> contains_unsupported_construct right)
  | _ -> None

(** Pick the most useful error string when both operands of a
    comparison fail to linearize: name the specific Farkas-incompatible
    construct if one is present, otherwise fall back to the generic
    "non-linear arithmetic operand". *)
let nonlinear_reason a b =
  match contains_unsupported_construct a with
  | Some s ->
    Printf.sprintf "%s in operand — Farkas requires linear arithmetic" s
  | None ->
    (match contains_unsupported_construct b with
     | Some s ->
       Printf.sprintf "%s in operand — Farkas requires linear arithmetic" s
     | None -> "non-linear arithmetic operand")

(** Compile a hypothesis shell to a [compiled] form. Returns the
    raw [Ir.shell_term] structure as a [Nonlinear] detail if anything
    fails to linearize; this lets the caller surface a useful error
    rather than a generic "couldn't parse".

    [fragment] selects how strict shapes ([LT.lt], [GT.gt],
    [Not(LE.le)]) compile: ["LRA"] keeps strictness explicit as
    [Lt]; anything else folds it into [Le] via the +1 trick, which
    is sound only over Z. Callers must use [effective_fragment ir]
    rather than the declared fragment label so a Real-typed IR
    mislabeled ["LIA"] doesn't accidentally unlock the +1 trick on
    the reals. *)
let compile_hypothesis ?(fragment = "LIA") (shell : Ir.shell_term)
  : (compiled, string) result =
  let lra = String.equal fragment "LRA" in
  let lift_le_pair a b =
    match linearize a, linearize b with
    | Some la, Some lb -> Ok (Le (Linear_arith.sub la lb))
    | _ -> Error (nonlinear_reason a b)
  in
  let lift_eq_pair a b =
    match linearize a, linearize b with
    | Some la, Some lb -> Ok (Eq (Linear_arith.sub la lb))
    | _ -> Error (nonlinear_reason a b)
  in
  (* Compile [a < b] under the active fragment: strict [Lt(a-b)] for
     LRA, or [Le(a-b+1)] under the LIA +1 trick. *)
  let lift_strict_pair a b =
    match linearize a, linearize b with
    | Some la, Some lb ->
      let f = Linear_arith.sub la lb in
      if lra then Ok (Lt f)
      else
        Ok (Le (Linear_arith.add f
                  (Linear_arith.const Linear_arith.rat_one)))
    | _ -> Error (nonlinear_reason a b)
  in
  match shell with
  | Eq { left; right; _ } ->
    lift_eq_pair left right
  | App { symbol = "LE.le"; args = [ a; b ]; _ }
  | App { symbol = "<="; args = [ a; b ]; _ } ->
    lift_le_pair a b
  | App { symbol = "GE.ge"; args = [ a; b ]; _ }
  | App { symbol = ">="; args = [ a; b ]; _ } ->
    lift_le_pair b a
  | App { symbol = "LT.lt"; args = [ a; b ]; _ }
  | App { symbol = "<"; args = [ a; b ]; _ } ->
    lift_strict_pair a b
  | App { symbol = "GT.gt"; args = [ a; b ]; _ }
  | App { symbol = ">"; args = [ a; b ]; _ } ->
    lift_strict_pair b a
  | Not { operand = App { symbol = "LE.le"; args = [ a; b ]; _ } }
  | Not { operand = App { symbol = "<="; args = [ a; b ]; _ } } ->
    (* ¬(a <= b) ≡ b < a *)
    lift_strict_pair b a
  | Not { operand = App { symbol = "LT.lt"; args = [ a; b ]; _ } }
  | Not { operand = App { symbol = "<"; args = [ a; b ]; _ } } ->
    (* ¬(a < b) ≡ b <= a — same in LIA and LRA, no +1. *)
    lift_le_pair b a
  | Not { operand = App { symbol = "GE.ge"; args = [ a; b ]; _ } }
  | Not { operand = App { symbol = ">="; args = [ a; b ]; _ } } ->
    (* ¬(a >= b) ≡ a < b *)
    lift_strict_pair a b
  | Not { operand = App { symbol = "GT.gt"; args = [ a; b ]; _ } }
  | Not { operand = App { symbol = ">"; args = [ a; b ]; _ } } ->
    (* ¬(a > b) ≡ a <= b *)
    lift_le_pair a b
  | _ -> Error "unsupported hypothesis shape"

(* --- fragment derivation --------------------------------------------- *)

(** True iff any subterm of [t] mentions a [Real] type tag, either
    on a numeric literal or an equality. The check is structural
    so an [Int]-typed term tree returns [false] even when it lives
    in an IR whose [logic_classification.first_order_fragment] is
    misreported. *)
let rec shell_mentions_real (t : Ir.shell_term) : bool =
  match t with
  | Var _ | Const _ -> false
  | Num_lit { ty; _ } -> String.equal ty "Real"
  | Eq { ty; left; right } ->
    String.equal ty "Real"
    || shell_mentions_real left || shell_mentions_real right
  | App { args; _ } -> List.exists shell_mentions_real args
  | And { left; right } | Or { left; right } ->
    shell_mentions_real left || shell_mentions_real right
  | Implies { antecedent; consequent } ->
    shell_mentions_real antecedent || shell_mentions_real consequent
  | Not { operand } -> shell_mentions_real operand
  | Forall { body; _ } | Exists { body; _ } -> shell_mentions_real body
  | Lambda { body; _ } -> shell_mentions_real body
  | Opaque _ -> false

(** Return the arithmetic-mode fragment to use for Farkas /
    Tier 3 reasoning, derived from the actual term and free-var
    types rather than trusting [logic_classification.first_order_fragment]
    blindly. The label is documentation; soundness is governed by
    types. Specifically: if any free var is [Real]-typed, or any
    subterm mentions a [Real] type tag, the effective fragment is
    ["LRA"] — the +1 strict-inequality trick is unsound on Reals
    and must not be applied. Otherwise the declared fragment
    passes through.

    Conservative bias: when in doubt, refuse the +1 trick.
    Rejecting a sound LIA witness because the IR happens to
    mention a stray [Real] tag is a false negative, not a
    soundness break. *)
let effective_fragment (ir : Ir.t) : string =
  let any_real_free_var =
    List.exists (fun (fv : Ir.free_var) -> String.equal fv.ty "Real")
      ir.context.free_vars
  in
  let any_real_term =
    shell_mentions_real ir.goal.shell
    || List.exists (fun (h : Ir.hypothesis) -> shell_mentions_real h.shell)
         ir.context.hypotheses
  in
  if any_real_free_var || any_real_term then "LRA"
  else
    (* Typeclass fixtures with universal type-var metadata leave
       [first_order_fragment] as ["none"] pending refinement; default
       to LIA so the refinement pipeline runs (refinement picks a host
       type per the embedding tags, which is the actual classifier
       for these IRs). Matches the legacy per-adapter [pick_fragment]
       behavior for non-Real IRs. *)
    match ir.logic_classification.first_order_fragment with
    | "" | "none" -> "LIA"
    | frag -> frag

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
    or one of the failure variants describing what went wrong. The
    active fragment comes from [effective_fragment ir] (term-type
    derived, not the [logic_classification] label) and selects
    strict-witness behavior — see [compile_hypothesis]. *)
let verify (ir : Ir.t) (witness : Yojson.Safe.t) : verdict =
  (* Duplicate hypothesis names make by-name resolution ambiguous:
     [lookup_hypothesis] would silently pick the FIRST match while a
     search over the same IR is positional, so a valid witness can be
     rejected as not-contradictory (C4 CONTINUATION ROUND 1 Med 3 —
     two Lean `have := e` both named `this`). Refuse loudly instead;
     the Lean front-end now renames shadowed duplicates before
     reification, so reaching this is a front-end bug or a hand-built
     IR. *)
  let seen = Hashtbl.create 8 in
  let dup =
    List.find_opt (fun (h : Ir.hypothesis) ->
      if Hashtbl.mem seen h.name then true
      else (Hashtbl.add seen h.name (); false))
      ir.context.hypotheses
  in
  match dup with
  | Some h -> Duplicate_hypothesis { hypothesis = h.name }
  | None ->
  let fragment = effective_fragment ir in
  match parse_coefficients witness with
  | None ->
    Malformed_witness {
      detail = "expected witness_data.coefficients to be array of \
                {hypothesis, coefficient} pairs";
    }
  | Some [] ->
    Malformed_witness { detail = "empty coefficient list" }
  | Some entries ->
    (* [has_strict] becomes true the first time a [Lt] form is added
       with a strictly positive coefficient. A zero coef on a strict
       form contributes nothing and does not preserve strictness. *)
    let rec sum_up acc has_strict = function
      | [] -> Ok (acc, has_strict)
      | (hyp_name, coef_str) :: rest ->
        (match Linear_arith.rat_of_string coef_str with
         | None ->
           Error (Bad_coefficient { hypothesis = hyp_name; raw = coef_str })
         | Some coef ->
           (match lookup_hypothesis ir hyp_name with
            | None ->
              Error (Unknown_hypothesis { hypothesis = hyp_name })
            | Some shell ->
              (match compile_hypothesis ~fragment shell with
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
                   sum_up (Linear_arith.add acc term) has_strict rest
               | Ok (Lt f) ->
                 if not (Linear_arith.rat_is_nonneg coef) then
                   Error (Negative_coefficient {
                     hypothesis = hyp_name;
                     value = Linear_arith.rat_to_string coef;
                   })
                 else
                   let term = Linear_arith.scale coef f in
                   let strict' =
                     has_strict || Linear_arith.rat_is_pos coef
                   in
                   sum_up (Linear_arith.add acc term) strict' rest
               | Ok (Eq f) ->
                 let term = Linear_arith.scale coef f in
                 sum_up (Linear_arith.add acc term) has_strict rest)))
    in
    (match sum_up Linear_arith.zero false entries with
     | Error r -> r
     | Ok (residual, has_strict) ->
       if not (Linear_arith.is_constant residual) then
         Not_contradictory { residual = Linear_arith.to_string residual }
       else
         let c = Linear_arith.constant_value residual in
         (* Loose combination: the sum is bounded by [<= 0], so a
            strictly-positive constant contradicts. With a strict
            witness present the sum is bounded by [< 0], so any
            non-negative constant contradicts. *)
         let ok =
           if has_strict then Linear_arith.rat_is_nonneg c
           else Linear_arith.rat_is_pos c
         in
         if ok then Verified
         else Not_contradictory {
           residual = Linear_arith.to_string residual;
         })

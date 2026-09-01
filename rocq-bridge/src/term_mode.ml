module Cert = Proof_broker.Certificate
module Farkas = Proof_broker.Farkas
module L = Proof_broker.Linear_arith
module Ir = Proof_broker.Ir
module Verifier = Proof_broker.Verifier
module Alethe_farkas = Proof_broker.Alethe_farkas

exception Unsupported of string
let unsupported fmt = Printf.ksprintf (fun s -> raise (Unsupported s)) fmt

(* --- Constr lookups ------------------------------------------------ *)

let constr_of_ref s =
  EConstr.of_constr
    (UnivGen.constr_of_monomorphic_global (Global.env ()) (Rocqlib.lib_ref s))

let safe_constr_of_ref s : EConstr.t option =
  try Some (constr_of_ref s) with _ -> None

(* Helpers registered in ProofBrokerTermMode.v. Kept lazy so module
   init doesn't hit Global.env (the same trap the reifier wraps
   around — see the Phase 4 retro). *)

(* Z-typed helpers. *)
let z_le_to_le0       = lazy (safe_constr_of_ref "proof_broker.term_mode.le_to_le0")
let z_ge_to_le0       = lazy (safe_constr_of_ref "proof_broker.term_mode.ge_to_le0")
let z_lt_to_le0       = lazy (safe_constr_of_ref "proof_broker.term_mode.lt_to_le0")
let z_gt_to_le0       = lazy (safe_constr_of_ref "proof_broker.term_mode.gt_to_le0")
let z_eq_to_le0_ref   = lazy (safe_constr_of_ref "proof_broker.term_mode.z_eq_to_le0")
let z_eq_to_le0_flipped_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.z_eq_to_le0_flipped")
let z_not_le_to_le0_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.z_not_le_to_le0")
let z_not_ge_to_le0_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.z_not_ge_to_le0")
let z_not_lt_to_le0_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.z_not_lt_to_le0")
let z_not_gt_to_le0_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.z_not_gt_to_le0")
let r_zero_nonneg_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_zero_nonneg")
let r_lt_to_lt0_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_lt_to_lt0")
let r_gt_to_lt0_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_gt_to_lt0")
let r_mul_pos_neg_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_mul_pos_neg")
let r_add_le_lt_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_add_le_lt")
let r_add_lt_le_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_add_lt_le")
let r_add_neg_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_add_neg")
let r_farkas_contradict_n_strict_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_farkas_contradict_n_strict")
let z_farkas_le_2     = lazy (safe_constr_of_ref "proof_broker.term_mode.farkas_le_2")
let z_pos_is_pos      = lazy (safe_constr_of_ref "proof_broker.term_mode.pos_is_pos")
let z_pos_is_nonneg   = lazy (safe_constr_of_ref "proof_broker.term_mode.pos_is_nonneg")
let z_farkas_contradict_n = lazy (safe_constr_of_ref "proof_broker.term_mode.farkas_contradict_n")
let z_mul_nonneg_nonpos   = lazy (safe_constr_of_ref "proof_broker.term_mode.z_mul_nonneg_nonpos")
let z_add_nonpos          = lazy (safe_constr_of_ref "proof_broker.term_mode.z_add_nonpos")

(* R-typed helpers (mirror of the Z ones for the LRA Tier 1 / Tier 2
   case-split paths). *)
let r_le_to_le0_ref     = lazy (safe_constr_of_ref "proof_broker.term_mode.r_le_to_le0")
let r_ge_to_le0_ref     = lazy (safe_constr_of_ref "proof_broker.term_mode.r_ge_to_le0")
let r_eq_to_le0_ref     = lazy (safe_constr_of_ref "proof_broker.term_mode.r_eq_to_le0")
let r_eq_to_le0_flipped_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_eq_to_le0_flipped")
let r_not_le_to_lt0_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_not_le_to_lt0")
let r_not_ge_to_lt0_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_not_ge_to_lt0")
let r_not_lt_to_le0_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_not_lt_to_le0")
let r_not_gt_to_le0_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_not_gt_to_le0")
let r_farkas_le_2_ref   = lazy (safe_constr_of_ref "proof_broker.term_mode.r_farkas_le_2")
let r_pos_is_pos_ref    = lazy (safe_constr_of_ref "proof_broker.term_mode.r_pos_is_pos")
let r_pos_is_nonneg_ref = lazy (safe_constr_of_ref "proof_broker.term_mode.r_pos_is_nonneg")
let r_farkas_contradict_n_ref = lazy (safe_constr_of_ref "proof_broker.term_mode.r_farkas_contradict_n")
let r_mul_nonneg_nonpos_ref   = lazy (safe_constr_of_ref "proof_broker.term_mode.r_mul_nonneg_nonpos")
let r_add_nonpos_ref          = lazy (safe_constr_of_ref "proof_broker.term_mode.r_add_nonpos")

(* Z + positive constructors for building literal Constr. *)
let r_Z0   = lazy (safe_constr_of_ref "num.Z.Z0")
let r_Zpos = lazy (safe_constr_of_ref "num.Z.Zpos")
let r_Zadd = lazy (safe_constr_of_ref "num.Z.add")
let r_Zsub = lazy (safe_constr_of_ref "num.Z.sub")
let r_Zmul = lazy (safe_constr_of_ref "num.Z.mul")
let r_Zle  = lazy (safe_constr_of_ref "num.Z.le")
let r_Zlt  = lazy (safe_constr_of_ref "num.Z.lt")
let r_Zge  = lazy (safe_constr_of_ref "num.Z.ge")
let r_Zgt  = lazy (safe_constr_of_ref "num.Z.gt")
let r_Z    = lazy (safe_constr_of_ref "num.Z.type")
let r_eq   = lazy (safe_constr_of_ref "core.eq.type")
let r_False = lazy (safe_constr_of_ref "core.False.type")
let r_or    = lazy (safe_constr_of_ref "core.or.type")
let r_not   = lazy (safe_constr_of_ref "core.not.type")
let r_xH   = lazy (safe_constr_of_ref "num.pos.xH")
let r_xO   = lazy (safe_constr_of_ref "num.pos.xO")
let r_xI   = lazy (safe_constr_of_ref "num.pos.xI")

(* R atoms. *)
let r_R       = lazy (safe_constr_of_ref "reals.R.type")
let r_R0      = lazy (safe_constr_of_ref "reals.R.R0")
let r_Rplus   = lazy (safe_constr_of_ref "reals.R.Rplus")
let r_Rminus  = lazy (safe_constr_of_ref "reals.R.Rminus")
let r_Rmult   = lazy (safe_constr_of_ref "reals.R.Rmult")
let r_Rle     = lazy (safe_constr_of_ref "reals.R.Rle")
let r_Rlt     = lazy (safe_constr_of_ref "reals.R.Rlt")
let r_Rge     = lazy (safe_constr_of_ref "reals.R.Rge")
let r_Rgt     = lazy (safe_constr_of_ref "reals.R.Rgt")
let r_IZR     = lazy (safe_constr_of_ref "reals.R.IZR")

(* R3-M1: nat atoms + the ℕ→ℤ push-cast/transfer shims registered in
   ProofBrokerTermMode.v. *)
let r_nat    = lazy (safe_constr_of_ref "num.nat.type")
let r_nat_le = lazy (safe_constr_of_ref "num.nat.le")
let r_nat_lt = lazy (safe_constr_of_ref "num.nat.lt")
let r_nat_ge = lazy (safe_constr_of_ref "num.nat.ge")
let r_nat_gt = lazy (safe_constr_of_ref "num.nat.gt")
let r_nat_add = lazy (safe_constr_of_ref "num.nat.add")
let r_nat_mul = lazy (safe_constr_of_ref "num.nat.mul")
let r_eq_refl = lazy (safe_constr_of_ref "core.eq.refl")
let nat_push_add_ref = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_push_add")
let nat_push_mul_ref = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_push_mul")
let nat_push_pow_ref = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_push_pow")
let nat_cast_le_ref  = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_cast_le")
let nat_cast_lt_ref  = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_cast_lt")
let nat_cast_ge_ref  = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_cast_ge")
let nat_cast_gt_ref  = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_cast_gt")
let nat_cast_eq_ref  = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_cast_eq")
let nat_cast_not_le_ref = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_cast_not_le")
let nat_cast_not_lt_ref = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_cast_not_lt")
let nat_cast_not_ge_ref = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_cast_not_ge")
let nat_cast_not_gt_ref = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_cast_not_gt")
let nat_cast_not_eq_ref = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_cast_not_eq")
let nat_cast_nonneg_ref = lazy (safe_constr_of_ref "proof_broker.term_mode.nat_cast_nonneg")

let force lz =
  match Lazy.force lz with
  | Some t -> t
  | None ->
    unsupported "term_mode: a required lib_ref isn't bound — make sure \
                 ProofBrokerTermMode.v is imported and ZArith / Reals are in scope"

let eq_ref sigma a (lz : EConstr.t option Lazy.t) : bool =
  match Lazy.force lz with
  | Some c -> EConstr.eq_constr_nounivs sigma a c
  | None -> false

(* --- positive literal construction --------------------------------- *)

(* positive_constr_of_z : Z.t > 0 → EConstr representing the matching
   [positive] term using xH/xO/xI. *)
let rec positive_constr_of_z (n : Z.t) : EConstr.t =
  if Z.equal n Z.one then force r_xH
  else if Z.equal (Z.rem n (Z.of_int 2)) Z.zero then
    EConstr.mkApp (force r_xO, [| positive_constr_of_z (Z.div n (Z.of_int 2)) |])
  else
    EConstr.mkApp (force r_xI,
      [| positive_constr_of_z (Z.div (Z.sub n Z.one) (Z.of_int 2)) |])

(* z_constr : Z.t → EConstr at type Z. Only handles non-negative
   here; the only callers (coefficients, residual K) are >= 0 in
   the cert shapes we accept. *)
let z_lit (n : Z.t) : EConstr.t =
  if Z.sign n < 0 then
    unsupported "term_mode: negative Z literal in cert (got %s)"
      (Z.to_string n);
  if Z.sign n = 0 then force r_Z0
  else EConstr.mkApp (force r_Zpos, [| positive_constr_of_z n |])

(* r_lit : Z.t → EConstr at type R, via [IZR (Zpos p)] / [0%R]. *)
let r_lit (n : Z.t) : EConstr.t =
  if Z.sign n < 0 then
    unsupported "term_mode: negative literal (got %s)" (Z.to_string n);
  if Z.sign n = 0 then force r_R0
  else
    let z_econstr =
      EConstr.mkApp (force r_Zpos, [| positive_constr_of_z n |])
    in
    EConstr.mkApp (force r_IZR, [| z_econstr |])

(* --- type universe ------------------------------------------------- *)

(* A type universe (Z or R) packages the Stdlib refs and registered
   helpers under one record, so [close_term_false] /
   [close_term_comparison] / [close_term_case_split] are universe-
   polymorphic over Z and R. The dispatch picks the universe by
   inspecting [Farkas.effective_fragment] of the IR being closed:
   "LRA" → [r_universe], otherwise [z_universe]. *)
type universe = {
  name : string;
  ty : EConstr.t;
  le : EConstr.t;
  ge : EConstr.t;
  add : EConstr.t;
  sub : EConstr.t;
  mul : EConstr.t;
  lit : Z.t -> EConstr.t;
  le_to_le0 : EConstr.t;
  ge_to_le0 : EConstr.t;
  farkas_le_2 : EConstr.t;
  pos_is_pos : Z.t -> EConstr.t;
  pos_is_nonneg : Z.t -> EConstr.t;
  (* Arity-N fold building blocks. *)
  mul_nonneg_nonpos : EConstr.t;
  add_nonpos : EConstr.t;
  farkas_contradict_n : EConstr.t;
  (* Strict-[<] / [>] normalization, [None] on universes where the
     +1 trick is unsound (any non-discrete domain, [R] in particular).
     [Some lemma] means the universe wires [lemma : a < b -> (a + 1) - b <= 0]
     (and the swapped variant for [>]) so the closer can normalize
     strict hypotheses to the same [a' <= 0] form [<=] / [>=] take. *)
  lt_to_le0 : EConstr.t option;
  gt_to_le0 : EConstr.t option;
  (* Eq-hypothesis normalization. From [h : a = b], produce
     [a - b <= 0] ([eq_to_le0]) or [b - a <= 0] ([eq_to_le0_flipped]).
     Always available — both Z and R have closed-form proofs via
     [sub_diag] + [le_refl]. The flipped variant is used when the
     witness's signed coefficient is negative. *)
  eq_to_le0 : EConstr.t;
  eq_to_le0_flipped : EConstr.t;
  (* Not-hypothesis normalization. Each takes [h : ~ (a <op> b)] and
     produces the matching normalized form:
       * [not_le_to_le0]: [~ a <= b] → [(b + 1) - a <= 0] (Z, +1 trick)
                          or [b - a < 0] (R, strict preserved).
       * [not_ge_to_le0]: [~ a >= b] → [(a + 1) - b <= 0] (Z)
                          or [a - b < 0] (R).
       * [not_lt_to_le0]: [~ a < b] → [b - a <= 0] (both, loose).
       * [not_gt_to_le0]: [~ a > b] → [a - b <= 0] (both, loose).
     [not_strict_inner_produces_lt] tracks whether the strict-inner
     negations ([~ <=] / [~ >=]) yield a Lt-form output (true on R,
     false on Z). *)
  not_le_to_le0 : EConstr.t;
  not_ge_to_le0 : EConstr.t;
  not_lt_to_le0 : EConstr.t;
  not_gt_to_le0 : EConstr.t;
  not_strict_inner_produces_lt : bool;
  (* Strict-aware Farkas fold building blocks. [Some _] only on
     universes where strict premises survive normalization as [a < 0]
     rather than getting folded into [a <= 0] via the LIA +1 trick —
     i.e. R only today (Z's [lt_to_le0]/[gt_to_le0] do the fold, so
     these stay [None] on Z and the strict-aware path is unreachable). *)
  lt_to_lt0 : EConstr.t option;
  gt_to_lt0 : EConstr.t option;
  mul_pos_neg : EConstr.t option;
  add_le_lt : EConstr.t option;
  add_lt_le : EConstr.t option;
  add_neg : EConstr.t option;
  farkas_contradict_n_strict : EConstr.t option;
}

let z_universe () : universe = {
  name = "Z";
  ty = force r_Z;
  le = force r_Zle;
  ge = force r_Zge;
  add = force r_Zadd;
  sub = force r_Zsub;
  mul = force r_Zmul;
  lit = z_lit;
  le_to_le0 = force z_le_to_le0;
  ge_to_le0 = force z_ge_to_le0;
  farkas_le_2 = force z_farkas_le_2;
  pos_is_pos = (fun n ->
    EConstr.mkApp (force z_pos_is_pos, [| positive_constr_of_z n |]));
  pos_is_nonneg = (fun n ->
    EConstr.mkApp (force z_pos_is_nonneg, [| positive_constr_of_z n |]));
  mul_nonneg_nonpos = force z_mul_nonneg_nonpos;
  add_nonpos = force z_add_nonpos;
  farkas_contradict_n = force z_farkas_contradict_n;
  lt_to_le0 = Some (force z_lt_to_le0);
  gt_to_le0 = Some (force z_gt_to_le0);
  eq_to_le0 = force z_eq_to_le0_ref;
  eq_to_le0_flipped = force z_eq_to_le0_flipped_ref;
  not_le_to_le0 = force z_not_le_to_le0_ref;
  not_ge_to_le0 = force z_not_ge_to_le0_ref;
  not_lt_to_le0 = force z_not_lt_to_le0_ref;
  not_gt_to_le0 = force z_not_gt_to_le0_ref;
  not_strict_inner_produces_lt = false;
  (* Z folds strict into Le via the +1 trick at [lt_to_le0] /
     [gt_to_le0] time, so the strict-aware fold path is unused
     on Z and these stay [None]. *)
  lt_to_lt0 = None;
  gt_to_lt0 = None;
  mul_pos_neg = None;
  add_le_lt = None;
  add_lt_le = None;
  add_neg = None;
  farkas_contradict_n_strict = None;
}

let r_universe () : universe = {
  name = "R";
  ty = force r_R;
  le = force r_Rle;
  ge = force r_Rge;
  add = force r_Rplus;
  sub = force r_Rminus;
  mul = force r_Rmult;
  lit = r_lit;
  le_to_le0 = force r_le_to_le0_ref;
  ge_to_le0 = force r_ge_to_le0_ref;
  farkas_le_2 = force r_farkas_le_2_ref;
  pos_is_pos = (fun n ->
    EConstr.mkApp (force r_pos_is_pos_ref, [| positive_constr_of_z n |]));
  pos_is_nonneg = (fun n ->
    EConstr.mkApp (force r_pos_is_nonneg_ref, [| positive_constr_of_z n |]));
  mul_nonneg_nonpos = force r_mul_nonneg_nonpos_ref;
  add_nonpos = force r_add_nonpos_ref;
  farkas_contradict_n = force r_farkas_contradict_n_ref;
  (* R strict-[<] / [>] preserve strictness through the fold (no +1
     trick over the reals) via the strict-aware path below. The Le-form
     [lt_to_le0]/[gt_to_le0] stay [None] because we don't weaken — the
     normalizer returns the strict [a - b < 0] form via [lt_to_lt0]/
     [gt_to_lt0] and the fold tracks strictness from there. *)
  lt_to_le0 = None;
  gt_to_le0 = None;
  eq_to_le0 = force r_eq_to_le0_ref;
  eq_to_le0_flipped = force r_eq_to_le0_flipped_ref;
  not_le_to_le0 = force r_not_le_to_lt0_ref;
  not_ge_to_le0 = force r_not_ge_to_lt0_ref;
  not_lt_to_le0 = force r_not_lt_to_le0_ref;
  not_gt_to_le0 = force r_not_gt_to_le0_ref;
  not_strict_inner_produces_lt = true;
  lt_to_lt0 = Some (force r_lt_to_lt0_ref);
  gt_to_lt0 = Some (force r_gt_to_lt0_ref);
  mul_pos_neg = Some (force r_mul_pos_neg_ref);
  add_le_lt = Some (force r_add_le_lt_ref);
  add_lt_le = Some (force r_add_lt_le_ref);
  add_neg = Some (force r_add_neg_ref);
  farkas_contradict_n_strict = Some (force r_farkas_contradict_n_strict_ref);
}

let universe_for_ir (ir : Ir.t) : universe =
  match Farkas.effective_fragment ir with
  | "LRA" -> r_universe ()
  | _ -> z_universe ()

(* --- goal kind ----------------------------------------------------- *)

(* Goal universe tag: discriminates Z- vs R-typed comparators so the
   dispatcher in pb_rocq_main.run_close_term picks the right
   normalization tactic ([Z.le_ge] vs [Rle_ge] etc.) and term_mode's
   [close_term_comparison] picks the right wrapper helper
   ([z_le_via_lt] vs [r_le_via_lt]) and neg_norm shape (+1 trick for
   LIA only). *)
type universe_tag = U_Z | U_R

type goal_kind =
  | Goal_false
  | Goal_le of EConstr.t * EConstr.t * universe_tag
  | Goal_lt of EConstr.t * EConstr.t * universe_tag
  | Goal_ge of EConstr.t * EConstr.t * universe_tag
  | Goal_gt of EConstr.t * EConstr.t * universe_tag
  | Goal_eq of EConstr.t * EConstr.t * universe_tag
  (* R3-M1: ℕ comparison goals. nat [>=] / [>] are DEFINITIONALLY the
     swapped [<=] / [<] (unlike Z's compare-based forms), so the
     matcher swaps here and the wrapper apply unifies by conversion —
     no per-direction lemma needed. -*)
  | Goal_nat_le of EConstr.t * EConstr.t
  | Goal_nat_lt of EConstr.t * EConstr.t
  | Goal_nat_eq

let goal_kind sigma (ty : EConstr.t) : goal_kind option =
  if eq_ref sigma ty r_False then Some Goal_false
  else match EConstr.kind sigma ty with
    | App (head, [| b; c |]) when eq_ref sigma head r_nat_le ->
      Some (Goal_nat_le (b, c))
    | App (head, [| b; c |]) when eq_ref sigma head r_nat_lt ->
      Some (Goal_nat_lt (b, c))
    | App (head, [| a; b |]) when eq_ref sigma head r_nat_ge ->
      Some (Goal_nat_le (b, a))
    | App (head, [| a; b |]) when eq_ref sigma head r_nat_gt ->
      Some (Goal_nat_lt (b, a))
    | App (head, [| ty_arg; _; _ |])
        when eq_ref sigma head r_eq && eq_ref sigma ty_arg r_nat ->
      Some Goal_nat_eq
    | App (head, [| b; c |]) when eq_ref sigma head r_Zle ->
      Some (Goal_le (b, c, U_Z))
    | App (head, [| b; c |]) when eq_ref sigma head r_Zlt ->
      Some (Goal_lt (b, c, U_Z))
    | App (head, [| b; c |]) when eq_ref sigma head r_Zge ->
      Some (Goal_ge (b, c, U_Z))
    | App (head, [| b; c |]) when eq_ref sigma head r_Zgt ->
      Some (Goal_gt (b, c, U_Z))
    | App (head, [| b; c |]) when eq_ref sigma head r_Rle ->
      Some (Goal_le (b, c, U_R))
    | App (head, [| b; c |]) when eq_ref sigma head r_Rlt ->
      Some (Goal_lt (b, c, U_R))
    | App (head, [| b; c |]) when eq_ref sigma head r_Rge ->
      Some (Goal_ge (b, c, U_R))
    | App (head, [| b; c |]) when eq_ref sigma head r_Rgt ->
      Some (Goal_gt (b, c, U_R))
    | App (head, [| ty_arg; a; b |])
        when eq_ref sigma head r_eq && eq_ref sigma ty_arg r_Z ->
      Some (Goal_eq (a, b, U_Z))
    | App (head, [| ty_arg; a; b |])
        when eq_ref sigma head r_eq && eq_ref sigma ty_arg r_R ->
      Some (Goal_eq (a, b, U_R))
    | _ -> None

let universe_of_tag = function
  | U_Z -> z_universe ()
  | U_R -> r_universe ()

(* --- witness parsing ----------------------------------------------- *)

(* Parse the witness into rational coefficients first, then call the
   SDK's [clear_denominators_list] to scale every coefficient by the
   LCM of denominators. Solver-emitted LRA Farkas witnesses routinely
   carry rationals (eg cvc5 emits 1/2-style coefficients when the
   combination requires fractional scaling); the closer's universe-
   polymorphic builders expect integer coefficients, so we clear once
   here and the rest of the pipeline doesn't need to know.

   Soundness rests on the SDK helper's invariant: multiplying every
   coefficient by a single positive integer preserves each premise's
   compiled non-positivity, scales the residual K by the same factor
   (sign preserved), and leaves strictness state untouched. The
   closer's contradiction step uses the scaled K. *)
let parse_witness (w : Yojson.Safe.t) : (string * Z.t) list =
  let entries_q : (string * L.rational) list =
    match w with
    | `Assoc kv ->
      (match List.assoc_opt "coefficients" kv with
       | Some (`List xs) ->
         List.map (function
           | `Assoc fields ->
             let h = match List.assoc_opt "hypothesis" fields with
               | Some (`String s) -> s
               | _ -> unsupported "term_mode: witness entry missing 'hypothesis' string"
             in
             let c_str = match List.assoc_opt "coefficient" fields with
               | Some (`String s) -> s
               | _ -> unsupported "term_mode: witness entry missing 'coefficient' string"
             in
             let r = match L.rat_of_string c_str with
               | Some r -> r
               | None -> unsupported "term_mode: bad coefficient %s" c_str
             in
             (h, r)
           | _ -> unsupported "term_mode: witness entry not an object")
           xs
       | _ -> unsupported "term_mode: witness missing 'coefficients' list")
    | _ -> unsupported "term_mode: witness is not a JSON object"
  in
  let scaled, _lcd = L.clear_denominators_list entries_q in
  scaled

(* --- residual K via SDK's Farkas linearizer ------------------------ *)

let compute_residual ?(require_strict=true) (ir : Ir.t)
    (entries : (string * Z.t) list) : Z.t =
  let fragment = Farkas.effective_fragment ir in
  let lookup name =
    match Farkas.lookup_hypothesis ir name with
    | Some shell -> shell
    | None ->
      unsupported "term_mode: cert references unknown hypothesis %s" name
  in
  let sum =
    List.fold_left (fun acc (name, coef) ->
      let shell = lookup name in
      match Farkas.compile_hypothesis ~fragment shell with
      | Ok (Le f) | Ok (Lt f) ->
        (* [Lt] only arises over LRA — LIA's [<] / [>] / [neg_goal]
           paths all fold strictness into [Le] via the +1 trick. For
           the residual K computation we drop strictness; soundness
           rests on K > 0 (which solver-emitted comparison-goal Farkas
           witnesses carry in practice). The strictness-aware proof
           term is handled inside the helper lemma's [destruct] — the
           OCaml side just constructs the linear-form scalar K. *)
        let scaled = L.scale (L.mk_rat_z coef Z.one) f in
        L.add acc scaled
      | Ok (Eq f) ->
        (* Eq compiles to a linear form that's exactly zero under the
           hypothesis. Any signed coefficient is sound — Eq hypotheses
           don't constrain sign because [c * 0 = 0] regardless of [c].
           For residual computation we scale by the signed coefficient
           (matches SDK [Farkas.verify]'s Eq branch); the closer side
           reconstructs the same scaled contribution by either applying
           [eq_to_le0] directly (positive coef) or after [eq_sym]
           (negative coef → flipped direction). *)
        let scaled = L.scale (L.mk_rat_z coef Z.one) f in
        L.add acc scaled
      | Error e ->
        unsupported "term_mode: compile_hypothesis(%s) failed: %s" name e)
      L.zero entries
  in
  let k_rat = L.constant_value sum in
  if not (Z.equal k_rat.den Z.one) then
    unsupported "term_mode: residual %s is not an integer"
      (L.rat_to_string k_rat);
  let sign = Z.sign k_rat.num in
  if require_strict && sign <= 0 then
    unsupported "term_mode: residual K=%s must be positive (cert verifier \
                 should have caught this earlier)" (Z.to_string k_rat.num);
  if (not require_strict) && sign < 0 then
    unsupported "term_mode: residual K=%s must be non-negative (cert \
                 verifier should have caught this earlier)"
      (Z.to_string k_rat.num);
  k_rat.num

(* --- per-hypothesis normalization ---------------------------------- *)

(* Normalized hypothesis output: linear-form LHS [expr], proof term,
   and a [strict] flag distinguishing the Le-shape [expr <= 0] from
   the Lt-shape [expr < 0]. The Z universe always returns
   [strict = false] (the +1 trick folds [<] / [>] into Le); the R
   universe returns [strict = true] for [Rlt] / [Rgt] heads and
   [strict = false] for [Rle] / [Rge]. *)
type normalized_hyp = {
  expr : EConstr.t;
  proof : EConstr.t;
  strict : bool;
}

(* For a hypothesis [h : T.le a b] / [h : T.ge a b] / [h : T.lt a b] /
   [h : T.gt a b] / [h : a = b] over T ∈ {Z, R}, produce a
   [normalized_hyp] using the universe's normalization helpers.
   Detection is by the inner head ref. Strict shapes route through
   different paths per universe:

     * Z (LIA): [lt_to_le0] / [gt_to_le0] (+1 trick), strict = false.
     * R (LRA): [lt_to_lt0] / [gt_to_lt0] (strictness preserving),
                strict = true; the strict-aware fold in the caller
                picks the right [mul_*] / [add_*] / [contradict_n_*]
                combinators from there.

   [flipped] controls Eq-hypothesis direction: [false] picks
   [a - b <= 0] (matches positive coefficients), [true] picks
   [b - a <= 0] (matches negative coefficients, after the caller
   has converted to |c|). [flipped] is ignored on inequality
   hypotheses — those have a unique normalized form. *)
(* --- R3-M1: the ℕ→ℤ lift (push-cast + hypothesis transfer) --------- *)

(* [(pushed Z form, proof [Z.of_nat t = pushed])] for a nat term [t].
   The recursive push mirrors the reifier's ℤ-image emission:
   literals fold, [+] and [*]-by-literal distribute through the
   [nat_push_*] shims, a product with no literal factor stays one
   [Z.of_nat _] atom (the reifier's Opaque atomization), and closed
   powers fold with the Z-side computation discharged by [eq_refl]
   (kernel-cheap on binary Z literals — normalizing
   [Z.of_nat (2^24)] through the unary numeral is exactly what this
   avoids). Everything applied is constructive, keeping the ℕ
   term-mode footprint EMPTY (the M1 Rocq gate). *)
let rec push_nat_to_z (u : universe) env sigma (t : EConstr.t)
  : EConstr.t * EConstr.t =
  let of_nat x = EConstr.mkApp (force Reifier.r_z_of_nat, [| x |]) in
  let refl_at z = EConstr.mkApp (force r_eq_refl, [| u.ty; z |]) in
  let atom () = let z = of_nat t in (z, refl_at z) in
  match Reifier.nat_literal sigma t with
  | Some n -> let z = u.lit n in (z, refl_at z)
  | None ->
    if EConstr.isVar sigma t then atom ()
    else
      (match EConstr.kind sigma t with
       | App (head, [| a; b |]) ->
         if eq_ref sigma head r_nat_add then
           let (za, pa) = push_nat_to_z u env sigma a in
           let (zb, pb) = push_nat_to_z u env sigma b in
           (EConstr.mkApp (u.add, [| za; zb |]),
            EConstr.mkApp (force nat_push_add_ref,
              [| a; b; za; zb; pa; pb |]))
         else if eq_ref sigma head r_nat_mul then begin
           match Reifier.nat_literal sigma a, Reifier.nat_literal sigma b with
           | None, None -> atom ()  (* the reifier's Opaque atom *)
           | _ ->
             let (za, pa) = push_nat_to_z u env sigma a in
             let (zb, pb) = push_nat_to_z u env sigma b in
             (EConstr.mkApp (u.mul, [| za; zb |]),
              EConstr.mkApp (force nat_push_mul_ref,
                [| a; b; za; zb; pa; pb |]))
         end
         else if eq_ref sigma head Reifier.r_nat_pow then begin
           match Reifier.nat_literal sigma a, Reifier.nat_literal sigma b with
           | Some base, Some exp when Z.compare exp (Z.of_int 256) <= 0 ->
             let z = u.lit (Z.pow base (Z.to_int exp)) in
             (z, EConstr.mkApp (force nat_push_pow_ref,
                   [| a; b; z; refl_at z |]))
           | _ -> atom ()
         end
         else atom ()
       | _ -> atom ())

let starts_with prefix s =
  String.length s >= String.length prefix
  && String.sub s 0 (String.length prefix) = prefix

(* ℕ hypothesis transfer: witness-named ℕ facts become their ℤ
   images by term construction, then flow through the SAME Z
   normalization the Int path uses — so the fold, residual and
   [ring] discharge are shared verbatim. [None] = not a ℕ-shaped
   entry (the caller falls through to the Z/R dispatch).

   [_pb_nonneg_*] entries are SYNTHETIC — no named hypothesis
   exists; the fact [0 <= z] is proved outright by
   [nat_cast_nonneg] on the atom (a variable, or an atomized
   product resolved through [nat_atoms]). *)
let normalize_nat_hyp (u : universe) env sigma (name : string)
    ~(flipped : bool) ~(nat_atoms : (string * EConstr.t) list)
  : normalized_hyp option =
  if starts_with "_pb_nonneg_" name then begin
    let key = String.sub name 11 (String.length name - 11) in
    let nat_e =
      if starts_with "atom_" key then
        (match List.assoc_opt ("_pb_" ^ key) nat_atoms with
         | Some e -> e
         | None ->
           unsupported "term_mode: witness names %s but the extraction \
                        has no atom _pb_%s" name key)
      else EConstr.mkVar (Names.Id.of_string key)
    in
    let (z, p) = push_nat_to_z u env sigma nat_e in
    let casted =
      EConstr.mkApp (force nat_cast_nonneg_ref, [| nat_e; z; p |]) in
    let zero = u.lit Z.zero in
    Some { expr = EConstr.mkApp (u.sub, [| zero; z |]);
           proof = EConstr.mkApp (u.le_to_le0, [| zero; z; casted |]);
           strict = false }
  end else
  match
    (try Some (Environ.lookup_named (Names.Id.of_string name) env)
     with Not_found -> None)
  with
  | None -> None
  | Some decl ->
    let ty = EConstr.of_constr (Context.Named.Declaration.get_type decl) in
    let h_term = EConstr.mkVar (Names.Id.of_string name) in
    let cast2 shim a b =
      let (za, pa) = push_nat_to_z u env sigma a in
      let (zb, pb) = push_nat_to_z u env sigma b in
      (za, zb,
       EConstr.mkApp (force shim, [| a; b; za; zb; pa; pb; h_term |]))
    in
    let le_norm za zb casted =
      Some { expr = EConstr.mkApp (u.sub, [| za; zb |]);
             proof = EConstr.mkApp (u.le_to_le0, [| za; zb; casted |]);
             strict = false }
    in
    let lt_norm za zb casted =
      (* Z +1 trick — the SDK compiled the strict shape the same way. *)
      match u.lt_to_le0 with
      | Some lemma ->
        let za1 = EConstr.mkApp (u.add, [| za; u.lit Z.one |]) in
        Some { expr = EConstr.mkApp (u.sub, [| za1; zb |]);
               proof = EConstr.mkApp (lemma, [| za; zb; casted |]);
               strict = false }
      | None ->
        unsupported "term_mode: ℕ lift needs the Z +1-trick lemma wired"
    in
    (match EConstr.kind sigma ty with
     | App (head, [| a; b |]) ->
       if eq_ref sigma head r_nat_le then
         let (za, zb, c) = cast2 nat_cast_le_ref a b in le_norm za zb c
       else if eq_ref sigma head r_nat_lt then
         let (za, zb, c) = cast2 nat_cast_lt_ref a b in lt_norm za zb c
       else if eq_ref sigma head r_nat_ge then
         (* casted : zb <= za *)
         let (za, zb, c) = cast2 nat_cast_ge_ref a b in le_norm zb za c
       else if eq_ref sigma head r_nat_gt then
         let (za, zb, c) = cast2 nat_cast_gt_ref a b in lt_norm zb za c
       else None
     | App (head, [| inner |]) when eq_ref sigma head r_not ->
       (match EConstr.kind sigma inner with
        | App (inner_head, [| a; b |]) ->
          if eq_ref sigma inner_head r_nat_le then
            (* casted : ~ (za <= zb) → SDK compiled (zb+1) - za <= 0. *)
            let (za, zb, c) = cast2 nat_cast_not_le_ref a b in
            Some { expr = EConstr.mkApp (u.sub,
                     [| EConstr.mkApp (u.add, [| zb; u.lit Z.one |]); za |]);
                   proof = EConstr.mkApp (u.not_le_to_le0, [| za; zb; c |]);
                   strict = false }
          else if eq_ref sigma inner_head r_nat_lt then
            (* casted : ~ (za < zb) → zb - za <= 0. *)
            let (za, zb, c) = cast2 nat_cast_not_lt_ref a b in
            Some { expr = EConstr.mkApp (u.sub, [| zb; za |]);
                   proof = EConstr.mkApp (u.not_lt_to_le0, [| za; zb; c |]);
                   strict = false }
          else if eq_ref sigma inner_head r_nat_ge then
            (* casted : ~ (zb <= za) → (za+1) - zb <= 0. *)
            let (za, zb, c) = cast2 nat_cast_not_ge_ref a b in
            Some { expr = EConstr.mkApp (u.sub,
                     [| EConstr.mkApp (u.add, [| za; u.lit Z.one |]); zb |]);
                   proof = EConstr.mkApp (u.not_le_to_le0, [| zb; za; c |]);
                   strict = false }
          else if eq_ref sigma inner_head r_nat_gt then
            (* casted : ~ (zb < za) → za - zb <= 0. *)
            let (za, zb, c) = cast2 nat_cast_not_gt_ref a b in
            Some { expr = EConstr.mkApp (u.sub, [| za; zb |]);
                   proof = EConstr.mkApp (u.not_lt_to_le0, [| zb; za; c |]);
                   strict = false }
          else None
        | _ -> None)
     | App (head, [| ty_arg; a; b |])
         when eq_ref sigma head r_eq && eq_ref sigma ty_arg r_nat ->
       let (za, zb, c) = cast2 nat_cast_eq_ref a b in
       if flipped then
         Some { expr = EConstr.mkApp (u.sub, [| zb; za |]);
                proof = EConstr.mkApp (u.eq_to_le0_flipped, [| za; zb; c |]);
                strict = false }
       else
         Some { expr = EConstr.mkApp (u.sub, [| za; zb |]);
                proof = EConstr.mkApp (u.eq_to_le0, [| za; zb; c |]);
                strict = false }
     | _ -> None)

(* Positive ℤ-image transfer for the WALKER's cast layer: the shims
   applied without ≤0-normalization (the walker matches trace
   assumes against the posed facts by conversion; the Farkas fold
   is not involved). [None] = not a ℕ-shaped Prop. *)
let nat_cast_fact_opt (u : universe) env sigma (ty : EConstr.t)
    (h_term : EConstr.t) : EConstr.t option =
  let cast2 shim a b =
    let (za, pa) = push_nat_to_z u env sigma a in
    let (zb, pb) = push_nat_to_z u env sigma b in
    EConstr.mkApp (force shim, [| a; b; za; zb; pa; pb; h_term |])
  in
  match EConstr.kind sigma ty with
  | App (head, [| a; b |]) ->
    if eq_ref sigma head r_nat_le then Some (cast2 nat_cast_le_ref a b)
    else if eq_ref sigma head r_nat_lt then Some (cast2 nat_cast_lt_ref a b)
    else if eq_ref sigma head r_nat_ge then Some (cast2 nat_cast_ge_ref a b)
    else if eq_ref sigma head r_nat_gt then Some (cast2 nat_cast_gt_ref a b)
    else None
  | App (head, [| inner |]) when eq_ref sigma head r_not ->
    (match EConstr.kind sigma inner with
     | App (inner_head, [| a; b |]) ->
       if eq_ref sigma inner_head r_nat_le then
         Some (cast2 nat_cast_not_le_ref a b)
       else if eq_ref sigma inner_head r_nat_lt then
         Some (cast2 nat_cast_not_lt_ref a b)
       else if eq_ref sigma inner_head r_nat_ge then
         Some (cast2 nat_cast_not_ge_ref a b)
       else if eq_ref sigma inner_head r_nat_gt then
         Some (cast2 nat_cast_not_gt_ref a b)
       else None
     | App (inner_head, [| ty_arg; a; b |])
         when eq_ref sigma inner_head r_eq && eq_ref sigma ty_arg r_nat ->
       Some (cast2 nat_cast_not_eq_ref a b)
     | _ -> None)
  | App (head, [| ty_arg; a; b |])
      when eq_ref sigma head r_eq && eq_ref sigma ty_arg r_nat ->
    Some (cast2 nat_cast_eq_ref a b)
  | _ -> None

(* Every ℤ-image fact the walker's cast layer poses: the cast image
   of each ℕ-shaped named Prop hypothesis (opportunistic — the
   walker matches what the trace needs), plus one nonneg fact per ℕ
   atom (named locals of type nat, and the atomized products). *)
let nat_walker_facts env sigma
    ~(nat_atoms : (string * EConstr.t) list)
  : (string * EConstr.t) list =
  let u = z_universe () in
  let named = Environ.named_context env in
  let hyp_facts =
    List.filter_map (fun decl ->
      let id = Context.Named.Declaration.get_id decl in
      let ty = EConstr.of_constr (Context.Named.Declaration.get_type decl) in
      match nat_cast_fact_opt u env sigma ty (EConstr.mkVar id) with
      | Some proof -> Some ("_pb_z_" ^ Names.Id.to_string id, proof)
      | None -> None)
      named
  in
  let nonneg_of name e =
    let (z, p) = push_nat_to_z u env sigma e in
    (name, EConstr.mkApp (force nat_cast_nonneg_ref, [| e; z; p |]))
  in
  let var_nonneg =
    List.filter_map (fun decl ->
      let id = Context.Named.Declaration.get_id decl in
      let ty = EConstr.of_constr (Context.Named.Declaration.get_type decl) in
      if eq_ref sigma ty r_nat then
        Some (nonneg_of ("_pb_z_nonneg_" ^ Names.Id.to_string id)
                (EConstr.mkVar id))
      else None)
      named
  in
  let atom_nonneg =
    List.map (fun (aid, e) -> nonneg_of ("_pb_z_nonneg" ^ aid) e) nat_atoms
  in
  hyp_facts @ var_nonneg @ atom_nonneg

let normalize_hypothesis (u : universe) env sigma (id : Names.Id.t)
    ~(nat_atoms : (string * EConstr.t) list)
    ~(flipped : bool)
  : normalized_hyp =
  (* R3-M1: ℕ-shaped entries (and the synthetic [_pb_nonneg_*]
     facts) go through the cast layer; everything else takes the
     pre-existing Z/R dispatch below. *)
  match
    normalize_nat_hyp u env sigma (Names.Id.to_string id) ~flipped ~nat_atoms
  with
  | Some nh -> nh
  | None ->
  let decl = Environ.lookup_named id env in
  let ty = EConstr.of_constr (Context.Named.Declaration.get_type decl) in
  let h_term = EConstr.mkVar id in
  match EConstr.kind sigma ty with
  | App (head, [| _ty_arg; a; b |]) when eq_ref sigma head r_eq ->
    (* Eq hypothesis [h : a = b]. *)
    if flipped then
      let expr = EConstr.mkApp (u.sub, [| b; a |]) in
      let proof = EConstr.mkApp (u.eq_to_le0_flipped, [| a; b; h_term |]) in
      { expr; proof; strict = false }
    else
      let expr = EConstr.mkApp (u.sub, [| a; b |]) in
      let proof = EConstr.mkApp (u.eq_to_le0, [| a; b; h_term |]) in
      { expr; proof; strict = false }
  | App (head, [| inner |]) when eq_ref sigma head r_not ->
    (* Not-hypothesis [h : ~ (a <op> b)]. Dispatch by inner head;
       each negation has a fixed conversion direction and the
       resulting form's strictness depends on the universe (Z folds
       strict via +1; R preserves strict via [lt_to_lt0] /
       [gt_to_lt0]-style). *)
    let one = u.lit Z.one in
    (match EConstr.kind sigma inner with
     | App (inner_head, [| a; b |]) ->
       let head_matches lz =
         match Lazy.force lz with
         | Some c -> EConstr.eq_constr_nounivs sigma inner_head c
         | None -> false
       in
       let is_le = head_matches r_Zle || head_matches r_Rle in
       let is_ge = head_matches r_Zge || head_matches r_Rge in
       let is_lt = head_matches r_Zlt || head_matches r_Rlt in
       let is_gt = head_matches r_Zgt || head_matches r_Rgt in
       if is_le then
         (* [~ a <= b] → Z: [(b + 1) - a <= 0]; R: [b - a < 0]. *)
         let expr =
           if u.not_strict_inner_produces_lt then
             EConstr.mkApp (u.sub, [| b; a |])
           else
             let b_plus_1 = EConstr.mkApp (u.add, [| b; one |]) in
             EConstr.mkApp (u.sub, [| b_plus_1; a |])
         in
         let proof = EConstr.mkApp (u.not_le_to_le0, [| a; b; h_term |]) in
         { expr; proof; strict = u.not_strict_inner_produces_lt }
       else if is_ge then
         (* [~ a >= b] → Z: [(a + 1) - b <= 0]; R: [a - b < 0]. *)
         let expr =
           if u.not_strict_inner_produces_lt then
             EConstr.mkApp (u.sub, [| a; b |])
           else
             let a_plus_1 = EConstr.mkApp (u.add, [| a; one |]) in
             EConstr.mkApp (u.sub, [| a_plus_1; b |])
         in
         let proof = EConstr.mkApp (u.not_ge_to_le0, [| a; b; h_term |]) in
         { expr; proof; strict = u.not_strict_inner_produces_lt }
       else if is_lt then
         (* [~ a < b] → [b - a <= 0] (loose, both Z and R). *)
         let expr = EConstr.mkApp (u.sub, [| b; a |]) in
         let proof = EConstr.mkApp (u.not_lt_to_le0, [| a; b; h_term |]) in
         { expr; proof; strict = false }
       else if is_gt then
         (* [~ a > b] → [a - b <= 0] (loose, both Z and R). *)
         let expr = EConstr.mkApp (u.sub, [| a; b |]) in
         let proof = EConstr.mkApp (u.not_gt_to_le0, [| a; b; h_term |]) in
         { expr; proof; strict = false }
       else
         unsupported "term_mode: Not-hypothesis %s on %s has unrecognized \
                      inner head (expected ≤/≥/</>)"
           (Names.Id.to_string id) u.name
     | _ ->
       unsupported "term_mode: Not-hypothesis %s on %s has non-binary inner \
                    operand"
         (Names.Id.to_string id) u.name)
  | App (head, [| a; b |]) ->
    let head_matches lz =
      match Lazy.force lz with
      | Some c -> EConstr.eq_constr_nounivs sigma head c
      | None -> false
    in
    let is_le = head_matches r_Zle || head_matches r_Rle in
    let is_ge = head_matches r_Zge || head_matches r_Rge in
    let is_lt = head_matches r_Zlt || head_matches r_Rlt in
    let is_gt = head_matches r_Zgt || head_matches r_Rgt in
    let one = u.lit Z.one in
    if is_le then
      let expr = EConstr.mkApp (u.sub, [| a; b |]) in
      let proof = EConstr.mkApp (u.le_to_le0, [| a; b; h_term |]) in
      { expr; proof; strict = false }
    else if is_ge then
      let expr = EConstr.mkApp (u.sub, [| b; a |]) in
      let proof = EConstr.mkApp (u.ge_to_le0, [| a; b; h_term |]) in
      { expr; proof; strict = false }
    else if is_lt then
      (* Prefer the strict-preserving path when the universe has it
         ([lt_to_lt0], R); otherwise fall back to the LIA +1 trick
         ([lt_to_le0], Z). *)
      (match u.lt_to_lt0, u.lt_to_le0 with
       | Some lemma, _ ->
         let expr = EConstr.mkApp (u.sub, [| a; b |]) in
         let proof = EConstr.mkApp (lemma, [| a; b; h_term |]) in
         { expr; proof; strict = true }
       | None, Some lemma ->
         let a_plus_1 = EConstr.mkApp (u.add, [| a; one |]) in
         let expr = EConstr.mkApp (u.sub, [| a_plus_1; b |]) in
         let proof = EConstr.mkApp (lemma, [| a; b; h_term |]) in
         { expr; proof; strict = false }
       | None, None ->
         unsupported "term_mode: strict [<] hypothesis %s on %s — \
                      neither strict-aware nor +1-trick normalization \
                      is wired on this universe"
           (Names.Id.to_string id) u.name)
    else if is_gt then
      (match u.gt_to_lt0, u.gt_to_le0 with
       | Some lemma, _ ->
         let expr = EConstr.mkApp (u.sub, [| b; a |]) in
         let proof = EConstr.mkApp (lemma, [| a; b; h_term |]) in
         { expr; proof; strict = true }
       | None, Some lemma ->
         let b_plus_1 = EConstr.mkApp (u.add, [| b; one |]) in
         let expr = EConstr.mkApp (u.sub, [| b_plus_1; a |]) in
         let proof = EConstr.mkApp (lemma, [| a; b; h_term |]) in
         { expr; proof; strict = false }
       | None, None ->
         unsupported "term_mode: strict [>] hypothesis %s on %s — \
                      neither strict-aware nor +1-trick normalization \
                      is wired on this universe"
           (Names.Id.to_string id) u.name)
    else
      unsupported "term_mode: hypothesis %s has shape outside \
                   %s.le / %s.ge / %s.lt / %s.gt / = \
                   (head not recognized for this universe)"
        (Names.Id.to_string id) u.name u.name u.name u.name
  | _ ->
    unsupported "term_mode: hypothesis %s is not a recognized comparison \
                 or equality shape"
      (Names.Id.to_string id)

(* Detect whether a hypothesis is an Eq shape. Used by the closer to
   permit signed coefficients on Eq while keeping the positive-
   coefficient invariant on inequalities. *)
let is_eq_hypothesis env sigma (id : Names.Id.t) : bool =
  try
    let decl = Environ.lookup_named id env in
    let ty = EConstr.of_constr (Context.Named.Declaration.get_type decl) in
    match EConstr.kind sigma ty with
    | App (head, [| _; _; _ |]) -> eq_ref sigma head r_eq
    | _ -> false
  with _ -> false

(* --- tactic invocation by name ------------------------------------- *)

(* Invoke an Ltac tactic by source-string. Same idiom the reifier
   uses around [Procq.parse_string] to call a name-resolved tactic
   from inside a plugin. [Goal.enter] defers the parse/intern so
   [Global.env] doesn't fire during plugin module init. *)
let invoke_tactic (src : string) : unit Proofview.tactic =
  Proofview.Goal.enter (fun _ ->
    let raw = Procq.parse_string Ltac_plugin.Pltac.tactic src in
    let glob =
      Ltac_plugin.Tacintern.intern_pure_tactic
        (Ltac_plugin.Tacintern.make_empty_glob_sign ~strict:false) raw
    in
    Ltac_plugin.Tacinterp.eval_tactic glob)

let invoke_ring : unit Proofview.tactic = invoke_tactic "ring"

(* --- shared coefficient-witness builders --------------------------- *)

(* Validate a witness entry's signed coefficient against its
   hypothesis shape:
   * c = 0: not allowed today (the caller filters these out before
     calling this); zero coefficients contribute nothing to the
     Farkas sum.
   * c < 0 on Eq hypothesis: sound — use the flipped direction
     [b - a <= 0] with [|c|] as the positive coefficient.
   * c < 0 on inequality hypothesis: unsound (SDK rejects). The
     bridge surfaces a clear error.
   * c > 0: standard path. *)
let check_signed_coef ~slot env sigma (cz : Z.t) (is_eq : bool) =
  let _ = env in let _ = sigma in
  let sign = Z.sign cz in
  if sign = 0 then
    unsupported "term_mode: zero coefficient on %s slot — should have been \
                 filtered before reaching the closer" slot;
  if sign < 0 && not is_eq then
    unsupported "term_mode: negative coefficient on %s slot (got %s) but \
                 hypothesis is not Eq — SDK should have rejected this cert"
      slot (Z.to_string cz)

(* --- False-goal closer --------------------------------------------- *)

(* General-arity False-goal closer. Folds the witness's coefficient
   list left-to-right, tracking strictness:

     1. For each (name, c): normalize hypothesis to either [a ≤ 0]
        (Le-form, [strict=false]) or [a < 0] (Lt-form, [strict=true],
        R only). Build [c * a] with proof [c * a ≤ 0] via
        [mul_nonneg_nonpos] or [c * a < 0] via [mul_pos_neg].
     2. Left-associative sum: accumulator [(s_i, s_i_proof, s_strict)].
        Each step picks the [add_*] combinator from the 4-way cross
        product (acc_strict × prod_strict):
          Le+Le→Le ([add_nonpos]); Le+Lt→Lt ([add_le_lt]);
          Lt+Le→Lt ([add_lt_le]); Lt+Lt→Lt ([add_neg]).
     3. Dispatch on final [s_strict]:
          false: [farkas_contradict_n] with [0 < K].
          true:  [farkas_contradict_n_strict] with [0 ≤ K]; K may be 0
                 (the [(h1 : 5 < x) (h2 : x < 5) ⊢ False] case has
                 [(5 - x) + (x - 5) = 0] as the linear sum, with
                 strictness from h1 and h2 carrying the contradiction).

   Z always stays in the Le-form branch ([strict] is forced false via
   the +1 trick at normalization time); R can land in either branch. *)
let close_term_false (u : universe) env sigma (ir : Ir.t)
    ?(nat_atoms : (string * EConstr.t) list = [])
    (entries : (string * Z.t) list) : unit Proofview.tactic =
  (* Pre-process: drop zero-coefficient entries (they contribute
     nothing to the Farkas sum), and split each remaining entry's
     signed coefficient into (|c|, flipped). [flipped=true] is only
     sound on Eq hypotheses — [check_signed_coef] enforces this. *)
  let processed = List.filter_map (fun (name, c) ->
    if Z.sign c = 0 then None
    else
      let id = Names.Id.of_string name in
      let is_eq = is_eq_hypothesis env sigma id in
      check_signed_coef ~slot:name env sigma c is_eq;
      let flipped = Z.sign c < 0 in
      let c_abs = Z.abs c in
      Some (name, c_abs, flipped)) entries in
  if List.length processed < 1 then
    unsupported "term_mode: all coefficients are zero (or empty witness) — \
                 arity ≥ 1 nonzero entry required";
  (* Normalize each entry. Builds (c_econstr, h_c_proof, a_econstr,
     h_a_proof, a_strict) per entry — the [h_c] proof varies with
     [a_strict] (strict premise needs [0 < c] from [pos_is_pos] so
     the product is strictly negative; Le premise uses [0 <= c]). *)
  let normalized = List.map (fun (name, c_abs, flipped) ->
    let id = Names.Id.of_string name in
    let { expr = a; proof = h_a; strict = a_strict } =
      normalize_hypothesis u env sigma id ~nat_atoms ~flipped
    in
    let c_econstr = u.lit c_abs in
    let h_c =
      if a_strict then u.pos_is_pos c_abs else u.pos_is_nonneg c_abs
    in
    (c_econstr, h_c, a, h_a, a_strict)) processed in
  (* Build (c_i * a_i, proof: c_i * a_i ≤ 0 OR < 0, prod_strict). *)
  let need_mul_pos_neg () =
    match u.mul_pos_neg with
    | Some lemma -> lemma
    | None ->
      unsupported "term_mode: strict premise on universe %s but \
                   [mul_pos_neg] not wired" u.name
  in
  let products = List.map (fun (c_econstr, h_c, a, h_a, a_strict) ->
    let prod = EConstr.mkApp (u.mul, [| c_econstr; a |]) in
    let proof =
      if a_strict then
        EConstr.mkApp (need_mul_pos_neg (),
          [| c_econstr; a; h_c; h_a |])
      else
        EConstr.mkApp (u.mul_nonneg_nonpos,
          [| c_econstr; a; h_c; h_a |])
    in
    (prod, proof, a_strict)) normalized in
  (* Left-associative fold: (acc, acc_proof, acc_strict). The add
     combinator depends on (acc_strict, prod_strict). *)
  let pick_add acc_strict prod_strict =
    match acc_strict, prod_strict with
    | false, false -> u.add_nonpos
    | false, true ->
      (match u.add_le_lt with
       | Some l -> l
       | None ->
         unsupported "term_mode: Le+Lt sum step but [add_le_lt] not \
                      wired on universe %s" u.name)
    | true, false ->
      (match u.add_lt_le with
       | Some l -> l
       | None ->
         unsupported "term_mode: Lt+Le sum step but [add_lt_le] not \
                      wired on universe %s" u.name)
    | true, true ->
      (match u.add_neg with
       | Some l -> l
       | None ->
         unsupported "term_mode: Lt+Lt sum step but [add_neg] not \
                      wired on universe %s" u.name)
  in
  let (sum_econstr, sum_proof, sum_strict) = match products with
    | [] -> assert false
    | (p0, h0, s0) :: rest ->
      List.fold_left (fun (acc_e, acc_h, acc_s) (p, h, ps) ->
        let new_sum = EConstr.mkApp (u.add, [| acc_e; p |]) in
        let add_lemma = pick_add acc_s ps in
        let new_proof = EConstr.mkApp (add_lemma,
          [| acc_e; p; acc_h; h |]) in
        (new_sum, new_proof, acc_s || ps)) (p0, h0, s0) rest
  in
  let k_z =
    compute_residual ~require_strict:(not sum_strict) ir entries
  in
  let k_constr = u.lit k_z in
  let hk =
    if sum_strict then
      (* Strict-aware contradiction: [0 ≤ K], may be zero. *)
      if Z.sign k_z = 0 then force r_zero_nonneg_ref
      else u.pos_is_nonneg k_z
    else u.pos_is_pos k_z
  in
  let contradict_lemma =
    if sum_strict then
      (match u.farkas_contradict_n_strict with
       | Some l -> l
       | None ->
         unsupported "term_mode: strict-aware fold reached final step \
                      but [farkas_contradict_n_strict] not wired on \
                      universe %s" u.name)
    else u.farkas_contradict_n
  in
  let refine_tac : unit Proofview.tactic =
    Refine.refine ~typecheck:true (fun sigma ->
      let heq_type =
        EConstr.mkApp (force r_eq, [| u.ty; sum_econstr; k_constr |])
      in
      let sigma, heq_evar = Evarutil.new_evar env sigma heq_type in
      let term =
        EConstr.mkApp (contradict_lemma,
          [| sum_econstr; k_constr; sum_proof; hk; heq_evar |])
      in
      (sigma, term))
  in
  Proofview.tclTHEN refine_tac invoke_ring

(* --- unified arity-N comparison-goal closer ----------------------- *)

(* Unified comparison-goal path. Converts [b <= c] / [b < c] to
   [False] by applying a wrapper of shape [(c <(=) b -> False) -> b
   <(=) c], introducing [neg_goal] as a regular Coq hypothesis, and
   delegating to [close_term_false]. The arity-N strict-aware fold
   in [close_term_false] handles all premises uniformly — including
   [neg_goal], whose normalization (Z: +1 trick; R: strict-
   preserving) flows through the existing per-universe machinery. *)
let close_term_comparison (u : universe) (ir : Ir.t)
    ?(nat_atoms : (string * EConstr.t) list = [])
    ?(nat_goal : bool = false)
    (entries : (string * Z.t) list)
    (tag : universe_tag) (goal_shape : [`Le | `Lt])
  : unit Proofview.tactic =
  let _ = u in
  (* R3-M1: a ℕ comparison goal enters through the constructive ℕ
     wrappers; the introduced [neg_goal] is a positive ℕ strict
     fact the cast layer transfers like any other hypothesis. *)
  let wrapper_name = match tag, goal_shape, nat_goal with
    | _, `Le, true -> "nat_le_via_lt"
    | _, `Lt, true -> "nat_lt_via_le"
    | U_Z, `Le, false -> "z_le_via_lt"
    | U_Z, `Lt, false -> "z_lt_via_le"
    | U_R, `Le, false -> "r_le_via_lt"
    | U_R, `Lt, false -> "r_lt_via_le"
  in
  let apply_wrapper = invoke_tactic (Printf.sprintf "apply %s" wrapper_name) in
  let intro_neg = invoke_tactic "intro neg_goal" in
  let close_false_tac =
    Proofview.Goal.enter (fun gl' ->
      let env' = Proofview.Goal.env gl' in
      let sigma' = Proofview.Goal.sigma gl' in
      try close_term_false u env' sigma' ir ~nat_atoms entries
      with Unsupported msg ->
        CErrors.user_err Pp.(str (Printf.sprintf "proof_broker_term: %s" msg)))
  in
  Proofview.tclTHEN apply_wrapper
    (Proofview.tclTHEN intro_neg close_false_tac)

(* --- top-level Tier 1 closer --------------------------------------- *)

let close_term (ir : Ir.t)
    ?(nat_atoms : (string * EConstr.t) list = [])
    (witness : Yojson.Safe.t) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    try
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let goal_ty = Proofview.Goal.concl gl in
    let entries = parse_witness witness in
    if List.length entries < 1 then
      unsupported "term_mode: empty witness — arity ≥ 1 required";
    let neg_entry = List.find_opt (fun (n, _) -> n = "neg_goal") entries in
    let kind = goal_kind sigma goal_ty in
    let u = universe_for_ir ir in
    match kind, neg_entry with
    | Some Goal_false, None ->
      close_term_false u env sigma ir ~nat_atoms entries
    | Some (Goal_nat_le _), Some _ ->
      close_term_comparison u ir ~nat_atoms ~nat_goal:true entries U_Z `Le
    | Some (Goal_nat_lt _), Some _ ->
      close_term_comparison u ir ~nat_atoms ~nat_goal:true entries U_Z `Lt
    | Some (Goal_nat_le _), None | Some (Goal_nat_lt _), None ->
      unsupported "term_mode: witness lacks neg_goal but goal is a ℕ \
                   comparison (cert/goal mismatch)"
    | Some Goal_nat_eq, _ ->
      unsupported "term_mode: ℕ equality goals are pre-split via \
                   Nat.le_antisymm by the dispatcher before reaching \
                   close_term (internal invariant violation)"
    | Some (Goal_le (_, _, tag)), Some _ ->
      close_term_comparison u ir ~nat_atoms entries tag `Le
    | Some (Goal_lt (_, _, tag)), Some _ ->
      close_term_comparison u ir ~nat_atoms entries tag `Lt
    | Some Goal_false, Some _ ->
      unsupported "term_mode: witness names neg_goal but goal is False \
                   (cert/goal mismatch)"
    | Some (Goal_le _), None | Some (Goal_lt _), None ->
      unsupported "term_mode: witness lacks neg_goal but goal is a comparison \
                   (cert/goal mismatch)"
    | Some (Goal_ge _), _ | Some (Goal_gt _), _ | Some (Goal_eq _), _ ->
      unsupported "term_mode: goal kind ≥/>/= should have been normalized \
                   to ≤/</antisymm by the closer dispatcher before reaching \
                   close_term (internal invariant violation)"
    | None, _ ->
      unsupported "term_mode: goal shape not recognized (expected False, \
                   _ <= _, _ < _, _ >= _, _ > _, or _ = _ over Z or R)"
    with Unsupported msg ->
      CErrors.user_err Pp.(str (Printf.sprintf "proof_broker_term: %s" msg)))

(* --- Tier 2 case-split closer -------------------------------------- *)

(* Parse one cert lemma object into (case_shell, witness). *)
let parse_case_lemma (j : Yojson.Safe.t) : Ir.shell_term * Yojson.Safe.t =
  match j with
  | `Assoc fields ->
    (match List.assoc_opt "case" fields, List.assoc_opt "witness" fields with
     | Some case_json, Some witness_json ->
       let case_shell =
         try Proof_broker.Codec.shell_of_json case_json
         with _ ->
           unsupported "term_mode: lemma's 'case' isn't a valid shell"
       in
       (case_shell, witness_json)
     | _ ->
       unsupported "term_mode: lemma missing 'case' or 'witness' field")
  | _ ->
    unsupported "term_mode: lemma entry not a JSON object"

let parse_disjunctive_hyp_name (sh : Yojson.Safe.t option) : string =
  match sh with
  | Some (`Assoc kvs) ->
    (match List.assoc_opt "disjunctive_hypothesis" kvs with
     | Some (`String s) -> s
     | _ ->
       unsupported "term_mode: structural_hint missing \
                    'disjunctive_hypothesis' string")
  | _ ->
    unsupported "term_mode: structural_hint is required for Tier 2 \
                 case-split"

(* Order the parsed lemmas by which disjunct each one matches.
   Returns a list of (case_shell, witness) in disjunct-index order
   (i.e. position 0 is the left disjunct of the destruct pattern,
   position 1 is the right, ...).

   Bridges the SDK's [Verifier.match_disjunct_index] (which works on
   compiled linear forms, so it absorbs sign-equivalent rewrites
   between the cert's case and the IR's disjunct) to the bridge's
   per-branch destruct ordering. *)
let order_lemmas_by_disjunct ~fragment
    (lemmas : (Ir.shell_term * Yojson.Safe.t) list)
    (disjuncts : Ir.shell_term list)
  : (Ir.shell_term * Yojson.Safe.t) list =
  let n = List.length disjuncts in
  let by_index = Array.make n None in
  List.iter (fun (case_shell, witness) ->
    match Verifier.match_disjunct_index ~fragment case_shell disjuncts with
    | Some i ->
      if by_index.(i) <> None then
        unsupported "term_mode: two lemmas match the same disjunct (index %d)" i;
      by_index.(i) <- Some (case_shell, witness)
    | None ->
      unsupported "term_mode: a lemma's case doesn't match any disjunct"
  ) lemmas;
  Array.to_list by_index
  |> List.mapi (fun i o ->
       match o with
       | Some p -> p
       | None ->
         unsupported "term_mode: disjunct index %d has no matching lemma" i)

(* Build the per-branch closure tactic for one (case, witness) pair.
   After [destruct hyp as [case | case | ...]], the current Coq context
   has [case : <disjunct>] in scope. We extend the IR with a hypothesis
   named "case" (matching what the SDK verifier did), then call the
   existing Tier 1 [close_term] on the extended IR + lemma's witness.
   The witness references [case] by that name; lookup resolves to the
   destruct-introduced Coq hypothesis. *)
let per_branch_close (ir : Ir.t)
    (case_shell : Ir.shell_term) (witness : Yojson.Safe.t)
  : unit Proofview.tactic =
  let extended_ir : Ir.t = {
    ir with
    context = { ir.context with
      hypotheses = ir.context.hypotheses
                   @ [ { Ir.name = "case"; shell = case_shell } ]
    }
  } in
  close_term extended_ir witness

(* Tier 2 case-split closer entry point.

   Scope: an arity-N disjunctive hypothesis ([A \/ B], [A \/ B \/ C],
   …) of LIA / LRA atoms, each branch closed by one Tier 1 Farkas
   witness. [disjuncts_of] flattens the right-nested [Or] to a list;
   [build_destruct_pattern n_disjuncts] emits the matching nested
   destruct pattern and [order_lemmas_by_disjunct] aligns the
   witnesses to the branches. Only arity < 2 is rejected. (Audit #18:
   an earlier comment here said "restrict to arity 2"; that was stale
   — the code has been arity-N.) *)
let close_term_case_split (ir : Ir.t)
    (lemmas_used : Yojson.Safe.t list)
    (structural_hint : Yojson.Safe.t option)
  : unit Proofview.tactic =
  Proofview.Goal.enter (fun _gl ->
    try
      let hyp_name = parse_disjunctive_hyp_name structural_hint in
      let disj_hyp =
        match
          List.find_opt (fun (h : Ir.hypothesis) -> h.name = hyp_name)
            ir.context.hypotheses
        with
        | Some h -> h
        | None ->
          unsupported "term_mode: disjunctive hypothesis %s not in IR" hyp_name
      in
      let disjuncts = Alethe_farkas.disjuncts_of disj_hyp.shell in
      let n_disjuncts = List.length disjuncts in
      if n_disjuncts < 2 then
        unsupported "term_mode: disjunctive hypothesis has %d disjuncts \
                     (expected ≥ 2)" n_disjuncts;
      let parsed = List.map parse_case_lemma lemmas_used in
      if List.length parsed <> n_disjuncts then
        unsupported "term_mode: lemma count (%d) doesn't match disjunct \
                     count (%d)" (List.length parsed) n_disjuncts;
      let fragment = Farkas.effective_fragment ir in
      let ordered = order_lemmas_by_disjunct ~fragment parsed disjuncts in
      let branches =
        List.map (fun (case_shell, witness) ->
          per_branch_close ir case_shell witness) ordered
      in
      (* Build an arity-N destruct pattern. Rocq's [destruct] on
         a right-associated chain [A \/ (B \/ (C \/ ...))] requires a
         matching nested OrAndIntroPattern. For [n] disjuncts:
           n=2: [case | case]
           n=3: [case | [case | case]]
           n=4: [case | [case | [case | case]]]
         The pattern recurses on the right child to mirror the [Or]
         tree's right-spine. Verified empirically — the flat form
         [case | case | case] errors with "expects a disjunctive
         pattern with 2 branches" since each [Or] node is binary. *)
      let rec build_destruct_pattern n =
        if n <= 2 then "case | case"
        else Printf.sprintf "case | [%s]" (build_destruct_pattern (n - 1))
      in
      let pattern = build_destruct_pattern n_disjuncts in
      let destruct_tac =
        invoke_tactic (Printf.sprintf "destruct %s as [%s]" hyp_name pattern)
      in
      Proofview.tclTHEN destruct_tac (Proofview.tclDISPATCH branches)
    with Unsupported msg ->
      CErrors.user_err Pp.(str (Printf.sprintf "proof_broker_term: %s" msg)))

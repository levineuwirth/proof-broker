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
let r_farkas_le_goal_2_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_farkas_le_goal_2")
let r_farkas_lt_goal_2_ref =
  lazy (safe_constr_of_ref "proof_broker.term_mode.r_farkas_lt_goal_2")
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
let z_farkas_le_goal_2 = lazy (safe_constr_of_ref "proof_broker.term_mode.farkas_le_goal_2")
let z_farkas_lt_goal_2 = lazy (safe_constr_of_ref "proof_broker.term_mode.farkas_lt_goal_2")
let z_pos_is_pos      = lazy (safe_constr_of_ref "proof_broker.term_mode.pos_is_pos")
let z_pos_is_nonneg   = lazy (safe_constr_of_ref "proof_broker.term_mode.pos_is_nonneg")
let z_farkas_contradict_n = lazy (safe_constr_of_ref "proof_broker.term_mode.farkas_contradict_n")
let z_mul_nonneg_nonpos   = lazy (safe_constr_of_ref "proof_broker.term_mode.z_mul_nonneg_nonpos")
let z_add_nonpos          = lazy (safe_constr_of_ref "proof_broker.term_mode.z_add_nonpos")

(* R-typed helpers (mirror of the Z ones for the LRA Tier 1 / Tier 2
   case-split paths). *)
let r_le_to_le0_ref     = lazy (safe_constr_of_ref "proof_broker.term_mode.r_le_to_le0")
let r_ge_to_le0_ref     = lazy (safe_constr_of_ref "proof_broker.term_mode.r_ge_to_le0")
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
   helpers under one record, so [close_term_false] / [close_term_goal]
   / [close_term_case_split] are universe-polymorphic over Z and R.
   The dispatch picks the universe by inspecting [Farkas.effective_fragment]
   of the IR being closed: "LRA" → [r_universe], otherwise [z_universe].
   *)
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
   [close_term] picks the right helper ([z_farkas_le_goal_2] vs
   [r_farkas_le_goal_2]) and neg_norm shape (+1 trick for LIA only). *)
type universe_tag = U_Z | U_R

type goal_kind =
  | Goal_false
  | Goal_le of EConstr.t * EConstr.t * universe_tag
  | Goal_lt of EConstr.t * EConstr.t * universe_tag
  | Goal_ge of EConstr.t * EConstr.t * universe_tag
  | Goal_gt of EConstr.t * EConstr.t * universe_tag
  | Goal_eq of EConstr.t * EConstr.t * universe_tag

let goal_kind sigma (ty : EConstr.t) : goal_kind option =
  if eq_ref sigma ty r_False then Some Goal_false
  else match EConstr.kind sigma ty with
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

let parse_witness (w : Yojson.Safe.t) : (string * Z.t) list =
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
           if not (Z.equal r.den Z.one) then
             unsupported "term_mode: rational coefficient %s; integer-only \
                          for now (clear-denominators not yet wired)" c_str;
           (h, r.num)
         | _ -> unsupported "term_mode: witness entry not an object")
         xs
     | _ -> unsupported "term_mode: witness missing 'coefficients' list")
  | _ -> unsupported "term_mode: witness is not a JSON object"

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
      | Ok (Eq _) ->
        unsupported
          "term_mode: hypothesis %s compiles to Eq — equality hypotheses \
           in the witness aren't wired yet" name
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
   [h : T.gt a b] over T ∈ {Z, R}, produce a [normalized_hyp] using
   the universe's normalization helpers. Detection is by the inner
   head ref. Strict shapes route through different paths per universe:

     * Z (LIA): [lt_to_le0] / [gt_to_le0] (+1 trick), strict = false.
     * R (LRA): [lt_to_lt0] / [gt_to_lt0] (strictness preserving),
                strict = true; the strict-aware fold in the caller
                picks the right [mul_*] / [add_*] / [contradict_n_*]
                combinators from there. *)
let normalize_hypothesis (u : universe) env sigma (id : Names.Id.t)
  : normalized_hyp =
  let decl = Environ.lookup_named id env in
  let ty = EConstr.of_constr (Context.Named.Declaration.get_type decl) in
  let h_term = EConstr.mkVar id in
  match EConstr.kind sigma ty with
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
                   %s.le / %s.ge / %s.lt / %s.gt \
                   (head not recognized for this universe)"
        (Names.Id.to_string id) u.name u.name u.name u.name
  | _ ->
    unsupported "term_mode: hypothesis %s is not a binary application"
      (Names.Id.to_string id)

(* --- ring tactic invocation (closes the Heq subgoal) --------------- *)

let invoke_ring : unit Proofview.tactic =
  Proofview.Goal.enter (fun _ ->
    let raw = Procq.parse_string Ltac_plugin.Pltac.tactic "ring" in
    let glob =
      Ltac_plugin.Tacintern.intern_pure_tactic
        (Ltac_plugin.Tacintern.make_empty_glob_sign ~strict:false) raw
    in
    Ltac_plugin.Tacinterp.eval_tactic glob)

(* --- shared coefficient-witness builders --------------------------- *)

let check_positive_coef ~slot (cz : Z.t) =
  if Z.sign cz <= 0 then
    unsupported "term_mode: non-positive coefficient on %s slot (got %s); \
                 only positive integers wired today"
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
    (entries : (string * Z.t) list) : unit Proofview.tactic =
  let n = List.length entries in
  if n < 1 then
    unsupported "term_mode: empty witness — arity ≥ 1 required";
  List.iter (fun (name, c) -> check_positive_coef ~slot:name c) entries;
  (* Normalize each entry. Builds (c_econstr, h_c_proof, a_econstr,
     h_a_proof, a_strict) per entry — the [h_c] proof varies with
     [a_strict] (strict premise needs [0 < c] from [pos_is_pos] so
     the product is strictly negative; Le premise uses [0 <= c]). *)
  let normalized = List.map (fun (name, c) ->
    let id = Names.Id.of_string name in
    let { expr = a; proof = h_a; strict = a_strict } =
      normalize_hypothesis u env sigma id
    in
    let c_econstr = u.lit c in
    let h_c =
      if a_strict then u.pos_is_pos c else u.pos_is_nonneg c
    in
    (c_econstr, h_c, a, h_a, a_strict)) entries in
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

(* --- non-False goal closer (Le / Lt over Z only) ------------------- *)

(* Proof-shape choice for the comparison-goal helper:

     * [PS_K_strict]   (Z helpers, R Lt-goal):
         [hcng = u.pos_is_nonneg cng_z]  (0 ≤ cng)
         [hk   = u.pos_is_pos k_z]       (0 < K)
         compute_residual requires K > 0
     * [PS_cng_strict] (R Le-goal only):
         [hcng = u.pos_is_pos cng_z]     (0 < cng — strictness comes
                                          from the LRA neg_goal Lt-shape,
                                          which is what produces the
                                          contradiction when [K = 0])
         [hk   = u.pos_is_nonneg k_z]    (0 ≤ K — may be zero in the
                                          trivial-equality case)
         compute_residual allows K = 0

   PS_cng_strict is the strict-aware path that handles the LRA Le-goal
   trivial-equality case (eg [n ≤ 5] ⊢ [n ≤ 5] post-Rle_antisym, where
   the Farkas residual is exactly zero — no LIA +1 trick over R). *)
type goal_proof_shape = PS_K_strict | PS_cng_strict

(* Goal closer for [b <= c] / [b < c] — universe-polymorphic, callers
   pass the universe explicitly (chosen from the [goal_kind]'s
   [universe_tag]) along with the helper lemma reference, neg_norm
   builder, and the proof-shape choice. The neg_norm shape differs
   by universe:

     * Z (LIA), Le goal: c + 1 - b  (the +1 trick image of [c < b])
     * Z (LIA), Lt goal: c - b      (no +1 trick on the [c <= b] negation)
     * R (LRA), Le goal: c - b      (no +1 trick over R; the helper
                                    uses strict cng > 0 to produce a
                                    strict combination instead)
     * R (LRA), Lt goal: c - b      (same shape; standard K > 0 path)

   The Tier 2 case-split path's per-branch goals stay [False] after
   destruct, so they go through [close_term_false], not this closer. *)
let close_term_goal (u : universe) env sigma (ir : Ir.t)
    ~helper ~neg_norm ~(proof_shape : goal_proof_shape)
    (b : EConstr.t) (c : EConstr.t)
    (real_name : string) (c1z : Z.t) (cng_z : Z.t)
    : unit Proofview.tactic =
  let _ = b in let _ = c in
  check_positive_coef ~slot:"c1" c1z;
  check_positive_coef ~slot:"neg_goal" cng_z;
  let id1 = Names.Id.of_string real_name in
  let { expr = a1; proof = h1; strict = h1_strict } =
    normalize_hypothesis u env sigma id1
  in
  if h1_strict then
    unsupported "term_mode: strict [<] / [>] hypothesis %s on a \
                 comparison-goal closer is out of scope (only False-goal \
                 supports strict premises today — comparison-goal needs \
                 a strict-aware variant of [farkas_le_goal_2] / \
                 [farkas_lt_goal_2], future scope)"
      real_name;
  let c1 = u.lit c1z in
  let cng = u.lit cng_z in
  let require_strict = match proof_shape with
    | PS_K_strict -> true
    | PS_cng_strict -> false
  in
  let k_z =
    compute_residual ~require_strict ir
      [(real_name, c1z); ("neg_goal", cng_z)]
  in
  let k_constr = u.lit k_z in
  (* Per [proof_shape]: K_strict path uses pos_is_pos for K, pos_is_nonneg
     for cng (Z standard); cng_strict path swaps them (R Le-goal). The
     cng_strict path also has to handle [k_z = 0] specifically since
     pos_is_nonneg / pos_is_pos both require a [positive] argument. *)
  let (hcng, hk) = match proof_shape with
    | PS_K_strict ->
      (u.pos_is_nonneg cng_z, u.pos_is_pos k_z)
    | PS_cng_strict ->
      let hk =
        if Z.sign k_z = 0 then force r_zero_nonneg_ref
        else u.pos_is_nonneg k_z
      in
      (u.pos_is_pos cng_z, hk)
  in
  let hc1 = u.pos_is_nonneg c1z in
  let refine_tac : unit Proofview.tactic =
    Refine.refine ~typecheck:true (fun sigma ->
      let heq_type =
        let mul x y = EConstr.mkApp (u.mul, [| x; y |]) in
        let add x y = EConstr.mkApp (u.add, [| x; y |]) in
        let lhs = add (mul c1 a1) (mul cng neg_norm) in
        EConstr.mkApp (force r_eq, [| u.ty; lhs; k_constr |])
      in
      let sigma, heq_evar = Evarutil.new_evar env sigma heq_type in
      let term =
        EConstr.mkApp (helper,
          [| b; c; a1; h1;
             c1; cng; hc1; hcng;
             k_constr; hk; heq_evar |])
      in
      (sigma, term))
  in
  Proofview.tclTHEN refine_tac invoke_ring

(* Z-side Le-goal neg_norm: +1 trick produces [c + 1 - b]. *)
let neg_norm_z_le b c : EConstr.t =
  let one = z_lit Z.one in
  let c_plus_1 = EConstr.mkApp (force r_Zadd, [| c; one |]) in
  EConstr.mkApp (force r_Zsub, [| c_plus_1; b |])

(* Z-side Lt-goal neg_norm: no +1, just [c - b]. *)
let neg_norm_z_lt b c : EConstr.t =
  EConstr.mkApp (force r_Zsub, [| c; b |])

(* R-side neg_norm (both Le and Lt goals): [c - b]. The helper
   lemma's destruct handles the strictness weakening; OCaml just
   constructs the linear-form LHS. *)
let neg_norm_r b c : EConstr.t =
  EConstr.mkApp (force r_Rminus, [| c; b |])

(* --- top-level Tier 1 closer --------------------------------------- *)

let close_term (ir : Ir.t) (witness : Yojson.Safe.t) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    try
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let goal_ty = Proofview.Goal.concl gl in
    let entries = parse_witness witness in
    if List.length entries < 1 then
      unsupported "term_mode: empty witness — arity ≥ 1 required";
    let neg_entry = List.find_opt (fun (n, _) -> n = "neg_goal") entries in
    let real_entries = List.filter (fun (n, _) -> n <> "neg_goal") entries in
    let kind = goal_kind sigma goal_ty in
    let u = universe_for_ir ir in
    (* For the comparison-goal case, pick the helper + neg_norm by
       (kind × universe_tag). The universe used for hypothesis
       normalization comes from [universe_for_ir ir] above and must
       agree with the tag — for non-degenerate IRs they always
       agree (LRA fragment ↔ Real-typed comparator), so we trust [u]. *)
    let goal_dispatch ~slot ~helper ~neg_norm ~proof_shape b c
        real_name c1z cng_z =
      match real_entries with
      | [(rn, c1z')] when rn = real_name && Z.equal c1z' c1z ->
        close_term_goal u env sigma ir ~helper ~neg_norm ~proof_shape
          b c real_name c1z cng_z
      | _ ->
        unsupported "term_mode: arity-2 %s goal expects one real-hypothesis \
                      entry alongside neg_goal (got %d real entries)"
          slot (List.length real_entries)
    in
    let single_real_entry () =
      match real_entries with
      | [(real_name, c1z)] -> Some (real_name, c1z)
      | _ -> None
    in
    match kind, neg_entry with
    | Some Goal_false, None ->
      close_term_false u env sigma ir entries
    | Some (Goal_le (b, c, U_Z)), Some (_, cng_z) ->
      (match single_real_entry () with
       | Some (real_name, c1z) ->
         goal_dispatch ~slot:"≤"
           ~helper:(force z_farkas_le_goal_2)
           ~neg_norm:(neg_norm_z_le b c)
           ~proof_shape:PS_K_strict
           b c real_name c1z cng_z
       | None ->
         unsupported "term_mode: arity-2 ≤ goal expects exactly one real \
                       entry (got %d)" (List.length real_entries))
    | Some (Goal_lt (b, c, U_Z)), Some (_, cng_z) ->
      (match single_real_entry () with
       | Some (real_name, c1z) ->
         goal_dispatch ~slot:"<"
           ~helper:(force z_farkas_lt_goal_2)
           ~neg_norm:(neg_norm_z_lt b c)
           ~proof_shape:PS_K_strict
           b c real_name c1z cng_z
       | None ->
         unsupported "term_mode: arity-2 < goal expects exactly one real \
                       entry (got %d)" (List.length real_entries))
    | Some (Goal_le (b, c, U_R)), Some (_, cng_z) ->
      (match single_real_entry () with
       | Some (real_name, c1z) ->
         goal_dispatch ~slot:"≤ (R)"
           ~helper:(force r_farkas_le_goal_2_ref)
           ~neg_norm:(neg_norm_r b c)
           ~proof_shape:PS_cng_strict
           b c real_name c1z cng_z
       | None ->
         unsupported "term_mode: arity-2 ≤ (R) goal expects exactly one real \
                       entry (got %d)" (List.length real_entries))
    | Some (Goal_lt (b, c, U_R)), Some (_, cng_z) ->
      (match single_real_entry () with
       | Some (real_name, c1z) ->
         goal_dispatch ~slot:"< (R)"
           ~helper:(force r_farkas_lt_goal_2_ref)
           ~neg_norm:(neg_norm_r b c)
           ~proof_shape:PS_K_strict
           b c real_name c1z cng_z
       | None ->
         unsupported "term_mode: arity-2 < (R) goal expects exactly one real \
                       entry (got %d)" (List.length real_entries))
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

(* Invoke a tactic by parsing its string form (same idiom the
   reifier wrapping around [Procq.parse_string] uses). *)
let invoke_tactic (src : string) : unit Proofview.tactic =
  Proofview.Goal.enter (fun _ ->
    let raw = Procq.parse_string Ltac_plugin.Pltac.tactic src in
    let glob =
      Ltac_plugin.Tacintern.intern_pure_tactic
        (Ltac_plugin.Tacintern.make_empty_glob_sign ~strict:false) raw
    in
    Ltac_plugin.Tacinterp.eval_tactic glob)

(* Tier 2 case-split closer entry point.

   Scope today: arity-2 disjunctive hypothesis ([A \/ B]) of LIA /
   LRA atoms, each closed by one Tier 1 Farkas witness. Higher arity
   (e.g. [A \/ B \/ C]) needs a destruct pattern of corresponding
   nesting and the SDK's [disjuncts_of] flattens to a list — we
   restrict to arity 2 here, matching the existing fixture, and the
   extension is mechanical. *)
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
      if List.length disjuncts <> 2 then
        unsupported "term_mode: only arity-2 disjunctive hypotheses wired \
                     today (got %d disjuncts)" (List.length disjuncts);
      let parsed = List.map parse_case_lemma lemmas_used in
      if List.length parsed <> List.length disjuncts then
        unsupported "term_mode: lemma count (%d) doesn't match disjunct \
                     count (%d)" (List.length parsed) (List.length disjuncts);
      let fragment = Farkas.effective_fragment ir in
      let ordered = order_lemmas_by_disjunct ~fragment parsed disjuncts in
      let branches =
        List.map (fun (case_shell, witness) ->
          per_branch_close ir case_shell witness) ordered
      in
      let destruct_tac =
        invoke_tactic (Printf.sprintf "destruct %s as [case | case]" hyp_name)
      in
      Proofview.tclTHEN destruct_tac (Proofview.tclDISPATCH branches)
    with Unsupported msg ->
      CErrors.user_err Pp.(str (Printf.sprintf "proof_broker_term: %s" msg)))

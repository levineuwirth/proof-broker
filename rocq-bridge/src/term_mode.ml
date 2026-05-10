module Cert = Proof_broker.Certificate
module Farkas = Proof_broker.Farkas
module L = Proof_broker.Linear_arith
module Ir = Proof_broker.Ir

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
let r_le_to_le0       = lazy (safe_constr_of_ref "proof_broker.term_mode.le_to_le0")
let r_ge_to_le0       = lazy (safe_constr_of_ref "proof_broker.term_mode.ge_to_le0")
let r_farkas_le_2     = lazy (safe_constr_of_ref "proof_broker.term_mode.farkas_le_2")
let r_farkas_le_goal_2 = lazy (safe_constr_of_ref "proof_broker.term_mode.farkas_le_goal_2")
let r_farkas_lt_goal_2 = lazy (safe_constr_of_ref "proof_broker.term_mode.farkas_lt_goal_2")
let r_pos_is_pos      = lazy (safe_constr_of_ref "proof_broker.term_mode.pos_is_pos")
let r_pos_is_nonneg   = lazy (safe_constr_of_ref "proof_broker.term_mode.pos_is_nonneg")

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
let r_xH   = lazy (safe_constr_of_ref "num.pos.xH")
let r_xO   = lazy (safe_constr_of_ref "num.pos.xO")
let r_xI   = lazy (safe_constr_of_ref "num.pos.xI")

let force lz =
  match Lazy.force lz with
  | Some t -> t
  | None ->
    unsupported "term_mode: a required lib_ref isn't bound — make sure \
                 ProofBrokerTermMode.v is imported and ZArith is in scope"

let eq_ref sigma a (lz : EConstr.t option Lazy.t) : bool =
  match Lazy.force lz with
  | Some c -> EConstr.eq_constr_nounivs sigma a c
  | None -> false

(* --- positive / Z literal construction ----------------------------- *)

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
let z_constr (n : Z.t) : EConstr.t =
  if Z.sign n < 0 then
    unsupported "term_mode: negative Z literal in cert (got %s)"
      (Z.to_string n);
  if Z.sign n = 0 then force r_Z0
  else EConstr.mkApp (force r_Zpos, [| positive_constr_of_z n |])

(* --- goal kind ----------------------------------------------------- *)

(* The six goal shapes term-mode recognizes. [Goal_false] / [Goal_le]
   / [Goal_lt] are handled directly here; [Goal_ge] / [Goal_gt] /
   [Goal_eq] are normalized to one of the three above by the
   recursive run_close_term in pb_rocq_main.ml before close_term
   sees them.

   Mirrors lean-bridge's [matchLiaGoal?] / [matchIntEqGoal?] —
   distinction is that Lean's [GE.ge a b ↘ LE.le b a] reduces by
   instance, so Lean's reifier emits [LE.le b a] directly. Rocq's
   [Z.ge] is a distinct constant (defined via [Z.compare]) so we
   route the normalization through the closer level. *)
type goal_kind =
  | Goal_false
  | Goal_le of EConstr.t * EConstr.t  (* b, c such that goal = (b <= c) *)
  | Goal_lt of EConstr.t * EConstr.t  (* b, c such that goal = (b < c) *)
  | Goal_ge of EConstr.t * EConstr.t  (* b, c such that goal = (b >= c) *)
  | Goal_gt of EConstr.t * EConstr.t  (* b, c such that goal = (b > c) *)
  | Goal_eq of EConstr.t * EConstr.t  (* a, b such that goal = (a = b : Z) *)

let goal_kind sigma (ty : EConstr.t) : goal_kind option =
  if eq_ref sigma ty r_False then Some Goal_false
  else match EConstr.kind sigma ty with
    | App (head, [| b; c |]) when eq_ref sigma head r_Zle -> Some (Goal_le (b, c))
    | App (head, [| b; c |]) when eq_ref sigma head r_Zlt -> Some (Goal_lt (b, c))
    | App (head, [| b; c |]) when eq_ref sigma head r_Zge -> Some (Goal_ge (b, c))
    | App (head, [| b; c |]) when eq_ref sigma head r_Zgt -> Some (Goal_gt (b, c))
    | App (head, [| ty_arg; a; b |])
        when eq_ref sigma head r_eq && eq_ref sigma ty_arg r_Z ->
      Some (Goal_eq (a, b))
    | _ -> None

(* --- witness parsing ----------------------------------------------- *)

(* Witness shape (per sdk/FFI_CONVENTIONS.md):
     {"coefficients": [{"hypothesis": <name>, "coefficient": <ratstr>}, ...]}
   We accept only integer coefficients here; rationals from a
   future LRA Tier 1 path would need clear-denominators logic
   (multiply both K and every c_i through by lcm of denominators —
   the cert remains valid, Farkas is scale-stable). *)
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

(* Compute K = constant value of [Σ c_i * f_i] where each f_i is the
   normalized [Le f_i] form of the named hypothesis. Delegates to
   the SDK's [Farkas.lookup_hypothesis] so the reserved name
   [neg_goal] resolves to the IR's goal-negation shell — the same
   path the verifier uses, which keeps the K we compute here
   consistent with the K the verifier validated. *)
let compute_residual (ir : Ir.t)
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
      | Ok (Le f) ->
        let scaled = L.scale (L.mk_rat_z coef Z.one) f in
        L.add acc scaled
      | Ok (Lt _) | Ok (Eq _) ->
        unsupported
          "term_mode: hypothesis %s compiles to Lt/Eq — only Le supported \
           in the arity-2 starter scope" name
      | Error e ->
        unsupported "term_mode: compile_hypothesis(%s) failed: %s" name e)
      L.zero entries
  in
  let k_rat = L.constant_value sum in
  if not (Z.equal k_rat.den Z.one) then
    unsupported "term_mode: residual %s is not an integer"
      (L.rat_to_string k_rat);
  if Z.sign k_rat.num <= 0 then
    unsupported "term_mode: residual K=%s must be positive (cert verifier \
                 should have caught this earlier)" (Z.to_string k_rat.num);
  k_rat.num

(* --- per-hypothesis (a_i, h_i' : a_i <= 0) construction ------------ *)

(* For a Rocq hypothesis [h : Z.le a b] or [h : Z.ge a b], produce
   the EConstr pair [(a_econstr, proof : a_econstr <= 0)] using
   [le_to_le0] / [ge_to_le0] from ProofBrokerTermMode.v.

   Mirror Farkas.compile_hypothesis's direction conventions:
     [Z.le a b]  → f = a - b
     [Z.ge a b]  → f = b - a *)
let normalize_hypothesis env sigma (id : Names.Id.t)
  : EConstr.t * EConstr.t =
  let decl = Environ.lookup_named id env in
  let ty = EConstr.of_constr (Context.Named.Declaration.get_type decl) in
  let h_term = EConstr.mkVar id in
  match EConstr.kind sigma ty with
  | App (head, [| a; b |]) ->
    if eq_ref sigma head r_Zle then
      let a_minus_b = EConstr.mkApp (force r_Zsub, [| a; b |]) in
      let proof =
        EConstr.mkApp (force r_le_to_le0, [| a; b; h_term |])
      in
      (a_minus_b, proof)
    else if eq_ref sigma head r_Zge then
      let b_minus_a = EConstr.mkApp (force r_Zsub, [| b; a |]) in
      let proof =
        EConstr.mkApp (force r_ge_to_le0, [| a; b; h_term |])
      in
      (b_minus_a, proof)
    else
      unsupported "term_mode: hypothesis %s has shape outside Z.le / Z.ge"
        (Names.Id.to_string id)
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

let nonneg_proof_of (cz : Z.t) : EConstr.t =
  EConstr.mkApp (force r_pos_is_nonneg, [| positive_constr_of_z cz |])

let pos_proof_of (cz : Z.t) : EConstr.t =
  EConstr.mkApp (force r_pos_is_pos, [| positive_constr_of_z cz |])

(* --- False-goal closer (existing behavior) ------------------------- *)

let close_term_false env sigma (ir : Ir.t)
    (entries : (string * Z.t) list) : unit Proofview.tactic =
  let (name1, c1z), (name2, c2z) =
    match entries with [a; b] -> (a, b) | _ -> assert false
  in
  check_positive_coef ~slot:"c1" c1z;
  check_positive_coef ~slot:"c2" c2z;
  let id1 = Names.Id.of_string name1 in
  let id2 = Names.Id.of_string name2 in
  let (a1, h1) = normalize_hypothesis env sigma id1 in
  let (a2, h2) = normalize_hypothesis env sigma id2 in
  let c1 = z_constr c1z in
  let c2 = z_constr c2z in
  let k_z = compute_residual ir entries in
  let k_constr = z_constr k_z in
  let hk = pos_proof_of k_z in
  let hc1 = nonneg_proof_of c1z in
  let hc2 = nonneg_proof_of c2z in
  let refine_tac : unit Proofview.tactic =
    Refine.refine ~typecheck:true (fun sigma ->
      let heq_type =
        let mul x y = EConstr.mkApp (force r_Zmul, [| x; y |]) in
        let add x y = EConstr.mkApp (force r_Zadd, [| x; y |]) in
        let lhs = add (mul c1 a1) (mul c2 a2) in
        EConstr.mkApp (force r_eq, [| force r_Z; lhs; k_constr |])
      in
      let sigma, heq_evar = Evarutil.new_evar env sigma heq_type in
      let term =
        EConstr.mkApp (force r_farkas_le_2,
          [| a1; a2; h1; h2;
             c1; c2; hc1; hc2;
             k_constr; hk; heq_evar |])
      in
      (sigma, term))
  in
  Proofview.tclTHEN refine_tac invoke_ring

(* --- non-False goal closer (Le / Lt) ------------------------------- *)

(* Generalized goal-closer for both [Le] and [Lt] cases. The two
   shapes differ only in:
     - which helper to apply ([farkas_le_goal_2] vs [farkas_lt_goal_2]),
     - the synthesized neg-goal-norm EConstr ([c + 1 - b] vs [c - b]),
   so we pass both as parameters. *)
let close_term_goal env sigma (ir : Ir.t)
    ~helper ~neg_norm
    (b : EConstr.t) (c : EConstr.t)
    (real_name : string) (c1z : Z.t) (cng_z : Z.t)
    : unit Proofview.tactic =
  let _ = b in let _ = c in
  check_positive_coef ~slot:"c1" c1z;
  check_positive_coef ~slot:"neg_goal" cng_z;
  let id1 = Names.Id.of_string real_name in
  let (a1, h1) = normalize_hypothesis env sigma id1 in
  let c1 = z_constr c1z in
  let cng = z_constr cng_z in
  let k_z =
    compute_residual ir [(real_name, c1z); ("neg_goal", cng_z)]
  in
  let k_constr = z_constr k_z in
  let hk = pos_proof_of k_z in
  let hc1 = nonneg_proof_of c1z in
  let hcng = nonneg_proof_of cng_z in
  let refine_tac : unit Proofview.tactic =
    Refine.refine ~typecheck:true (fun sigma ->
      let heq_type =
        let mul x y = EConstr.mkApp (force r_Zmul, [| x; y |]) in
        let add x y = EConstr.mkApp (force r_Zadd, [| x; y |]) in
        let lhs = add (mul c1 a1) (mul cng neg_norm) in
        EConstr.mkApp (force r_eq, [| force r_Z; lhs; k_constr |])
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

(* Build EConstr [c + 1 - b] for the [<=]-goal neg-goal slot.
   Matches the LIA +1-trick image of [~(b <= c)] ≡ [c + 1 <= b]
   ≡ [c + 1 - b <= 0] that [farkas_le_goal_2] expects. *)
let neg_norm_le b c : EConstr.t =
  let one = z_constr Z.one in
  let c_plus_1 = EConstr.mkApp (force r_Zadd, [| c; one |]) in
  EConstr.mkApp (force r_Zsub, [| c_plus_1; b |])

(* Build EConstr [c - b] for the [<]-goal neg-goal slot. Matches
   [~(b < c)] ≡ [c <= b] ≡ [c - b <= 0]. *)
let neg_norm_lt b c : EConstr.t =
  EConstr.mkApp (force r_Zsub, [| c; b |])

(* --- top-level closer ---------------------------------------------- *)

let close_term (ir : Ir.t) (witness : Yojson.Safe.t) : unit Proofview.tactic =
  (* Catch [Unsupported] inside the tactic so it surfaces as a
     well-shaped [CErrors.user_err] rather than a Rocq Anomaly. The
     caller in pb_rocq_main can't catch this from outside —
     Goal.enter defers execution past the try/with stack frame. *)
  Proofview.Goal.enter (fun gl ->
    try
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let goal_ty = Proofview.Goal.concl gl in
    let entries = parse_witness witness in
    if List.length entries <> 2 then
      unsupported "term_mode: arity %d witness — only arity 2 wired today \
                   (higher arities are mechanical farkas_le_n copies)"
        (List.length entries);
    let neg_entry = List.find_opt (fun (n, _) -> n = "neg_goal") entries in
    let real_entries = List.filter (fun (n, _) -> n <> "neg_goal") entries in
    let kind = goal_kind sigma goal_ty in
    match kind, neg_entry with
    | Some Goal_false, None ->
      close_term_false env sigma ir entries
    | Some (Goal_le (b, c)), Some (_, cng_z) ->
      (match real_entries with
       | [(real_name, c1z)] ->
         close_term_goal env sigma ir
           ~helper:(force r_farkas_le_goal_2)
           ~neg_norm:(neg_norm_le b c)
           b c real_name c1z cng_z
       | _ ->
         unsupported "term_mode: arity-2 ≤ goal expects one real-hypothesis \
                       entry alongside neg_goal (got %d real entries)"
           (List.length real_entries))
    | Some (Goal_lt (b, c)), Some (_, cng_z) ->
      (match real_entries with
       | [(real_name, c1z)] ->
         close_term_goal env sigma ir
           ~helper:(force r_farkas_lt_goal_2)
           ~neg_norm:(neg_norm_lt b c)
           b c real_name c1z cng_z
       | _ ->
         unsupported "term_mode: arity-2 < goal expects one real-hypothesis \
                       entry alongside neg_goal (got %d real entries)"
           (List.length real_entries))
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
                   _ <= _, _ < _, _ >= _, _ > _, or _ = _ over Z)"
    with Unsupported msg ->
      CErrors.user_err Pp.(str (Printf.sprintf "proof_broker_term: %s" msg)))

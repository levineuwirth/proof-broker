(** Tier-3 TSTP provenance + structure verifier (Phase 3 M2;
    roadmap §Phase 3 deliverable 2).

    What this verifies — and, deliberately, what it does not.

    The Alethe Tier-3 verifier ([Tier3_alethe]) re-derives every
    proof step: each rule has a checker that recomputes the step's
    clause from its premises. Vampire's TSTP derivation does not
    admit that cheaply — superposition / resolution steps are
    emitted without the unifier or term ordering, so re-deriving a
    step means re-running the inference, which is the proof-search
    problem itself. The roadmap anticipates exactly this: "Symbolic
    Tier 3 verifier for TPTP-FOF traces. May initially have lower
    coverage than Alethe; documented gaps fall through."

    So this verifier checks the property that IS soundly and
    cheaply checkable, and is the TSTP analogue of
    [Tier3_alethe.validate_top_level_assumes]: that the derivation
    is a {b well-formed refutation of our exact goal from our exact
    premises, introducing nothing else}. Concretely, [Verified_provenance]
    means all of:

    * Every leaf reachable from the [$false] sink is one of our
      input formulas — a [file(_, NAME)] whose NAME is one of the
      IR's hypothesis names or the goal — never a prover-[introduced]
      formula (skolem/AVATAR/theory-axiom definitions) and never a
      [file] leaf naming something we did not send. This is the
      anti-smuggling check: a proof cannot slip in [axiom $false]
      or an extra lemma.
    * The conjecture leaf is our goal and is consumed only through
      a [negated_conjecture] / [assume_negation] inference — Vampire
      refuted the negation of {e our} goal, not asserted the goal.
    * The parent DAG is well-formed (every cited parent resolves,
      no cycles) and terminates in a [$false] node.
    * Every inference rule used is in a reviewed allowlist
      ([recognized_rules]); an unrecognized rule name falls the
      proof through (conservative — we do not certify a derivation
      whose vocabulary we have not vetted for axiom-introducing
      behavior).

    [Verified_provenance] is therefore {b not} a claim that each
    inference was re-checked. It is a sound {e filter}: it never
    accepts a derivation that smuggled an axiom, skipped the goal,
    or failed to reach [$false]. In the broker's H1 model the
    home-system closer (M3) re-proves the goal with an axiom-free
    tactic gated on this verdict — that closer, not this module, is
    the kernel-level check. The cert's [trace_annotations] states
    this explicitly so a consumer is never misled about the
    guarantee. Anything short of [Verified_provenance] makes the
    Vampire adapter fall back to a Tier-0 oracle cert, exactly as
    the cvc5 adapter falls back when its Tier-3 gate fails. *)

type verify_result =
  | Verified_provenance
  | Unrecognized_rule of { rule : string; node : string }
  | Structural_failure of { node : string; detail : string }

(** Vampire inference-rule names vetted as consequence-producing
    (they derive from their parents; they do not inject a fresh
    axiom — anything that does is emitted with an [introduced(...)]
    source and is caught by the leaf-provenance check instead).
    An inference whose rule is not here makes the proof fall
    through rather than be certified: conservative by construction.
    Kept sorted; [test_tier3_tptp] pins membership of the rules the
    bundled fixtures exercise. *)
let recognized_rules : string list = [
  "assume_negation";
  "avatar_component_clause";
  "avatar_contradiction_clause";
  "avatar_sat_refutation";
  "avatar_split_clause";
  "backward_demodulation";
  "backward_subsumption_resolution";
  "cnf_transformation";
  "definition_folding";
  "definition_unfolding";
  "duplicate_literal_removal";
  "ennf_transformation";
  "equality_factoring";
  "equality_resolution";
  "factoring";
  "flattening";
  "foolean_elimination";
  "fool_elimination";
  "forward_demodulation";
  "forward_subsumption_resolution";
  "negated_conjecture";
  "nnf_transformation";
  "pure_predicate_removal";
  "rectify";
  "resolution";
  "skolemisation";
  "subsumption_resolution";
  "superposition";
  "trivial_inequality_removal";
  "unused_predicate_definition_removal";
]

let strip_quotes (s : string) : string =
  let s = String.trim s in
  let n = String.length s in
  if n >= 2 && s.[0] = '\'' && s.[n - 1] = '\'' then String.sub s 1 (n - 2)
  else s

(** Names we sent to Vampire: the IR hypothesis names plus the
    serializer's fixed conjecture name "goal" (see [Tptp.emit],
    which writes [LANG(goal, conjecture, …)] and
    [LANG(<hyp-name>, axiom, …)]). Single-quote-stripped so a
    quoted echo still matches. *)
let our_input_names (ir : Ir.t) : (string, unit) Hashtbl.t =
  let h = Hashtbl.create 16 in
  Hashtbl.replace h "goal" ();
  List.iter
    (fun (hyp : Ir.hypothesis) ->
       Hashtbl.replace h hyp.name ();
       Hashtbl.replace h (strip_quotes hyp.name) ())
    ir.context.hypotheses;
  h

let hyp_role_ok = function
  | "axiom" | "hypothesis" | "assumption" | "negated_conjecture" -> true
  | _ -> false

let negation_rule = function
  | "negated_conjecture" | "assume_negation" -> true
  | _ -> false

(** Backward-reachable node set from the sink, with a cycle guard
    and a [Structural_failure] on any dangling parent reference.
    Returns the reachable [node] list or the failure. *)
let reachable_from
    (p : Tptp_proof.proof) (sink : Tptp_proof.node)
  : (Tptp_proof.node list, verify_result) result =
  let seen = Hashtbl.create 64 in
  let acc = ref [] in
  let bad = ref None in
  let rec visit depth (n : Tptp_proof.node) =
    if !bad <> None then ()
    else if Hashtbl.mem seen n.name then ()
    else if depth > Tptp_proof.max_parse_depth then
      bad := Some (Structural_failure {
        node = n.name; detail = "derivation depth bound exceeded" })
    else begin
      Hashtbl.replace seen n.name ();
      acc := n :: !acc;
      List.iter
        (fun pname ->
           match Hashtbl.find_opt p.by_name pname with
           | Some parent -> visit (depth + 1) parent
           | None ->
             bad := Some (Structural_failure {
               node = n.name;
               detail = Printf.sprintf
                 "cites parent %s which is not in the derivation" pname }))
        (Tptp_proof.parents n)
    end
  in
  visit 0 sink;
  match !bad with Some f -> Error f | None -> Ok !acc

let verify_parsed (ir : Ir.t) (p : Tptp_proof.proof) : verify_result =
  (* 1. The refutation sink. *)
  match List.find_opt Tptp_proof.is_false_sink p.nodes with
  | None ->
    Structural_failure { node = ""; detail = "no $false node in derivation" }
  | Some sink ->
    (match reachable_from p sink with
     | Error f -> f
     | Ok reach ->
       let expected = our_input_names ir in
       (* 2. Leaf provenance + 3. inference-rule allowlist, in one
          pass over the reachable sub-DAG. *)
       let fail = ref None in
       List.iter
         (fun (n : Tptp_proof.node) ->
            if !fail <> None then ()
            else if Tptp_proof.is_introduced n then
              fail := Some (Structural_failure {
                node = n.name;
                detail = "prover-introduced formula in the refutation \
                          (skolem/AVATAR/theory-axiom definition); not \
                          one of our premises" })
            else if Tptp_proof.is_leaf n then begin
              match Tptp_proof.file_name n with
              | None ->
                fail := Some (Structural_failure {
                  node = n.name;
                  detail = "leaf with unrecognized provenance (no \
                            file(_, NAME) source)" })
              | Some raw ->
                let nm = strip_quotes raw in
                if not (Hashtbl.mem expected nm) then
                  fail := Some (Structural_failure {
                    node = n.name;
                    detail = Printf.sprintf
                      "leaf cites input %S which is not one of our \
                       hypotheses or the goal (smuggled axiom)" raw })
                else begin
                  if nm = "goal" then begin
                    if n.role <> "conjecture" then
                      fail := Some (Structural_failure {
                        node = n.name;
                        detail = Printf.sprintf
                          "goal leaf has role %S, expected conjecture"
                          n.role })
                  end
                  else if not (hyp_role_ok n.role) then
                    fail := Some (Structural_failure {
                      node = n.name;
                      detail = Printf.sprintf
                        "hypothesis leaf %S has unexpected role %S"
                        raw n.role })
                end
            end
            else
              (* An inference node: its rule must be recognized. *)
              match Tptp_proof.inference_rule n with
              | Some r when List.mem r recognized_rules -> ()
              | Some r ->
                fail := Some (Unrecognized_rule { rule = r; node = n.name })
              | None ->
                fail := Some (Structural_failure {
                  node = n.name;
                  detail = "non-leaf node with no inference rule" }))
         reach;
       (match !fail with
        | Some f -> f
        | None ->
          (* 4. The conjecture, if present, must be consumed only
             through a negation inference — Vampire refuted the
             negation of {e our} goal, not asserted the goal. The
             conjecture is the reachable node whose input name is
             "goal" or whose role is "conjecture"; its DAG children
             are nodes citing {e its node name} as a parent. (A
             refutation of the hypotheses alone, with no conjecture,
             is also sound; we only constrain it when present.) *)
          let conj_node =
            List.find_opt
              (fun (n : Tptp_proof.node) ->
                 n.role = "conjecture"
                 || (match Tptp_proof.file_name n with
                     | Some raw -> strip_quotes raw = "goal"
                     | None -> false))
              reach
          in
          (match conj_node with
           | None -> Verified_provenance
           | Some cn ->
             let conj_child_ok =
               List.for_all
                 (fun (n : Tptp_proof.node) ->
                    if List.mem cn.name (Tptp_proof.parents n) then
                      (match Tptp_proof.inference_rule n with
                       | Some r -> negation_rule r
                       | None -> false)
                    else true)
                 reach
             in
             if not conj_child_ok then
               Structural_failure {
                 node = cn.name;
                 detail = "conjecture is consumed by a non-negation \
                           inference (goal not refuted via its \
                           negation)" }
             else Verified_provenance)))

(** Top-level [verify]: parse then [verify_parsed]. A parse failure
    surfaces as a [Structural_failure] so callers need no extra arm
    (mirrors [Tier3_alethe.verify]). *)
let verify (ir : Ir.t) (proof_str : string) : verify_result =
  match Tptp_proof.parse proof_str with
  | exception Tptp_proof.Parse_error msg ->
    Structural_failure { node = ""; detail = "parse: " ^ msg }
  | p -> verify_parsed ir p

let result_to_string = function
  | Verified_provenance -> "verified_provenance"
  | Unrecognized_rule { rule; node } ->
    Printf.sprintf "unrecognized_rule(%s @ %s)" rule node
  | Structural_failure { node; detail } ->
    Printf.sprintf "structural_failure(%s: %s)"
      (if node = "" then "-" else node) detail

(** Unit tests for [Tptp_proof] (TSTP parser).

    Driven by a verbatim Vampire 5.0.1 FOF derivation for
    [p(a), ! x. p(x) => q(x) ⊢ q(a)] so the parser is pinned
    against real solver output shape (multi-line formulas,
    [file(_, NAME)] / [inference(...)] sources, the [$false]
    sink), not a hand-idealized form. *)

open Proof_broker

let proof_block =
  "% SZS output start Proof for q\n\
   fof(f1,axiom,(\n  p(a)),\n  file('/tmp/q.p',h1)).\n\
   fof(f2,axiom,(\n  ! [X0] : (p(X0) => q(X0))),\n  file('/tmp/q.p',h2)).\n\
   fof(f3,conjecture,(\n  q(a)),\n  file('/tmp/q.p',goal)).\n\
   fof(f4,negated_conjecture,(\n  ~q(a)),\n\
   \  inference(negated_conjecture,[status(cth)],[f3])).\n\
   fof(f5,plain,(\n  ~q(a)),\n  inference(flattening,[],[f4])).\n\
   fof(f6,plain,(\n  ! [X0] : (q(X0) | ~p(X0))),\n\
   \  inference(ennf_transformation,[],[f2])).\n\
   fof(f7,plain,(\n  p(a)),\n  inference(cnf_transformation,[],[f1])).\n\
   fof(f8,plain,(\n  ( ! [X0] : (~p(X0) | q(X0)) )),\n\
   \  inference(cnf_transformation,[],[f6])).\n\
   fof(f9,plain,(\n  ~q(a)),\n  inference(cnf_transformation,[],[f5])).\n\
   fof(f10,plain,(\n  q(a)),\n  inference(resolution,[],[f8,f7])).\n\
   fof(f11,plain,(\n  $false),\n\
   \  inference(forward_subsumption_resolution,[],[f10,f9])).\n\
   % SZS output end Proof for q\n"

let p () = Tptp_proof.parse proof_block

let node name =
  let pr = p () in
  match Hashtbl.find_opt pr.by_name name with
  | Some n -> n
  | None -> Alcotest.fail ("no node " ^ name)

let test_node_count () =
  Alcotest.(check int) "11 annotated formulas" 11
    (List.length (p ()).nodes)

let test_leaf_provenance () =
  let f1 = node "f1" in
  Alcotest.(check bool) "f1 is a leaf" true (Tptp_proof.is_leaf f1);
  Alcotest.(check (option string)) "f1 file name = h1"
    (Some "h1") (Tptp_proof.file_name f1);
  Alcotest.(check string) "f1 role" "axiom" f1.role;
  Alcotest.(check bool) "f1 not introduced" false
    (Tptp_proof.is_introduced f1)

let test_inference_rule_and_parents () =
  let f4 = node "f4" in
  Alcotest.(check (option string)) "f4 rule"
    (Some "negated_conjecture") (Tptp_proof.inference_rule f4);
  Alcotest.(check (list string)) "f4 parents" [ "f3" ]
    (Tptp_proof.parents f4);
  let f10 = node "f10" in
  Alcotest.(check (option string)) "f10 rule"
    (Some "resolution") (Tptp_proof.inference_rule f10);
  Alcotest.(check (list string)) "f10 parents" [ "f8"; "f7" ]
    (Tptp_proof.parents f10)

let test_false_sink () =
  Alcotest.(check bool) "f11 is $false sink" true
    (Tptp_proof.is_false_sink (node "f11"));
  Alcotest.(check bool) "f1 is not a sink" false
    (Tptp_proof.is_false_sink (node "f1"))

let test_rule_inventory () =
  Alcotest.(check (list string)) "sorted distinct rules"
    [ "cnf_transformation"; "ennf_transformation"; "flattening";
      "forward_subsumption_resolution"; "negated_conjecture";
      "resolution" ]
    (Tptp_proof.rule_inventory (p ()))

let test_no_markers_fallback () =
  (* Without SZS markers the parser falls back to scanning all
     non-comment lines. *)
  let bare = "fof(a1, axiom, ( r(x) ), file('f', h1)).\n\
              cnf(a2, plain, ($false), inference(resolution,[],[a1])).\n" in
  let pr = Tptp_proof.parse bare in
  Alcotest.(check int) "2 nodes without markers" 2
    (List.length pr.nodes)

let () =
  Alcotest.run "tptp_proof"
    [
      ( "parse",
        [ Alcotest.test_case "node count" `Quick test_node_count;
          Alcotest.test_case "leaf provenance" `Quick test_leaf_provenance;
          Alcotest.test_case "rule+parents" `Quick
            test_inference_rule_and_parents;
          Alcotest.test_case "$false sink" `Quick test_false_sink;
          Alcotest.test_case "rule inventory" `Quick test_rule_inventory;
          Alcotest.test_case "no-marker fallback" `Quick
            test_no_markers_fallback ] );
    ]

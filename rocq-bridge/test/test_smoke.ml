(** Plugin-glue-free smoke test for the IR shape the Rocq reifier
    produces. Hand-builds the [Ir.t] for example1 [forall x : Z,
    x >= 5 -> x <= 3 -> False] in the same App-symbol vocabulary
    [Reifier.build_ir] emits, then exercises the full dispatch +
    verify pipeline. Lets us catch IR-shape regressions without
    spawning [rocq compile]: when this passes but [Test.v] fails,
    the bug is on the Rocq plugin glue side; when this fails too,
    the shape itself is wrong. *)

open Proof_broker

let lia_logic : Ir.logic_classification = {
  order = "first_order";
  features_used = [];
  first_order_fragment = "LIA";
  decidable_theory = None;
}

(* Build the IR exactly as [Reifier.build_ir] would for the goal
   [forall x : Z, x >= 5 -> x <= 3 -> False] — typeclass-flavored
   shell vocabulary, [Z.ge a b] flipped to [LE.le b a]. *)
let example1_rocq_ir () : Ir.t =
  let x : Ir.shell_term = Var { name = "x" } in
  let three : Ir.shell_term = Num_lit { value = "3"; ty = "Int" } in
  let five : Ir.shell_term = Num_lit { value = "5"; ty = "Int" } in
  let h1 : Ir.hypothesis = {
    name = "H1";
    shell = App { symbol = "LE.le"; type_args = []; args = [ five; x ] };
  } in
  let h2 : Ir.hypothesis = {
    name = "H2";
    shell = App { symbol = "LE.le"; type_args = []; args = [ x; three ] };
  } in
  {
    ir_version = "1.0";
    source_system = { name = "rocq"; version = "0.1" };
    tier = "goal";
    logic_classification = lia_logic;
    goal = { shell = Const { name = "False" }; payloads = None };
    context = {
      type_vars = [];
      free_vars = [ { name = "x"; ty = "Int" } ];
      hypotheses = [ h1; h2 ];
      library_slice = None;
    };
    type_metadata = [];
    definitional_metadata = [];
    library_provenance = [];
    user_directives = None;
  }

let any_solver_on_path () : bool =
  List.exists (fun b -> Sys.command (Printf.sprintf "which %s > /dev/null 2>&1" b) = 0)
    [ "cvc4"; "cvc5"; "z3" ]

let load_manifests () : Manifest.t list =
  (* Test exe runs from [_build/default/rocq-bridge/test/], four
     levels under the repo root. The other candidates handle anyone
     running this test exe directly from a different cwd. *)
  let candidates = [
    "../../../../examples";
    "../../../examples";
    "../../examples";
    "../examples";
    "examples";
  ] in
  let dir = List.find_opt (fun d ->
    Sys.file_exists (Filename.concat d "manifest-cvc5.json")) candidates
  in
  match dir with
  | None -> Alcotest.fail "manifest dir not found from any candidate"
  | Some d ->
    List.filter_map (fun n ->
      let p = Filename.concat d (Printf.sprintf "manifest-%s.json" n) in
      if Sys.file_exists p then
        Some (Manifest.of_json (Yojson.Safe.from_file p))
      else None)
      [ "cvc4"; "cvc5"; "z3" ]

let adapter_registry () : (string, Adapter.t) Hashtbl.t =
  let r = Hashtbl.create 4 in
  Hashtbl.replace r "cvc4" Adapter_cvc4.adapter;
  Hashtbl.replace r "cvc5" Adapter_cvc5.adapter;
  Hashtbl.replace r "z3"   Adapter_z3.adapter;
  r

let test_rocq_shape_dispatches_and_verifies () =
  if not (any_solver_on_path ()) then
    Printf.printf "[skip] no cvc4/cvc5/z3 on PATH\n"
  else begin
    let ir = example1_rocq_ir () in
    let manifests =
      Manifest.sort_by_max_tier_descending (load_manifests ())
    in
    let result = Dispatch.run ~manifests ~adapters:(adapter_registry ()) ir in
    match result.cert with
    | None -> Alcotest.fail "no cert minted on example1-Rocq IR"
    | Some cert ->
      Alcotest.(check bool) "tier in {1,2,3}" true
        (cert.tier = 1 || cert.tier = 2 || cert.tier = 3);
      let reason = Verifier.verify ~trace:None cert ir in
      let kind = Verifier.kind_of_reason reason in
      let ok =
        kind = "verified_envelope" || kind = "verified_farkas"
        || kind = "verified_case_split" || kind = "verified_tier3"
      in
      Alcotest.(check bool)
        (Printf.sprintf "verify reason is Verified_* (got %s)" kind)
        true ok
  end

let () =
  Alcotest.run "rocq-bridge-smoke" [
    "ir_shape", [
      Alcotest.test_case "Rocq-emitted example1 IR dispatches + verifies"
        `Quick test_rocq_shape_dispatches_and_verifies;
    ];
  ]

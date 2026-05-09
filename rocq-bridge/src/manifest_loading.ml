(* Walk upward from [start] looking for a directory containing
   [examples/manifest-cvc4.json]. Stops at the filesystem root. *)
let find_examples_dir_upward (start : string) : string option =
  let rec loop d =
    let candidate = Filename.concat d "examples" in
    if Sys.file_exists (Filename.concat candidate "manifest-cvc4.json") then
      Some candidate
    else
      let parent = Filename.dirname d in
      if parent = d then None
      else loop parent
  in
  loop start

let resolve_examples_dir () : string =
  match Sys.getenv_opt "PROOF_BROKER_EXAMPLES_DIR" with
  | Some s -> s
  | None ->
    (* Self-locate. The Lean tactic runs with cwd = lean-bridge/, one
       level under the repo root, so its [<cwd>/../examples] heuristic
       works. Under dune-driven [rocq compile] the cwd is the build
       dir [_build/default/], a varying number of levels deep, so a
       fixed [..] count doesn't transfer. Walking upward is the
       portable fix. *)
    (match find_examples_dir_upward (Sys.getcwd ()) with
     | Some s -> s
     | None ->
       (* Last resort: hand the original Lean-style path back so the
          error message names something a human can chase. *)
       Filename.concat (Sys.getcwd ()) "../examples")

let load_one (dir : string) (name : string)
  : Proof_broker.Manifest.t option =
  let path = Filename.concat dir (Printf.sprintf "manifest-%s.json" name) in
  if not (Sys.file_exists path) then None
  else
    let json = Yojson.Safe.from_file path in
    Some (Proof_broker.Manifest.of_json json)

let load_default () : Proof_broker.Manifest.t list =
  let dir = resolve_examples_dir () in
  let manifests =
    List.filter_map (load_one dir) [ "cvc4"; "cvc5"; "z3" ]
  in
  if manifests = [] then
    CErrors.user_err Pp.(
      str "proof_broker: no manifests found in " ++ str dir ++
      str "; set PROOF_BROKER_EXAMPLES_DIR or run from a directory " ++
      str "whose parent has examples/manifest-*.json");
  manifests

let load_named (names : string list) : Proof_broker.Manifest.t list =
  let dir = resolve_examples_dir () in
  List.map (fun name ->
    match load_one dir name with
    | Some m -> m
    | None ->
      CErrors.user_err Pp.(
        str (Printf.sprintf
               "proof_broker: manifest-%s.json not found in %s" name dir)))
    names

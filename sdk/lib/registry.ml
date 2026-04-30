(** Adapter manifest registry: load manifests from disk and hold
    them in a name-keyed map for lookup.

    Used by tests today; intended to be the deployment artifact a
    Phase-2 dispatcher consults at startup. The registry is local
    to whichever code creates it — there is no global mutable
    instance. Tests build their own; deployments would build one
    once at OCaml init.

    Conventions:
    * [load_dir dir] reads every file in [dir] matching the pattern
      [manifest-*.json] and parses it as a manifest. Files that
      fail to parse are reported with their path; the caller
      decides whether to fail-fast or continue.
    * Adapter-name collisions (two manifests declaring the same
      [adapter]) are reported as errors; the registry holds at
      most one manifest per adapter name. *)

module SM = Map.Make (String)

type t = Manifest.t SM.t

(** Directory scan filter: matches the spec's recommended file
    naming for manifests on disk. *)
let manifest_filename_pattern (name : string) : bool =
  let prefix = "manifest-" in
  let suffix = ".json" in
  String.length name >= String.length prefix + String.length suffix
  && String.sub name 0 (String.length prefix) = prefix
  && String.sub name (String.length name - String.length suffix)
                    (String.length suffix) = suffix

(** [load_file path] reads and parses a single manifest file. Wraps
    parse errors with the path so callers can locate the offender. *)
let load_file (path : string) : (Manifest.t, string) result =
  try
    let raw = In_channel.with_open_text path In_channel.input_all in
    let j = Yojson.Safe.from_string raw in
    Ok (Manifest.of_json j)
  with
  | Yojson.Json_error msg ->
    Error (Printf.sprintf "%s: JSON parse error: %s" path msg)
  | Codec.Decode_error (msg, _) ->
    Error (Printf.sprintf "%s: manifest decode error: %s" path msg)
  | Sys_error msg ->
    Error (Printf.sprintf "%s: %s" path msg)

(** Build a registry from an explicit manifest list. Adapter-name
    collisions are an error. *)
let of_list (manifests : Manifest.t list) : (t, string) result =
  let rec loop acc = function
    | [] -> Ok acc
    | (m : Manifest.t) :: rest ->
      if SM.mem m.adapter acc then
        Error (Printf.sprintf
                 "duplicate adapter name in registry: %s" m.adapter)
      else
        loop (SM.add m.adapter m acc) rest
  in
  loop SM.empty manifests

(** Scan [dir] for [manifest-*.json] files; load them all; build a
    registry. Returns the registry and a list of per-file errors
    (paths that failed to parse), so callers can choose to log and
    continue or to fail-fast. *)
let load_dir (dir : string) : t * string list =
  let entries =
    try Sys.readdir dir
    with Sys_error msg ->
      Printf.eprintf "registry: %s\n" msg;
      [||]
  in
  let matched =
    Array.to_list entries
    |> List.filter manifest_filename_pattern
    |> List.sort compare
    |> List.map (Filename.concat dir)
  in
  let manifests, errors =
    List.fold_left
      (fun (ms, es) path ->
        match load_file path with
        | Ok m -> m :: ms, es
        | Error e -> ms, e :: es)
      ([], []) matched
  in
  match of_list (List.rev manifests) with
  | Ok t -> t, List.rev errors
  | Error e -> SM.empty, e :: List.rev errors

let find = SM.find_opt

let to_list (r : t) : Manifest.t list =
  SM.fold (fun _ m acc -> m :: acc) r []

let cardinal = SM.cardinal

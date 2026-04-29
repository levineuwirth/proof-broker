(** JSON codec for IR documents (spec v1.0 §4 / [schemas/v1.0/ir.schema.json]).

    Conventions:
    - Field names match the schema verbatim ("type", "node", etc.); OCaml
      reserved words ([type]) become [ty] in IR records.
    - Optional fields encode as omission, never as [null], unless the
      schema explicitly says nullable (currently only
      [logic_classification.decidable_theory]).
    - Required-but-empty objects/arrays encode as [{}] / [[]]
      verbatim, not omitted.
    - Pass-through metadata maps ([type_metadata], [definitional_metadata])
      preserve their JSON exactly; full ADTs are deferred. *)

open Yojson.Safe

exception Decode_error of string * t
(** [Decode_error (msg, j)] is raised when [of_json] meets JSON it cannot
    parse. [msg] names the offending field or constructor; [j] is the
    JSON value at the failure site. *)

let fail msg j = raise (Decode_error (msg, j))

let assoc j = match j with
  | `Assoc pairs -> pairs
  | _ -> fail "expected object" j

let get k pairs = try List.assoc k pairs with Not_found ->
  fail ("missing field: " ^ k) (`Assoc pairs)

let get_opt k pairs = List.assoc_opt k pairs

let str = function `String s -> s | j -> fail "expected string" j

let int_of = function `Int n -> n | j -> fail "expected int" j

let bool_of = function `Bool b -> b | j -> fail "expected bool" j

let list_of f = function
  | `List xs -> List.map f xs
  | j -> fail "expected array" j

let str_list = list_of str

let opt f = function `Null -> None | j -> Some (f j)

(* --- shell terms ---------------------------------------------------------- *)

let rec shell_to_json (t : Ir.shell_term) : Yojson.Safe.t =
  match t with
  | Forall { var; ty; body } ->
    `Assoc [
      "node", `String "Forall";
      "var", `String var;
      "type", `String ty;
      "body", shell_to_json body;
    ]
  | Exists { var; ty; body } ->
    `Assoc [
      "node", `String "Exists";
      "var", `String var;
      "type", `String ty;
      "body", shell_to_json body;
    ]
  | Lambda { binders; body } ->
    `Assoc [
      "node", `String "Lambda";
      "binders", `List (List.map binder_to_json binders);
      "body", shell_to_json body;
    ]
  | Implies { antecedent; consequent } ->
    `Assoc [
      "node", `String "Implies";
      "antecedent", shell_to_json antecedent;
      "consequent", shell_to_json consequent;
    ]
  | And { left; right } ->
    `Assoc [
      "node", `String "And";
      "left", shell_to_json left;
      "right", shell_to_json right;
    ]
  | Or { left; right } ->
    `Assoc [
      "node", `String "Or";
      "left", shell_to_json left;
      "right", shell_to_json right;
    ]
  | Not { operand } ->
    `Assoc [
      "node", `String "Not";
      "operand", shell_to_json operand;
    ]
  | Eq { ty; left; right } ->
    `Assoc [
      "node", `String "Eq";
      "type", `String ty;
      "left", shell_to_json left;
      "right", shell_to_json right;
    ]
  | App { symbol; type_args; args } ->
    `Assoc [
      "node", `String "App";
      "symbol", `String symbol;
      "type_args", `List (List.map (fun s -> `String s) type_args);
      "args", `List (List.map shell_to_json args);
    ]
  | Var { name } ->
    `Assoc [ "node", `String "Var"; "name", `String name ]
  | Const { name } ->
    `Assoc [ "node", `String "Const"; "name", `String name ]
  | Num_lit { value; ty } ->
    `Assoc [
      "node", `String "NumLit";
      "value", `String value;
      "type", `String ty;
    ]
  | Opaque { payload_id } ->
    `Assoc [
      "node", `String "Opaque";
      "payload_id", `String payload_id;
    ]

and binder_to_json (b : Ir.binder) : Yojson.Safe.t =
  `Assoc [ "var", `String b.var; "type", `String b.ty ]

let rec shell_of_json (j : Yojson.Safe.t) : Ir.shell_term =
  let pairs = assoc j in
  let node = str (get "node" pairs) in
  match node with
  | "Forall" ->
    Forall { var = str (get "var" pairs);
             ty = str (get "type" pairs);
             body = shell_of_json (get "body" pairs) }
  | "Exists" ->
    Exists { var = str (get "var" pairs);
             ty = str (get "type" pairs);
             body = shell_of_json (get "body" pairs) }
  | "Lambda" ->
    Lambda { binders = list_of binder_of_json (get "binders" pairs);
             body = shell_of_json (get "body" pairs) }
  | "Implies" ->
    Implies { antecedent = shell_of_json (get "antecedent" pairs);
              consequent = shell_of_json (get "consequent" pairs) }
  | "And" ->
    And { left = shell_of_json (get "left" pairs);
          right = shell_of_json (get "right" pairs) }
  | "Or" ->
    Or { left = shell_of_json (get "left" pairs);
         right = shell_of_json (get "right" pairs) }
  | "Not" ->
    Not { operand = shell_of_json (get "operand" pairs) }
  | "Eq" ->
    Eq { ty = str (get "type" pairs);
         left = shell_of_json (get "left" pairs);
         right = shell_of_json (get "right" pairs) }
  | "App" ->
    App { symbol = str (get "symbol" pairs);
          type_args = (match get_opt "type_args" pairs with
                       | None -> []
                       | Some j -> str_list j);
          args = (match get_opt "args" pairs with
                  | None -> []
                  | Some j -> list_of shell_of_json j) }
  | "Var" ->
    Var { name = str (get "name" pairs) }
  | "Const" ->
    Const { name = str (get "name" pairs) }
  | "NumLit" ->
    Num_lit { value = str (get "value" pairs);
              ty = str (get "type" pairs) }
  | "Opaque" ->
    Opaque { payload_id = str (get "payload_id" pairs) }
  | other -> fail ("unknown shell node: " ^ other) j

and binder_of_json (j : Yojson.Safe.t) : Ir.binder =
  let pairs = assoc j in
  { var = str (get "var" pairs); ty = str (get "type" pairs) }

(* --- top-level structures ------------------------------------------------- *)

let logic_classification_to_json (lc : Ir.logic_classification) : Yojson.Safe.t =
  `Assoc [
    "order", `String lc.order;
    "features_used", `List (List.map (fun s -> `String s) lc.features_used);
    "first_order_fragment", `String lc.first_order_fragment;
    "decidable_theory", (match lc.decidable_theory with
                         | None -> `Null
                         | Some s -> `String s);
  ]

let logic_classification_of_json (j : Yojson.Safe.t) : Ir.logic_classification =
  let p = assoc j in
  {
    order = str (get "order" p);
    features_used = str_list (get "features_used" p);
    first_order_fragment = str (get "first_order_fragment" p);
    decidable_theory = opt str (get "decidable_theory" p);
  }

let goal_to_json (g : Ir.goal) : Yojson.Safe.t =
  let base = [ "shell", shell_to_json g.shell ] in
  match g.payloads with
  | None -> `Assoc base
  | Some ps -> `Assoc (base @ [ "payloads", `Assoc ps ])

let goal_of_json (j : Yojson.Safe.t) : Ir.goal =
  let p = assoc j in
  {
    shell = shell_of_json (get "shell" p);
    payloads = Option.map assoc (get_opt "payloads" p);
  }

let free_var_to_json (fv : Ir.free_var) : Yojson.Safe.t =
  `Assoc [ "name", `String fv.name; "type", `String fv.ty ]

let free_var_of_json (j : Yojson.Safe.t) : Ir.free_var =
  let p = assoc j in
  { name = str (get "name" p); ty = str (get "type" p) }

let hypothesis_to_json (h : Ir.hypothesis) : Yojson.Safe.t =
  `Assoc [ "name", `String h.name; "shell", shell_to_json h.shell ]

let hypothesis_of_json (j : Yojson.Safe.t) : Ir.hypothesis =
  let p = assoc j in
  { name = str (get "name" p); shell = shell_of_json (get "shell" p) }

let library_slice_entry_to_json (e : Ir.library_slice_entry) : Yojson.Safe.t =
  let fields = [
    "entity_name", `String e.entity_name;
    "shell", shell_to_json e.shell;
  ] in
  match e.selection_reason with
  | None -> `Assoc fields
  | Some r -> `Assoc (fields @ [ "selection_reason", `String r ])

let library_slice_entry_of_json (j : Yojson.Safe.t) : Ir.library_slice_entry =
  let p = assoc j in
  {
    entity_name = str (get "entity_name" p);
    shell = shell_of_json (get "shell" p);
    selection_reason = Option.map str (get_opt "selection_reason" p);
  }

let context_to_json (c : Ir.context) : Yojson.Safe.t =
  let fields = [
    "type_vars", `List (List.map (fun s -> `String s) c.type_vars);
    "free_vars", `List (List.map free_var_to_json c.free_vars);
    "hypotheses", `List (List.map hypothesis_to_json c.hypotheses);
  ] in
  match c.library_slice with
  | None -> `Assoc fields
  | Some xs ->
    `Assoc (fields @ [ "library_slice", `List (List.map library_slice_entry_to_json xs) ])

let context_of_json (j : Yojson.Safe.t) : Ir.context =
  let p = assoc j in
  {
    type_vars = (match get_opt "type_vars" p with None -> [] | Some j -> str_list j);
    free_vars = (match get_opt "free_vars" p with
                 | None -> []
                 | Some j -> list_of free_var_of_json j);
    hypotheses = (match get_opt "hypotheses" p with
                  | None -> []
                  | Some j -> list_of hypothesis_of_json j);
    library_slice = Option.map (list_of library_slice_entry_of_json)
                      (get_opt "library_slice" p);
  }

let provenance_to_json (p : Ir.provenance) : Yojson.Safe.t =
  let fields = [
    "library", `String p.library;
    "version", `String p.version;
  ] in
  let fields = match p.module_path with
    | None -> fields
    | Some s -> fields @ [ "module_path", `String s ]
  in
  `Assoc (fields @ [ "content_hash", `String p.content_hash ])

let provenance_of_json (j : Yojson.Safe.t) : Ir.provenance =
  let p = assoc j in
  {
    library = str (get "library" p);
    version = str (get "version" p);
    module_path = Option.map str (get_opt "module_path" p);
    content_hash = str (get "content_hash" p);
  }

let budget_to_json (b : Ir.budget) : Yojson.Safe.t =
  let fields = [] in
  let fields = match b.wall_time_ms with
    | None -> fields | Some n -> fields @ [ "wall_time_ms", `Int n ]
  in
  let fields = match b.memory_mb with
    | None -> fields | Some n -> fields @ [ "memory_mb", `Int n ]
  in
  `Assoc fields

let budget_of_json (j : Yojson.Safe.t) : Ir.budget =
  let p = assoc j in
  {
    wall_time_ms = Option.map int_of (get_opt "wall_time_ms" p);
    memory_mb = Option.map int_of (get_opt "memory_mb" p);
  }

let rewriter_preferences_to_json (rp : Ir.rewriter_preferences) : Yojson.Safe.t =
  let fields = [] in
  let fields = match rp.enable_quotient_elimination with
    | None -> fields
    | Some b -> fields @ [ "enable_quotient_elimination", `Bool b ]
  in
  let fields = match rp.enable_definition_unfolding with
    | None -> fields
    | Some xs -> fields @ [ "enable_definition_unfolding",
                            `List (List.map (fun s -> `String s) xs) ]
  in
  let fields = match rp.disable_passes with
    | None -> fields
    | Some xs -> fields @ [ "disable_passes",
                            `List (List.map (fun s -> `String s) xs) ]
  in
  `Assoc fields

let rewriter_preferences_of_json (j : Yojson.Safe.t) : Ir.rewriter_preferences =
  let p = assoc j in
  {
    enable_quotient_elimination = Option.map bool_of (get_opt "enable_quotient_elimination" p);
    enable_definition_unfolding = Option.map str_list (get_opt "enable_definition_unfolding" p);
    disable_passes = Option.map str_list (get_opt "disable_passes" p);
  }

let user_directives_to_json (ud : Ir.user_directives) : Yojson.Safe.t =
  let fields = [] in
  let fields = match ud.preferred_backend with
    | None -> fields
    | Some `Null -> fields @ [ "preferred_backend", `Null ]
    | Some (`String s) -> fields @ [ "preferred_backend", `String s ]
  in
  let fields = match ud.tier_preference with
    | None -> fields
    | Some xs -> fields @ [ "tier_preference",
                            `List (List.map (fun s -> `String s) xs) ]
  in
  let fields = match ud.rewriter_preferences with
    | None -> fields
    | Some rp -> fields @ [ "rewriter_preferences", rewriter_preferences_to_json rp ]
  in
  let fields = match ud.budget with
    | None -> fields
    | Some b -> fields @ [ "budget", budget_to_json b ]
  in
  `Assoc fields

let user_directives_of_json (j : Yojson.Safe.t) : Ir.user_directives =
  let p = assoc j in
  let preferred_backend =
    match get_opt "preferred_backend" p with
    | None -> None
    | Some `Null -> Some `Null
    | Some (`String s) -> Some (`String s)
    | Some j -> fail "preferred_backend" j
  in
  {
    preferred_backend;
    tier_preference = Option.map str_list (get_opt "tier_preference" p);
    rewriter_preferences = Option.map rewriter_preferences_of_json
                             (get_opt "rewriter_preferences" p);
    budget = Option.map budget_of_json (get_opt "budget" p);
  }

let source_system_to_json (s : Ir.source_system) : Yojson.Safe.t =
  `Assoc [ "name", `String s.name; "version", `String s.version ]

let source_system_of_json (j : Yojson.Safe.t) : Ir.source_system =
  let p = assoc j in
  { name = str (get "name" p); version = str (get "version" p) }

let to_json (ir : Ir.t) : Yojson.Safe.t =
  let provenance_pairs =
    List.map (fun (k, v) -> (k, provenance_to_json v)) ir.library_provenance
  in
  let fields = [
    "ir_version", `String ir.ir_version;
    "source_system", source_system_to_json ir.source_system;
    "tier", `String ir.tier;
    "logic_classification", logic_classification_to_json ir.logic_classification;
    "goal", goal_to_json ir.goal;
    "context", context_to_json ir.context;
    "type_metadata", `Assoc ir.type_metadata;
    "definitional_metadata", `Assoc ir.definitional_metadata;
    "library_provenance", `Assoc provenance_pairs;
  ] in
  match ir.user_directives with
  | None -> `Assoc fields
  | Some ud -> `Assoc (fields @ [ "user_directives", user_directives_to_json ud ])

let of_json (j : Yojson.Safe.t) : Ir.t =
  let p = assoc j in
  let provenance_pairs = match get_opt "library_provenance" p with
    | None -> []
    | Some j -> List.map (fun (k, v) -> (k, provenance_of_json v)) (assoc j)
  in
  {
    ir_version = str (get "ir_version" p);
    source_system = source_system_of_json (get "source_system" p);
    tier = str (get "tier" p);
    logic_classification = logic_classification_of_json (get "logic_classification" p);
    goal = goal_of_json (get "goal" p);
    context = context_of_json (get "context" p);
    type_metadata = (match get_opt "type_metadata" p with
                     | None -> []
                     | Some j -> assoc j);
    definitional_metadata = (match get_opt "definitional_metadata" p with
                             | None -> []
                             | Some j -> assoc j);
    library_provenance = provenance_pairs;
    user_directives = Option.map user_directives_of_json (get_opt "user_directives" p);
  }

(* --- JSON normalization for round-trip equality --------------------------- *)

let rec normalize (j : Yojson.Safe.t) : Yojson.Safe.t = match j with
  | `Assoc pairs ->
    let normalized = List.map (fun (k, v) -> (k, normalize v)) pairs in
    let sorted = List.sort (fun (a, _) (b, _) -> String.compare a b) normalized in
    `Assoc sorted
  | `List xs -> `List (List.map normalize xs)
  | other -> other

let json_equal a b = normalize a = normalize b

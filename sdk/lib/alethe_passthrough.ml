(** Tier 3 Alethe-passthrough payload constructor.

    Tier 3 ships the entire solver proof so a Lean re-checker can
    re-derive the unsat verdict step-by-step instead of trusting any
    single rule extraction (Tier 1) or structural pattern (Tier 2).
    This module is the OCaml-side minter for the [alethe-2024]
    flavor of Tier 3: it captures the raw Alethe S-expression text,
    inventories which rules and structural features the proof
    actually uses, and assembles a verifier-ready
    [Certificate.Tier3_proof_trace] payload.

    Why this exists, separate from the cvc5 adapter. Direction (1)
    of the Tier 3 plan is "define the cert format precisely"; the
    Lean re-checker (direction 2) and the cvc5 dispatch wiring
    (direction 3) come later. Splitting the format/minter into its
    own module pins the contract — what [trace_data] looks like,
    what tags appear in [trace_dialect_features], how [trace_annotations]
    is shaped — without entangling that contract with cvc5-specific
    plumbing. The same minter will serve any solver whose proof we
    can parse into [Alethe.proof] (e.g., a future cvc4/Alethe path).

    Format conventions (alethe-2024).

    * [trace_format = "alethe-2024"]. Identifies the dialect; the
      Lean re-checker dispatches its parser/checkers on this string.
    * [trace_data]: a JSON string carrying the verbatim Alethe
      S-expression text (everything from the [(] following [unsat]
      onward). Kept opaque so newer Alethe revisions can ride the
      same envelope without schema changes; the verifier re-parses
      with its own tokenizer.
    * [trace_dialect_features]: a sorted, deduped list of feature
      tags. Two prefixes:
      * [rule:<name>] for every distinct [:rule] used in the proof
        (e.g., [rule:la_generic], [rule:resolution]).
      * Bare structural tags for parser-level features:
        [subproofs] (any [:rule "subproof"] step), [named_refs]
        (any [(! INNER :named NAME)] annotation), [discharge_lists]
        (any step with [:discharge ...]).
      A re-checker checks coverage by comparing this list against
      its own implemented set; a missing tag means "needs a
      replayer for this rule/feature."
    * [trace_annotations]: a short human-readable summary
      (step count, rule list, subproof count) for dashboards and
      LLM-assisted reconstruction. Optional per the schema; we
      always emit it.

    Format choice: string vs structured [trace_data]. We store the
    raw S-expr text rather than a JSON-encoded Alethe AST. Pro:
    dialect-neutral envelope, smaller diff to schema, the Lean side
    can use its own parser without negotiating an intermediate
    representation. Con: dashboards can't filter on internal
    structure without re-parsing. The con is worth it — the cert
    is meant to be replayed, not browsed. *)

(** Sorted deduplicated list of every [:rule] name that appears in
    the proof. Stable order so two passthrough certs minted from
    the same proof produce structurally identical payloads. *)
let rule_inventory (p : Alethe.proof) : string list =
  let names = List.map (fun (s : Alethe.step) -> s.rule) p.steps in
  let names = List.filter (fun s -> String.length s > 0) names in
  List.sort_uniq String.compare names

(** Structural Alethe feature tags. Distinct from per-rule tags
    because the Lean re-checker's parser support and per-rule
    checker support evolve independently — a re-checker can
    understand [subproofs] in general but lack a specific rule
    impl, or vice versa. *)
let structural_features (p : Alethe.proof) : string list =
  let has_subproof =
    List.exists (fun (s : Alethe.step) -> s.rule = "subproof") p.steps
  in
  let has_discharge =
    List.exists
      (fun (s : Alethe.step) -> Option.is_some s.discharge)
      p.steps
  in
  let has_named_refs = Hashtbl.length p.table > 0 in
  let acc = [] in
  let acc = if has_subproof then "subproofs" :: acc else acc in
  let acc = if has_discharge then "discharge_lists" :: acc else acc in
  let acc = if has_named_refs then "named_refs" :: acc else acc in
  List.sort String.compare acc

(** The combined feature list shipped in [trace_dialect_features].
    Rules are prefixed with [rule:]; structural tags are bare. *)
let dialect_features (p : Alethe.proof) : string list =
  let rules =
    List.map (fun r -> "rule:" ^ r) (rule_inventory p)
  in
  let structural = structural_features p in
  List.sort_uniq String.compare (rules @ structural)

(** Short single-line summary suitable for [trace_annotations].
    Format: ["alethe-2024 passthrough: N steps, M assumes; rules:
    r1, r2, r3"]. Stable phrasing so log scrapers can extract
    counts. *)
let summarize (p : Alethe.proof) : string =
  let n_steps = List.length p.steps in
  let n_assumes = List.length p.assumes in
  let rules = rule_inventory p in
  Printf.sprintf
    "alethe-2024 passthrough: %d steps, %d assumes; rules: %s"
    n_steps n_assumes
    (if rules = [] then "(none)" else String.concat ", " rules)

(** Build a Tier 3 [Certificate.payload] for an Alethe proof.
    [proof_str] is the raw S-expression captured from the solver;
    [proof] is the result of [Alethe.parse proof_str] (passed
    explicitly so the caller can re-use a parse it already did
    for Tier 1 / Tier 2 extraction). *)
let make_payload ~(proof_str : string) (proof : Alethe.proof)
  : Certificate.payload =
  Certificate.Tier3_proof_trace {
    trace_format = "alethe-2024";
    trace_data = `String proof_str;
    trace_dialect_features = Some (dialect_features proof);
    trace_annotations = Some (summarize proof);
  }

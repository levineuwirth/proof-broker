(** Capability matching: given an [Ir.t] and a [Manifest.t], decide
    whether the adapter is eligible for dispatch (spec v1.0 §7.4).

    Returns one of:
      [Match] — adapter is eligible.
      [Order_too_high] — IR is higher-order, manifest is first-order
        only.
      [Logic_out_of_fragment] — IR's first-order fragment is not in
        the manifest's [logic_fragments] list.
      [Type_construction_not_supported] — some construction kind in
        the IR's [type_metadata] (or the presence of bare type
        variables) is not supported by the manifest's
        [type_constructions].

    Each non-match case carries a [detail] string suitable for
    surfacing in dispatcher logs and dashboards (spec §7.6). The
    matching is conservative: when [logic_classification.first_order_fragment]
    is ["none"] (the source explicitly declined to classify), the
    fragment check is skipped because the IR is genuinely beyond
    fragment-level classification — the type-construction check
    will usually catch the actual mismatch.

    What this v1 implementation does NOT do:
    * Re-run the rewriter to update fragment classification post-rewrite
      before matching. The IR's fragment is set by the source per
      spec §4.4.2 and rewrite passes don't update it; if a future
      pass *does* (e.g., a fragment-recanonicalization pass after
      [quotient_elimination]), the dispatcher would call this
      module on the post-rewrite IR.
    * Validate [type_variable_via_specialization] against an actual
      specialization record — currently it only checks presence of
      [context.type_vars]. The full check belongs with the
      adapter-specialization layer (Phase 2). *)

type reason =
  | Match
  | Order_too_high of { detail : string }
  | Logic_out_of_fragment of { detail : string }
  | Type_construction_not_supported of { detail : string }

let reason_kind = function
  | Match -> "match"
  | Order_too_high _ -> "order_too_high"
  | Logic_out_of_fragment _ -> "logic_out_of_fragment"
  | Type_construction_not_supported _ -> "type_construction_not_supported"

let reason_detail = function
  | Match -> ""
  | Order_too_high { detail }
  | Logic_out_of_fragment { detail }
  | Type_construction_not_supported { detail } -> detail

let reason_to_json (r : reason) : Yojson.Safe.t =
  let kind = reason_kind r in
  let detail = reason_detail r in
  if detail = "" then `Assoc [ "kind", `String kind ]
  else `Assoc [ "kind", `String kind; "detail", `String detail ]

(* --- order check ----------------------------------------------------- *)

let check_order (ir : Ir.t) (m : Manifest.t) : reason option =
  match ir.logic_classification.order, m.max_order with
  | "higher_order", "first_order" ->
    Some (Order_too_high {
      detail = Printf.sprintf
        "ir.order=higher_order but adapter %s declares max_order=first_order"
        m.adapter
    })
  | _ -> None

(* --- fragment check -------------------------------------------------- *)

let check_fragment (ir : Ir.t) (m : Manifest.t) : reason option =
  let frag = ir.logic_classification.first_order_fragment in
  if frag = "none" then None  (* see module-level note *)
  else if List.mem frag m.logic_fragments then None
  else
    Some (Logic_out_of_fragment {
      detail = Printf.sprintf
        "ir.first_order_fragment=%s not in adapter %s's fragments [%s]"
        frag m.adapter (String.concat ", " m.logic_fragments)
    })

(* --- type-construction check ----------------------------------------- *)

(** Collect the construction-kind labels the IR uses. The labels are
    drawn from:
    * [type_metadata[T].constructor.construction_kind] for each
      typed entry whose constructor block was recognized.
    * [type_variable_via_specialization] iff [context.type_vars]
      is non-empty.
    * [primitive] always — every IR uses primitives. *)
let collect_required_constructions (ir : Ir.t) : string list =
  let entries = Type_metadata.parse_all ir in
  let from_metadata =
    Type_metadata.SM.fold
      (fun _ e acc ->
        match e with
        | Type_metadata.TypeConstructorApplication
            { constructor = Quotient _; _ } ->
          "quotient" :: acc
        | TypeConstructorApplication
            { constructor = ConstructorOther { construction_kind; _ }; _ } ->
          construction_kind :: acc
        | OtherKind _ -> acc)
      entries []
  in
  let with_type_vars =
    if ir.context.type_vars = [] then from_metadata
    else "type_variable_via_specialization" :: from_metadata
  in
  let dedup =
    List.fold_left
      (fun acc x -> if List.mem x acc then acc else x :: acc)
      [] with_type_vars
  in
  "primitive" :: List.rev dedup

let check_type_constructions (ir : Ir.t) (m : Manifest.t) : reason option =
  let required = collect_required_constructions ir in
  let unsupported =
    List.filter (fun c -> not (List.mem c m.type_constructions)) required
  in
  match unsupported with
  | [] -> None
  | xs ->
    Some (Type_construction_not_supported {
      detail = Printf.sprintf
        "adapter %s does not support construction kinds [%s]; \
         supports [%s]"
        m.adapter
        (String.concat ", " xs)
        (String.concat ", " m.type_constructions)
    })

(* --- driver ---------------------------------------------------------- *)

(** Run all checks in spec order; return the first failing reason or
    [Match]. The order matters because the failure surfaces in
    dispatcher logs and the most informative reason should win. *)
let check (ir : Ir.t) (m : Manifest.t) : reason =
  match check_order ir m with
  | Some r -> r
  | None ->
    match check_fragment ir m with
    | Some r -> r
    | None ->
      match check_type_constructions ir m with
      | Some r -> r
      | None -> Match

(** Apply [check] to a list of manifests; partition into matches and
    rejections. Order is preserved within each output list relative
    to the input. *)
let select (manifests : Manifest.t list) (ir : Ir.t)
  : Manifest.t list * (Manifest.t * reason) list =
  let rec loop ms matches rejections =
    match ms with
    | [] -> List.rev matches, List.rev rejections
    | m :: rest ->
      (match check ir m with
       | Match -> loop rest (m :: matches) rejections
       | r -> loop rest matches ((m, r) :: rejections))
  in
  loop manifests [] []

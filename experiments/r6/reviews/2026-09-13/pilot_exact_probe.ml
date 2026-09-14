(** Offline review: can the existing exact recovery find the live support?
    The second input retains only hwidth from the saved final IR. This is a
    diagnostic of representability, not a new original-obligation episode. *)
open Proof_broker
module J = Yojson.Safe
let render ir search =
  match search ir with
  | Error _ -> `Assoc ["found", `Bool false]
  | Ok w ->
    let verified = match Farkas.verify ir w with Farkas.Verified -> true | _ -> false in
    `Assoc ["found", `Bool true; "witness", w; "verified", `Bool verified]
let () =
  let packet = J.from_file Sys.argv.(1) in
  let ir = Codec.of_json (Yojson.Safe.Util.member "final_ir" packet) in
  let hs = List.filter (fun (h : Ir.hypothesis) -> h.name = "hwidth") ir.context.hypotheses in
  assert (List.length hs = 1);
  let limited = { ir with context = { ir.context with hypotheses = hs } } in
  let results = `Assoc [
    "full_bounded", render ir Farkas_search.try_close;
    "full_exact", render ir Farkas_search.try_close_exact;
    "hwidth_only_bounded", render limited Farkas_search.try_close;
    "hwidth_only_exact", render limited Farkas_search.try_close_exact;
    "scope", `String "existing SDK search; hwidth-only is a diagnostic context restriction, not a new evaluation episode"
  ] in
  J.pretty_to_channel stdout results; print_newline ()

"""Build a traced copy of the pinned broker; never rebuild C1's binaries.

All edits below add observations to the actual execution. The generated source
diff and hashes are retained with each episode. Search algorithms are unchanged.
"""
from pathlib import Path
import difflib
import os
import shutil
import subprocess

import run as r6

BASE = "e627efe1ee69638678cc94e3f759d93abd69a160"
REPO = r6.ROOT.parents[1]


def original(path):
    return subprocess.check_output(["git", "-C", str(REPO), "show", f"{BASE}:{path}"])


def replace(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"Instrumentation anchor is not unique: {old[:90]}")
    return text.replace(old, new, 1)


SDK_TRACE = r'''(* Process observations, received and sealed by the external supervisor.
   These are not computation attestations. Disabled outside the R6 overlay. *)
let lock = Mutex.create ()
let emit event fields =
  if Sys.getenv_opt "PROOF_BROKER_EPISODE_TRACE" = Some "1" then begin
    let j = `Assoc ["component", `String "sdk"; "event", `String event;
                    "data", `Assoc fields] in
    Mutex.lock lock;
    Fun.protect ~finally:(fun () -> Mutex.unlock lock) (fun () ->
      Printf.eprintf "R6_EVENT %s\n%!" (Yojson.Safe.to_string j))
  end
'''

LEAN_TRACE = r'''
private def episodeEvent (event : String) (fields : List (String × Json)) : TacticM Unit := do
  if (← IO.getEnv "PROOF_BROKER_EPISODE_TRACE") == some "1" then
    let line := "R6_EVENT " ++ (Json.mkObj [
      ("component", toJson "lean_bridge"), ("event", toJson event),
      ("data", Json.mkObj fields)]).compress
    -- Bypass Lean's elaboration-output capture: this is the same OS pipe the
    -- SDK writes, and the supervisor receives each event during execution.
    IO.FS.withFile "/proc/self/fd/2" .append fun handle => do
      handle.putStrLn line
      handle.flush

'''


def sdk_edits(name, text):
    if name == "farkas_search.ml":
        text = replace(text, '''  match try_close ?bound ir with
  | Ok w -> Ok w
  | Error _ -> try_close_exact ir
''', '''  Episode_trace.emit "recovery_started" ["route", `String "bounded_enumeration"];
  match try_close ?bound ir with
  | Ok w ->
    Episode_trace.emit "recovery_finished" ["route", `String "bounded_enumeration";
      "ok", `Bool true; "witness", w];
    Ok w
  | Error e ->
    Episode_trace.emit "recovery_finished" ["route", `String "bounded_enumeration";
      "ok", `Bool false; "reason", `String (kind_of_error e)];
    Episode_trace.emit "recovery_started" ["route", `String "exact_support_bounded"];
    let result = try_close_exact ir in
    Episode_trace.emit "recovery_finished" (["route", `String "exact_support_bounded"] @
      (match result with
       | Ok w -> ["ok", `Bool true; "witness", w]
       | Error e -> ["ok", `Bool false; "reason", `String (kind_of_error e)]));
    result
''')
    if name == "adapter_cvc4.ml":
        text = replace(text, '  (* No shell: see the module header.', '''  Episode_trace.emit "solver_started" ["backend", `String "cvc4";
    "argv", `List (Array.to_list (Array.map (fun s -> `String s) argv));
    "stdin", `String script];
  (* No shell: see the module header.''')
        text = replace(text, '  (out, err, code)\n', '''  Episode_trace.emit "solver_finished" ["backend", `String "cvc4";
    "stdout", `String out; "stderr", `String err; "exit_code", `Int code];
  (out, err, code)
''')
        text = replace(text, '            Cert cert\n', '''            Episode_trace.emit "certificate_created" ["backend", `String "cvc4";
              "producer", `String "sdk_synthesis"; "certificate", Certificate.to_json cert];
            Cert cert
''')
    if name == "dispatch.ml":
        text = replace(text, "                   Succeeded c'\n", """                   Episode_trace.emit "certificate_bound" [
                     "before", Certificate.to_json c; "after", Certificate.to_json c';
                     "manifest", Manifest.to_json m];
                   Succeeded c'
""")
        text = replace(text, '    let result = snapshot () in\n', '''    let result = snapshot () in
    Episode_trace.emit "selection_decided" [
      "manifest_order", `List (Array.to_list (Array.map (fun n -> `String n) names));
      "grace_window_ms", `Int grace_window_ms;
      "selection_rule", `String "tier_preference_then_tier_then_manifest_index";
      "attempts", `List (List.map attempt_to_json result.attempts);
      "certificate", (match result.cert with Some c -> Certificate.to_json c | None -> `Null)];
''')
        text = replace(text, '    List.iter Thread.join handles;\n    result\n', '''    List.iter Thread.join handles;
    Episode_trace.emit "dispatch_returned" [];
    result
''')
    return text


def lean_edits(text):
    text = replace(text, 'private def msSince', LEAN_TRACE + 'private def msSince')
    text = replace(text, '  let (ir, natAtoms, natDefs, skippedLocals) ← Reify.buildIR goal\n', '''  episodeEvent "reification_started" []
  let (ir, natAtoms, natDefs, skippedLocals) ← Reify.buildIR goal
  episodeEvent "reification_finished" [
    ("ir", ProofBroker.IR.IR.toJson ir),
    ("skipped_locals", toJson (skippedLocals.map fun (name, reason) =>
      Json.mkObj [("name", toJson name), ("reason", toJson reason)]))]
''')
    text = replace(text, '  let t0 ← IO.monoMsNow\n  let dispatch ← match runDispatchBroker', '''  episodeEvent "dispatch_started" [
    ("ir", ProofBroker.IR.IR.toJson ir), ("manifests", toJson manifests),
    ("prefer_higher_tier", toJson preferHigherTier)]
  let t0 ← IO.monoMsNow
  let dispatch ← match runDispatchBroker''')
    text = replace(text, '  let dispatchMs ← msSince t0\n', '''  let dispatchMs ← msSince t0
  episodeEvent "dispatch_received" [
    ("dispatch_ms", toJson dispatchMs), ("certificate", toJson dispatch.cert),
    ("final_ir", toJson dispatch.finalIr), ("trace", toJson dispatch.trace)]
''')
    text = replace(text, '    let verif ← match runVerifyCertificateJson cert irForVerify dispatch.trace with\n', '''    episodeEvent "certificate_verification_started" [("certificate", cert)]
    let verif ← match runVerifyCertificateJson cert irForVerify dispatch.trace with
''')
    text = replace(text, '    verifyReason := some verif.reason\n', '''    verifyReason := some verif.reason
    episodeEvent "certificate_verification_finished" [
      ("ok", toJson verif.ok), ("envelope_ok", toJson verif.envelopeOk),
      ("reason", toJson (reprStr verif.reason)), ("certificate", cert)]
''')
    text = replace(text, '  let cert ← match path.cert with\n    | some c => pure c\n    | none => throwError "proof_broker_term: no adapter minted a cert"\n', '''  let cert ← match path.cert with
    | some c => pure c
    | none => throwError "proof_broker_term: no adapter minted a cert"
  episodeEvent "reconstruction_started" [("certificate", cert)]
''')
    text = replace(text, '    closeNatViaTermMode goal goalType cert path.ir path.natAtoms\n    return (path, "term_mode_nat")\n', '''    closeNatViaTermMode goal goalType cert path.ir path.natAtoms
    episodeEvent "reconstruction_finished" [("certificate", cert),
      ("closer", toJson "term_mode_nat"), ("certificate_consumed", toJson true),
      ("derivation_replayed", toJson false), ("residual_closer", toJson "omega")]
    return (path, "term_mode_nat")
''')
    text = replace(text, '  evalTactic (← `(tactic| omega))\n  setGoals prevGoals\n', '''  episodeEvent "residual_started" [("closer", toJson "omega"),
    ("goal", toJson (← ppExpr (← omegaMV.getType)).pretty)]
  evalTactic (← `(tactic| omega))
  unless (← getGoals).isEmpty do throwError "R6 residual closer left goals"
  episodeEvent "residual_finished" [("closer", toJson "omega")]
  setGoals prevGoals
''')
    return text


def build(compiler):
    dest = r6.ROOT / ".cache/instrumented"
    sdk, bridge = dest / "sdk", dest / "bridge"
    diffs = []
    sources = {}

    def save(repo_path, target, edit=lambda x: x):
        base = original(repo_path).decode()
        patched = edit(base)
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or target.read_text() != patched:
            target.write_text(patched)
        sources[repo_path] = {"base_sha256": r6.hashlib.sha256(base.encode()).hexdigest(),
                              "instrumented_sha256": r6.sha(target)}
        diffs.extend(difflib.unified_diff(base.splitlines(True), patched.splitlines(True),
                     fromfile="a/" + repo_path, tofile="b/" + repo_path))

    paths = r6.command(["git", "-C", REPO, "ls-tree", "-r", "--name-only", BASE, "sdk/lib", "sdk/ffi"]).splitlines()
    for path in paths:
        if '/test/' in path:
            continue
        save(path, dest / path, lambda text, name=Path(path).name: sdk_edits(name, text))
    (sdk / "dune-project").write_text('(lang dune 3.21)\n(name proof_broker)\n(package (name proof_broker))\n')
    (sdk / "lib/episode_trace.ml").write_text(SDK_TRACE)
    (sdk / "validate").mkdir(exist_ok=True)
    shutil.copyfile(r6.ROOT / "validate/verify_certificate.ml", sdk / "validate/verify_certificate.ml")
    (sdk / "validate/dune").write_text('(executable (name verify_certificate) (libraries proof_broker yojson))\n')
    subprocess.run(['dune', 'build', '--root', str(sdk), 'ffi/proof_broker_ffi.so', 'validate/verify_certificate.exe'], check=True)

    for name in ['IR', 'Trace', 'Bridge', 'TermMode', 'Alethe', 'Tactic']:
        save(f'lean-bridge/ProofBroker/{name}.lean', bridge/f'ProofBroker/{name}.lean',
             lean_edits if name == 'Tactic' else lambda t: t)
    save('lean-bridge/ProofBroker.lean', bridge/'ProofBroker.lean')
    (bridge/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage «r6-bridge»\nlean_lib ProofBroker where\n  precompileModules := true\n')
    (bridge/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
    subprocess.run([str(compiler/'bin/lake'), 'build', 'ProofBroker'], cwd=bridge, check=True)
    capture = (r6.ROOT/'capture/Capture.lean').read_text()
    capture = replace(capture, 'import Lean\n', 'import Lean\nimport ProofBroker\n')
    capture = replace(capture, 'elab "r6_capture_human"', 'elab "r6_capture_broker"')
    capture = replace(capture, 'evalTactic (← `(tactic| omega))',
                      'let adapter := mkIdent (Name.mkSimple "cvc4")\n  evalTactic (← `(tactic| proof_broker_term [$adapter:ident]))')
    capture = capture.replace('R6 human proof left goals', 'R6 broker proof left goals')
    (dest/'BrokerCapture.lean').write_text(capture)
    return dest, sources, ''.join(diffs)

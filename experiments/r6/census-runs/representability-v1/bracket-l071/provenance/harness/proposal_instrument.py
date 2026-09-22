"""Separate R6-001 overlay: external witness delivery, unchanged reconstruction.

Unlike the R6-000 observation overlay, this intentionally changes dispatch.
Source hashes and its full diff are retained. Original broker binaries remain
in their separate cache. No generated Lean source enters this interface.
"""
import difflib
import functools
from pathlib import Path
import shutil
import subprocess

import instrument
import run as r6

DEST = r6.ROOT/'.cache/proposal-instrumented'
SOURCE_LOCK = r6.ROOT/'policies/fixture-harness-v1.sha256.json'
RETAINED_SOURCES = {'provenance/harness/validate/fixture_responder.c'}
HARNESS_FILES = (
    'proposal_episode.py', 'proposal_audit.py', 'proposal_instrument.py', 'payload.py', 'admission.py',
    'episode.py', 'run.py', 'events.py', 'supervise.py', 'task_spec.py', 'instrument.py',
    'validate/proposal_driver.ml', 'validate/verify_certificate.ml', 'validate/fixture_responder.c',
    'validate/Replay.lean', 'policies/fixture-farkas-v1.json', 'policies/admission-v1.json',
    'schema/proposal-request.schema.json', 'schema/proposal-response.schema.json',
    'schema/proposal-episode.schema.json', 'schema/event.schema.json',
    'test_proposals.py', 'test_task_identity.py', 'policies/fixture-harness-v1.sha256.json')


def source_lock():
    lock = r6.read_json(SOURCE_LOCK)
    expected = {name for name in HARNESS_FILES if not name.startswith('policies/')}
    if set(lock) != expected:
        raise ValueError('Frozen fixture source inventory changed')
    return lock


def verify_live_sources():
    # Launching v1 requires its frozen source revision. Reading an old v1
    # artifact does not require the working tree to remain at that revision.
    if any(r6.sha(r6.ROOT/name) != digest for name, digest in source_lock().items()):
        raise ValueError('Fixture v1 source changed; use its frozen checkout or create a new policy version')

DELIVERY = r'''
private def r6ReadProposal (ir : ProofBroker.IR.IR) : TacticM BrokerResult := do
  let some path ← IO.getEnv "R6_PROPOSAL_PACKET" | throwError "R6_PROPOSAL_PACKET is required"
  let raw ← IO.FS.readFile path
  let packet ← match Json.parse raw with
    | .ok p => pure p | .error e => throwError "R6 proposal JSON: {e}"
  let input ← match packet.getObjVal? "input_ir" with
    | .ok p => pure p | .error e => throwError "R6 proposal input: {e}"
  unless input == ProofBroker.IR.IR.toJson ir do
    throwError "R6 proposal input differs from freshly reified goal/context"
  let cert ← match packet.getObjVal? "certificate" with
    | .ok p => pure p | .error e => throwError "R6 proposal certificate: {e}"
  let finalIr ← match packet.getObjVal? "final_ir" with
    | .ok p => pure p | .error e => throwError "R6 proposal final IR: {e}"
  let traceJson ← match packet.getObjVal? "trace" with
    | .ok p => pure p | .error e => throwError "R6 proposal trace: {e}"
  let trace ← match Trace.Document.fromJson? traceJson with
    | .ok t => pure t | .error e => throwError "R6 proposal trace decode: {e}"
  return {cert := some cert, finalIr := some finalIr, trace := some trace,
          attempts := [{adapter := "r6_fixture_witness", outcome := .succeeded}]}

'''


def lean_edits(source):
    source = instrument.lean_edits(source)
    source = instrument.replace(source, 'private def buildExtractionPath', DELIVERY+'private def buildExtractionPath')
    source = instrument.replace(source, '''  let manifests ← match adapterNames? with
    | some names => loadManifestsByName names
    | none => loadDefaultManifests
''', '''  unless adapterNames? == some ["r6_fixture_witness"] do
    throwError "R6 fixture delivery requires the explicit proposal route"
  let manifests : List Json := []
''')
    source = instrument.replace(source, '''  let dispatch ← match runDispatchBroker ir manifests preferHigherTier with
    | .ok r => pure r
    | .error e => throwError "proof_broker: dispatch_broker failed: {repr e}"
''', '  let dispatch ← r6ReadProposal ir\n')
    return source


def capture_source(task, preparation=False):
    source = task.capture.read_text()
    source = instrument.replace(source, 'import Lean\n', 'import Lean\nimport ProofBroker\n')
    source = source.replace('r6_capture_human', 'r6_prepare' if preparation else 'r6_capture_proposal')
    if preparation:
        # This known-control preparation records IR before running the frozen
        # human closer. That closure never supplies a candidate or model context.
        source = instrument.replace(source, '  let target ← instantiateMVars (← goal.getType)\n', '''  let (ir, _, _, skipped) ← ProofBroker.Tactic.Reify.buildIR goal
  let some irOut ← IO.getEnv "R6_PREPARE_OUTPUT" | throwError "R6_PREPARE_OUTPUT is required"
  let ir := { ir with userDirectives := ir.userDirectives.map fun ud =>
    {ud with tierPreference := some ["1", "2"]} }
  IO.FS.writeFile irOut <| (Json.mkObj [
    ("ir", ProofBroker.IR.IR.toJson ir),
    ("skipped_locals", toJson (skipped.map fun (name, reason) =>
      Json.mkObj [("name", toJson name), ("reason", toJson reason)]))]).compress
  let target ← instantiateMVars (← goal.getType)
''')
    else:
        source = instrument.replace(source, '  evalTactic (← `(tactic| omega))',
            '  let adapter := mkIdent (Name.mkSimple "r6_fixture_witness")\n'
            '  evalTactic (← `(tactic| proof_broker_term [$adapter:ident]))')
    return source


@functools.lru_cache(maxsize=1)
def source_record():
    """Expected base and overlay bytes, without compiling or consulting a cache."""
    paths = r6.command(['git', '-C', instrument.REPO, 'ls-tree', '-r', '--name-only', instrument.BASE,
                       'sdk/lib', 'sdk/ffi']).splitlines()
    paths = [p for p in paths if '/test/' not in p]
    paths += [f'lean-bridge/ProofBroker/{name}.lean' for name in ['IR', 'Trace', 'Bridge', 'TermMode', 'Alethe', 'Tactic']]
    paths += ['lean-bridge/ProofBroker.lean']
    sources, diffs = {}, []
    for name in paths:
        base = instrument.original(name).decode()
        changed = lean_edits(base) if name == 'lean-bridge/ProofBroker/Tactic.lean' else base
        sources[name] = {'base_sha256': r6.hashlib.sha256(base.encode()).hexdigest(),
                         'instrumented_sha256': r6.hashlib.sha256(changed.encode()).hexdigest()}
        diffs.extend(difflib.unified_diff(base.splitlines(True), changed.splitlines(True),
                                        fromfile='a/'+name, tofile='b/'+name))
    return sources, ''.join(diffs)


def build(compiler):
    sdk, bridge = DEST/'sdk', DEST/'bridge'
    sources, diffs = {}, []

    def save(name, target, transform=lambda s: s):
        base = instrument.original(name).decode()
        changed = transform(base)
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or target.read_text() != changed:
            target.write_text(changed)
        sources[name] = {'base_sha256': r6.hashlib.sha256(base.encode()).hexdigest(),
                         'instrumented_sha256': r6.sha(target)}
        diffs.extend(difflib.unified_diff(base.splitlines(True), changed.splitlines(True),
                                        fromfile='a/'+name, tofile='b/'+name))

    paths = r6.command(['git', '-C', instrument.REPO, 'ls-tree', '-r', '--name-only', instrument.BASE,
                       'sdk/lib', 'sdk/ffi']).splitlines()
    for name in paths:
        if '/test/' not in name:
            save(name, DEST/name)
    (sdk/'dune-project').write_text('(lang dune 3.21)\n(name proof_broker)\n(package (name proof_broker))\n')
    (sdk/'validate').mkdir(exist_ok=True)
    for name in ['verify_certificate', 'proposal_driver']:
        shutil.copyfile(r6.ROOT/f'validate/{name}.ml', sdk/f'validate/{name}.ml')
    (sdk/'validate/dune').write_text('(executables (names verify_certificate proposal_driver) (libraries proof_broker yojson))\n')
    subprocess.run(['dune', 'build', '--root', str(sdk), 'ffi/proof_broker_ffi.so',
                    'validate/proposal_driver.exe', 'validate/verify_certificate.exe'], check=True)
    for name in ['IR', 'Trace', 'Bridge', 'TermMode', 'Alethe', 'Tactic']:
        save(f'lean-bridge/ProofBroker/{name}.lean', bridge/f'ProofBroker/{name}.lean',
             lean_edits if name == 'Tactic' else lambda s: s)
    save('lean-bridge/ProofBroker.lean', bridge/'ProofBroker.lean')
    (bridge/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage «r6-proposal»\nlean_lib ProofBroker where\n  precompileModules := true\n')
    (bridge/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
    subprocess.run([str(compiler/'bin/lake'), 'build', 'ProofBroker'], cwd=bridge, check=True)
    return DEST, sources, ''.join(diffs)

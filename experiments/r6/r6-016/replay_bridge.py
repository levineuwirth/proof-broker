"""R6-016 replay bridge: R6-015's (`r6-015/replay_bridge.py`), at R6-016's bridge revision. Only the revision, the build
directory and the package's name change; the overlays and observations are R6-015's, unchanged, and apply to the new
`Tactic.lean` as they stand (the bridge build record checked this).

The Lean bridge is taken from git at `BRIDGE_REV` (`64585867`, approved in R6-016's bridge review), never from the working tree; the SDK, the
independent checker and the assembler from R6's pinned base (`instrument.BASE`), exactly as R6 built them (the SDK is identical at
both revisions). The Tactic text receives, in order and each at exactly one site:

1. R6's frozen overlays, unchanged (`consumption_overlay.lean_edits`): the R6-000 observations, the R6-001 packet delivery
   (`R6_PROPOSAL_PACKET`, guarded by the freshly reified input IR) and the R6-013 closer observations;
2. R6-015's (`EDITS`):
   - `term_route`: the value of `proofBroker.term.constrained` when the closers are reached, so every run records the route it
     took;
   - `closer_selected` inside `closeConstrained`, before each closer runs;
   - after `closeConstrained` returns, the consumption receipt `reconstruction_finished`, naming the certificate, the closer and
     the constrained final step (`final_step: constrained`, `residual_closer: constrained_normalization`);
   - `R6_015_INJECT_UNVERIFIED=1` skips the bridge's own certificate gate, for the deliberate injections of controls 1(b) and 4
     only, and records `certificate_gate_bypassed`. Nothing else changes; the kernel still checks every proof.

Observation and injection only: selection, fact assertion, the fold and the constrained final step (`posOfLinearNum`) are
`BRIDGE_REV`'s. The receipt's `residual_closer: constrained_normalization` names the constrained step, as in R6-015. Identifiers
carried from R6-015 (`R6_015_INJECT_UNVERIFIED`, `r6015CloserSelected`) are kept, so that the observations stay R6-015's to the
byte. Built into its own directory; R6's and R6-015's builds and locks are untouched.
"""
import difflib
import functools
import gzip
import json
from pathlib import Path
import shutil
import subprocess
import sys

R6 = Path(__file__).resolve().parents[1]
if str(R6) not in sys.path: sys.path.insert(0, str(R6))

import consumption_overlay  # noqa: E402
import instrument  # noqa: E402
import proposal_instrument as overlay  # noqa: E402
import run as r6  # noqa: E402

BRIDGE_REV = '64585867afa1194be2b0832b77fd62bbefc2462b'
DEST = r6.ROOT/'.cache/r6-016-replay'
PACKAGE = 'r6-016-replay'
MODULES = ('IR', 'Trace', 'Bridge', 'TermMode', 'Alethe', 'Tactic')
MODULE_PREFIX = 'r6_x2d016_x2dreplay_ProofBroker_'

SELECTED = '''/-- R6-015 observation: the closer the constrained route selected, before it runs. -/
private def r6015ComparisonType (goalType : Expr) : MetaM Json := do
  match goalType.getAppFnArgs with
  | (``LE.le, #[α, _, _, _]) => return toJson (toString (← ppExpr α))
  | (``LT.lt, #[α, _, _, _]) => return toJson (toString (← ppExpr α))
  | (``GE.ge, #[α, _, _, _]) => return toJson (toString (← ppExpr α))
  | (``GT.gt, #[α, _, _, _]) => return toJson (toString (← ppExpr α))
  | _ => return Json.null

private def r6015CloserSelected (closer : String) (cert : Json) (goal : MVarId) (goalType : Expr) : TacticM Unit := do
  let (shown, carrier) ← goal.withContext do
    return (toString (← ppExpr goalType), ← r6015ComparisonType goalType)
  episodeEvent "closer_selected" [("certificate", cert), ("closer", toJson closer),
    ("goal", toJson shown), ("comparison_type", carrier), ("route", toJson "constrained")]

'''
RECEIPT = '''    episodeEvent "reconstruction_finished" [("certificate", cert),
      ("closer", toJson closer), ("certificate_consumed", toJson true),
      ("derivation_replayed", toJson false), ("residual_closer", toJson "constrained_normalization"),
      ("final_step", toJson "constrained"), ("constrained_option", toJson true)]
'''
EDITS = (
    ("/-- R6-015: the constrained route's closer selection", SELECTED+"/-- R6-015: the constrained route's closer selection"),
    ('      closeMixedViaTermMode goal goalType cert ir natAtoms\n      return "term_mode_int"\n',
     '      r6015CloserSelected "term_mode_int" cert goal goalType\n'
     '      closeMixedViaTermMode goal goalType cert ir natAtoms\n      return "term_mode_int"\n'),
    ('    closeNatViaTermMode goal goalType cert ir natAtoms (constrained := true)\n    return "term_mode_nat"\n',
     '    r6015CloserSelected "term_mode_nat" cert goal goalType\n'
     '    closeNatViaTermMode goal goalType cert ir natAtoms (constrained := true)\n    return "term_mode_nat"\n'),
    ('  closeViaTermMode goal goalType cert (constrained := true)\n  return "term_mode_int"\n',
     '  r6015CloserSelected "term_mode_int" cert goal goalType\n'
     '  closeViaTermMode goal goalType cert (constrained := true)\n  return "term_mode_int"\n'),
    ('  if proofBroker.term.constrained.get (← getOptions) then\n'
     '    return (path, ← closeConstrained goal goalType cert path.ir path.natAtoms)\n',
     '  episodeEvent "term_route" [("constrained", toJson (proofBroker.term.constrained.get (← getOptions)))]\n'
     '  if proofBroker.term.constrained.get (← getOptions) then\n'
     '    let closer ← closeConstrained goal goalType cert path.ir path.natAtoms\n'+RECEIPT+'    return (path, closer)\n'),
    ('  unless path.verifyOk == some true do\n    let r := path.verifyReason.map reprStr |>.getD "<unknown>"\n'
     '    throwError "proof_broker_term: cert was minted',
     '  let r6015Unverified := (← IO.getEnv "R6_015_INJECT_UNVERIFIED") == some "1"\n'
     '  if r6015Unverified then\n'
     '    episodeEvent "certificate_gate_bypassed" [("certificate", cert), ("verify_ok", toJson path.verifyOk)]\n'
     '  unless r6015Unverified || path.verifyOk == some true do\n'
     '    let r := path.verifyReason.map reprStr |>.getD "<unknown>"\n'
     '    throwError "proof_broker_term: cert was minted'),
)

# The capture helper: R6's reconstruction helper, with the frozen option setting around the one tactic call.
PINNED_CALL = '  evalTactic (← `(tactic| proof_broker_term [$adapter:ident]))'
CONSTRAINED_CALL = '  evalTactic (← `(tactic| set_option proofBroker.term.constrained true in proof_broker_term [$adapter:ident]))'


def original(path):
    """A bridge source at `BRIDGE_REV`; SDK sources stay at R6's base (`instrument.original`)."""
    if path.startswith('lean-bridge/'):
        return subprocess.check_output(['git', '-C', str(instrument.REPO), 'show', f'{BRIDGE_REV}:{path}'])
    return instrument.original(path)


def lean_edits(source):
    source = consumption_overlay.lean_edits(source)
    for old, new in EDITS:
        source = instrument.replace(source, old, new)
    return source


def capture_source(site_task, task, route):
    """R6's reconstruction helper for the site; `constrained` sets the option around the call, `pinned` leaves it unset."""
    source = site_task.capture_source(task)
    if route == 'constrained': return instrument.replace(source, PINNED_CALL, CONSTRAINED_CALL)
    if route == 'pinned': return instrument.replace(source, PINNED_CALL, PINNED_CALL)
    raise ValueError(f'unknown route {route}')


def sdk_paths():
    return [p for p in r6.command(['git', '-C', instrument.REPO, 'ls-tree', '-r', '--name-only', instrument.BASE, 'sdk/lib', 'sdk/ffi']).splitlines()
            if '/test/' not in p]


@functools.lru_cache(maxsize=1)
def source_record():
    """Base and instrumented digests, and the patch against each base, without building."""
    sources, diffs = {}, []
    for name in sdk_paths() + [f'lean-bridge/ProofBroker/{m}.lean' for m in MODULES] + ['lean-bridge/ProofBroker.lean']:
        base = original(name).decode()
        changed = lean_edits(base) if name.endswith('ProofBroker/Tactic.lean') else base
        sources[name] = {'base': BRIDGE_REV if name.startswith('lean-bridge/') else instrument.BASE,
                         'base_sha256': r6.hashlib.sha256(base.encode()).hexdigest(),
                         'instrumented_sha256': r6.hashlib.sha256(changed.encode()).hexdigest()}
        diffs.extend(difflib.unified_diff(base.splitlines(True), changed.splitlines(True), fromfile='a/'+name, tofile='b/'+name))
    return sources, ''.join(diffs)


def build(compiler):
    """`consumption_overlay.build` with the bridge at `BRIDGE_REV` and R6-015's edits, into `DEST`."""
    sdk, bridge = DEST/'sdk', DEST/'bridge'
    sources, diffs = {}, []

    def save(name, target, transform=lambda s: s):
        base = original(name).decode(); changed = transform(base)
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or target.read_text() != changed: target.write_text(changed)
        sources[name] = {'base': BRIDGE_REV if name.startswith('lean-bridge/') else instrument.BASE,
                         'base_sha256': r6.hashlib.sha256(base.encode()).hexdigest(), 'instrumented_sha256': r6.sha(target)}
        diffs.extend(difflib.unified_diff(base.splitlines(True), changed.splitlines(True), fromfile='a/'+name, tofile='b/'+name))

    for name in sdk_paths(): save(name, DEST/name)
    (sdk/'dune-project').write_text('(lang dune 3.21)\n(name proof_broker)\n(package (name proof_broker))\n')
    (sdk/'validate').mkdir(exist_ok=True)
    for name in ['verify_certificate', 'proposal_driver']:
        shutil.copyfile(r6.ROOT/f'validate/{name}.ml', sdk/f'validate/{name}.ml')
    (sdk/'validate/dune').write_text('(executables (names verify_certificate proposal_driver) (libraries proof_broker yojson))\n')
    subprocess.run(['dune', 'build', '--root', str(sdk), 'ffi/proof_broker_ffi.so',
                    'validate/proposal_driver.exe', 'validate/verify_certificate.exe'], check=True)
    for name in MODULES:
        save(f'lean-bridge/ProofBroker/{name}.lean', bridge/f'ProofBroker/{name}.lean', lean_edits if name == 'Tactic' else lambda s: s)
    save('lean-bridge/ProofBroker.lean', bridge/'ProofBroker.lean')
    (bridge/'lakefile.lean').write_text(f'import Lake\nopen Lake DSL\npackage «{PACKAGE}»\nlean_lib ProofBroker where\n  precompileModules := true\n')
    (bridge/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
    subprocess.run([str(compiler/'bin/lake'), 'build', 'ProofBroker'], cwd=bridge, check=True)
    if (sources, ''.join(diffs)) != source_record(): raise ValueError('built sources differ from the source record')
    return DEST, sources, ''.join(diffs)


def setup(run, site_task, task, packages):
    """`site_task.setup` with this bridge: the frozen setup on the registered D1 control (`consumption_overlay.setup`, its build
    line and module names changed, the fixture responder dropped: there is no network stage), then the site's expectation."""
    _, expected = site_task.frozen_site(task); site_task.same_environment()
    overlay.verify_live_sources()
    _, d1_expected = r6.frozen_task(r6.D1)
    compiler, exporter, checker = r6.build_tools(task=r6.D1)
    dest, sources, patch = build(compiler)
    mounts, lean_path, environment = r6.environment(packages.resolve(), compiler, r6.D1)
    with gzip.open(r6.D1.path/'environment-inventory.json.gz', 'rt') as f:
        if not (environment == d1_expected['environment'] and r6.inventory(mounts, compiler) == json.load(f)):
            raise ValueError('frozen environment changed')
    if d1_expected['environment'] != expected['environment']: raise ValueError('site expectation environment differs from the verified setup')
    native = dest/'bridge/.lake/build/lib/lean'
    modules = [native/f'{MODULE_PREFIX}{name}.so' for name in MODULES]
    if not all(p.exists() for p in modules): raise ValueError('bridge module libraries missing: '+str([p.name for p in modules if not p.exists()]))
    ffi = dest/'sdk/_build/default/ffi/proof_broker_ffi.so'
    glue = r6.ROOT.parents[1]/'lean-bridge/.lake/build/lib/libpbglue.so'
    driver = dest/'sdk/_build/default/validate/proposal_driver.exe'
    verifier = dest/'sdk/_build/default/validate/verify_certificate.exe'
    binaries = [compiler/'bin/lean', exporter, checker, ffi, glue, driver, verifier, *modules]
    provenance = run/'provenance'; provenance.mkdir()
    r6.write_json(provenance/'sources.json', sources)
    (provenance/'instrumentation.patch').write_text(patch)
    r6.write_json(provenance/'binaries.json', {str(p): r6.sha(p) for p in binaries})
    r6.write_json(run/'runtime.json', r6.runtime_record(checker))
    bridge_mounts = [(native, '/broker/modules'), (ffi, '/broker/lib/ffi.so'), (glue, '/broker/lib/glue.so')]
    loads = ['--load-dynlib=/broker/lib/glue.so', '--load-dynlib=/broker/lib/ffi.so']
    loads += [f'--load-dynlib=/broker/modules/{p.name}' for p in modules]
    return {'compiler': compiler, 'exporter': exporter, 'checker': checker, 'driver': driver, 'verifier': verifier,
            'mounts': [*mounts, *bridge_mounts], 'loads': loads, 'extras': [ffi, glue, *modules],
            'lean_path': lean_path+':/broker/modules', 'expected': expected}

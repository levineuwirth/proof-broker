"""R6-013 overlay revision 2: truthful, closer-specific reconstruction observations. Observation only.

The frozen R6-001 overlay (`proposal_instrument.lean_edits`, over `instrument.lean_edits`) emits `reconstruction_finished` only after
the ℕ closer returns, the one path its fixtures used. This revision applies that overlay unchanged and then adds, inside the pinned
`runTermModeOnGoal` at `instrument.BASE`:

* `closer_selected` immediately before each closer is called: the closer's name, the certificate, the goal and the comparison's
  carrier type as Lean prints them. It is branch evidence, emitted before the closer can succeed or fail;
* after `closeViaTermMode` (the core ℤ closer) returns, `reconstruction_finished` with the ℕ receipt's fields. Both closers consume the
  witness through the same arity-N fold, `closeViaTermModeFalse`, which ends in `closeOmegaSubgoal` (`omega` on the literal
  positivity subgoal only), so the fields `certificate_consumed`, `derivation_replayed: false` and `residual_closer: omega` are the
  implementation's, not copied;
* after an extension closer returns (`term_mode_poly`, `term_mode_case_split`, `term_mode_ext`), `closer_returned` with the closer and
  certificate only. The extension closers live outside the pinned core; this overlay claims no consumption for them, and no fixture
  here exercises them.

No guard, dispatch, verification or proof construction changes; each edit inserts an observation around an existing call. The
bridge is built into its own directory, so the frozen build and its lock are untouched. `setup` is `proposal_episode.setup` with its
one build line pointed here; `test_site.py` pins that difference and the edit population.
"""
import difflib
import functools
import gzip
import json
import shutil
import subprocess

import episode
import instrument
from proposal_episode import require
import proposal_instrument as overlay
import run as r6

REVISION = 2
DEST = r6.ROOT/'.cache/proposal-instrumented-r2'
SELECTED = '''/-- R6-013 observation helpers: the selected closer, the goal, and the comparison's carrier type. -/
private def r6ComparisonType (goalType : Expr) : MetaM Json := do
  match goalType.getAppFnArgs with
  | (``LE.le, #[α, _, _, _]) => return toJson (toString (← ppExpr α))
  | (``LT.lt, #[α, _, _, _]) => return toJson (toString (← ppExpr α))
  | (``GE.ge, #[α, _, _, _]) => return toJson (toString (← ppExpr α))
  | (``GT.gt, #[α, _, _, _]) => return toJson (toString (← ppExpr α))
  | _ => return Json.null

private def r6CloserSelected (closer : String) (cert : Json) (goal : MVarId) (goalType : Expr) : TacticM Unit := do
  let (shown, carrier) ← goal.withContext do
    return (toString (← ppExpr goalType), ← r6ComparisonType goalType)
  episodeEvent "closer_selected" [("certificate", cert), ("closer", toJson closer),
    ("goal", toJson shown), ("comparison_type", carrier)]

'''
INT_RECEIPT = '''episodeEvent "reconstruction_finished" [("certificate", cert),
{i}  ("closer", toJson "term_mode_int"), ("certificate_consumed", toJson true),
{i}  ("derivation_replayed", toJson false), ("residual_closer", toJson "omega")]'''
# (frozen overlay text, revision 2 text): every edit wraps an existing call and changes nothing else.
EDITS = (
    ('/-- Single-goal term-mode pipeline: build the IR + dispatch + verify\n', SELECTED+'/-- Single-goal term-mode pipeline: build the IR + dispatch + verify\n'),
    ('    closeNatViaTermMode goal goalType cert path.ir path.natAtoms\n    episodeEvent "reconstruction_finished"',
     '    r6CloserSelected "term_mode_nat" cert goal goalType\n    closeNatViaTermMode goal goalType cert path.ir path.natAtoms\n    episodeEvent "reconstruction_finished"'),
    ('    | some ext => ext.polyFarkasCloser cert path.ir\n    | none =>\n      throwError "proof_broker_term: polymorphic-α cert minted but no',
     '    | some ext =>\n      r6CloserSelected "term_mode_poly" cert goal goalType\n      ext.polyFarkasCloser cert path.ir\n'
     '      episodeEvent "closer_returned" [("certificate", cert), ("closer", toJson "term_mode_poly")]\n'
     '    | none =>\n      throwError "proof_broker_term: polymorphic-α cert minted but no'),
    ('    | some ext => ext.tier2CaseSplitCloser cert path.ir; pure (path, "term_mode_case_split")\n',
     '    | some ext =>\n      r6CloserSelected "term_mode_case_split" cert goal goalType\n      ext.tier2CaseSplitCloser cert path.ir\n'
     '      episodeEvent "closer_returned" [("certificate", cert), ("closer", toJson "term_mode_case_split")]\n'
     '      pure (path, "term_mode_case_split")\n'),
    ('        ext.tier1FarkasCloser cert path.ir; pure (path, "term_mode_ext")\n',
     '        r6CloserSelected "term_mode_ext" cert goal goalType\n        ext.tier1FarkasCloser cert path.ir\n'
     '        episodeEvent "closer_returned" [("certificate", cert), ("closer", toJson "term_mode_ext")]\n'
     '        pure (path, "term_mode_ext")\n'),
    ('      else\n        closeViaTermMode goal goalType cert; pure (path, "term_mode_int")\n',
     '      else\n        r6CloserSelected "term_mode_int" cert goal goalType\n        closeViaTermMode goal goalType cert\n'
     '        '+INT_RECEIPT.format(i='        ')+'\n        pure (path, "term_mode_int")\n'),
    ('    | none =>\n      closeViaTermMode goal goalType cert; pure (path, "term_mode_int")\n',
     '    | none =>\n      r6CloserSelected "term_mode_int" cert goal goalType\n      closeViaTermMode goal goalType cert\n'
     '      '+INT_RECEIPT.format(i='      ')+'\n      pure (path, "term_mode_int")\n'),
)


def lean_edits(source):
    """The frozen overlay, then the revision 2 observations, each at exactly one site."""
    source = overlay.lean_edits(source)
    for old, new in EDITS:
        source = instrument.replace(source, old, new)
    return source


@functools.lru_cache(maxsize=1)
def source_record():
    """`proposal_instrument.source_record` for this revision: base and overlay digests, and the patch against the pinned base."""
    paths = r6.command(['git', '-C', instrument.REPO, 'ls-tree', '-r', '--name-only', instrument.BASE, 'sdk/lib', 'sdk/ffi']).splitlines()
    paths = [p for p in paths if '/test/' not in p]
    paths += [f'lean-bridge/ProofBroker/{name}.lean' for name in ['IR', 'Trace', 'Bridge', 'TermMode', 'Alethe', 'Tactic']]
    paths += ['lean-bridge/ProofBroker.lean']
    sources, diffs = {}, []
    for name in paths:
        base = instrument.original(name).decode()
        changed = lean_edits(base) if name == 'lean-bridge/ProofBroker/Tactic.lean' else base
        sources[name] = {'base_sha256': r6.hashlib.sha256(base.encode()).hexdigest(),
                         'instrumented_sha256': r6.hashlib.sha256(changed.encode()).hexdigest()}
        diffs.extend(difflib.unified_diff(base.splitlines(True), changed.splitlines(True), fromfile='a/'+name, tofile='b/'+name))
    return sources, ''.join(diffs)


def build(compiler):
    """`proposal_instrument.build` into this revision's directory with this revision's Tactic edits; everything else identical."""
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


# `proposal_episode.setup` below, verbatim but for this one line.
SETUP_LINE = '    dest, sources, patch = overlay.build(compiler)\n'
SETUP_LINE_R2 = '    dest, sources, patch = build(compiler)\n'


def setup(run, task, packages):
    overlay.verify_live_sources()
    _, expected = r6.frozen_task(task)
    compiler, exporter, checker = r6.build_tools(task=task)
    dest, sources, patch = build(compiler)
    mounts, lean_path, environment = r6.environment(packages.resolve(), compiler, task)
    with gzip.open(task.path/'environment-inventory.json.gz', 'rt') as f:
        require(environment == expected['environment'] and r6.inventory(mounts, compiler) == json.load(f),
                'frozen environment changed')
    native = dest/'bridge/.lake/build/lib/lean'
    modules = [native/f'r6_x2dproposal_ProofBroker_{name}.so' for name in ['IR', 'Trace', 'Bridge', 'TermMode', 'Alethe', 'Tactic']]
    ffi = dest/'sdk/_build/default/ffi/proof_broker_ffi.so'
    glue = r6.ROOT.parents[1]/'lean-bridge/.lake/build/lib/libpbglue.so'
    driver = dest/'sdk/_build/default/validate/proposal_driver.exe'
    verifier = dest/'sdk/_build/default/validate/verify_certificate.exe'
    fixture = dest/'fixture'
    subprocess.run(['cc', '-O0', str(r6.ROOT/'validate/fixture_responder.c'), '-o', str(fixture)], check=True)
    binaries = [compiler/'bin/lean', exporter, checker, ffi, glue, driver, verifier, fixture, *modules]
    provenance = run/'provenance'
    provenance.mkdir()
    r6.write_json(provenance/'sources.json', sources)
    (provenance/'instrumentation.patch').write_text(patch)
    r6.write_json(provenance/'binaries.json', {str(p): r6.sha(p) for p in binaries})
    for name in overlay.HARNESS_FILES:
        target = provenance/'harness'/name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(r6.ROOT/name, target)
    r6.write_json(run/'runtime.json', r6.runtime_record(checker))
    r6.write_json(provenance/'fixture-runtime.json', [
        {'host': str(p.resolve()), 'guest': str(p), 'sha256': r6.sha(p)} for p in episode.libraries(fixture)])
    bridge_mounts = [(native, '/broker/modules'), (ffi, '/broker/lib/ffi.so'), (glue, '/broker/lib/glue.so')]
    loads = ['--load-dynlib=/broker/lib/glue.so', '--load-dynlib=/broker/lib/ffi.so']
    loads += [f'--load-dynlib=/broker/modules/{p.name}' for p in modules]
    return {'compiler': compiler, 'exporter': exporter, 'checker': checker, 'driver': driver, 'verifier': verifier,
            'fixture': fixture, 'mounts': [*mounts, *bridge_mounts], 'loads': loads,
            'extras': [ffi, glue, *modules], 'lean_path': lean_path+':/broker/modules', 'expected': expected}

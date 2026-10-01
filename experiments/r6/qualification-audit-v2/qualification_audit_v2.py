#!/usr/bin/env python3
"""Driver for the R6 qualification-1 audit, amended (`R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md`, revision 3), build
revision 3. `qualification-audit-v1` and its files are only read; this driver imports v1's driver for its control expectations
and its `Nat.rec` mutation, unchanged.

    build                  build the amended program (Lean 4.32.2) and the controls (Lean 4.32.0, R6's pinned exporter)
    controls --output      run C1-C9 and R1-R9b and assert their frozen expectations
    lock                   write `qualification-audit-v2`, once, after the implementation review
    regression --output    application 1: R6's 32 classified slots must reproduce addendum 1 (classifications and mappings)
    addendum2 --output     application 2: R6's 16 slots at l096 and l099, with their sealed rename rows
    l175 --output          application 3: R6-015's 17 proofs at l175, informational only

Every application refuses unless the lock verifies, and verifies it again afterwards, with the locks of the evidence it reads
(`live-evaluation-v3` for R6's runs, `r6-015-replay-v1` for R6-015's). Offline: no provider, credential or spending.
"""
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
REPO = R6.parents[1]
V1 = R6/'qualification-audit'
_spec = importlib.util.spec_from_file_location('qualification_audit_v1', V1/'qualification_audit.py')
v1 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(v1)

BUILD = R6/'.cache/qualification-audit-v2'
TOOLCHAIN, CONTROLS_TOOLCHAIN, EXPORTER = v1.TOOLCHAIN, v1.CONTROLS_TOOLCHAIN, v1.EXPORTER
TOOL = BUILD/'.lake/build/bin/r6-qualification-audit'
LOCK = R6/'policies/qualification-audit-v2.sha256.json'
V1_AUDIT = R6/'reviews/2026-10-01/R6-QUALIFICATION-1-AUDIT.json'
R6015_LOCK = R6/'policies/r6-015-replay-v1.sha256.json'
R6015_RUNS = R6/'r6-015-runs'
SOURCES = [HERE/'Audit.lean', HERE/'make_controls.py', HERE/'R6AuditControlsV2.lean', HERE/'R6AuditControlsV2.provenance.json',
           Path(__file__).resolve(), V1/'qualification_audit.py', V1/'make_controls.py',
           R6/'vendor/lean4export/Export/Parse.lean', R6/'vendor/lean4export/Export.lean']
EXPORTS = ['c1', 'c2', 'c3', 'c4', 'c5', 'c6', 'r1', 'r7l', 'r7n', 'r7b', 'r8', 'r9', 'r9b']
UNBOUND = 'unbound_residual_mismatch'

# R1-R6: one export, a synthetic frozen context, and the rows each control passes
R1_CONTEXT = [{'index': 0, 'name': 'r1_local', 'included_in_telescope': False}, {'index': 1, 'name': 'x', 'included_in_telescope': True},
              {'index': 2, 'name': "c'", 'included_in_telescope': True}, {'index': 3, 'name': 'h', 'included_in_telescope': True}]
R1_RESIDUAL = '0 < 1 * (x - c_) + 1 * (c_ + 1 - x)'
def _row(i, o, s): return {'index': i, 'original_name': o, 'search_name': s, 'fvar_in_original': True}
RENAMES = {'R1': [_row(2, "c'", 'c_')], 'R2': [_row(2, "c'", 'd_')], 'R3': [_row(2, "c'", 'c_'), _row(2, "c'", 'e_')],
           'R4': [_row(2, "c'", 'x')], 'R5': [_row(2, "c'", 'c_'), _row(3, 'h', 'c_')], 'R6': [_row(3, "c'", 'c_')]}

sha, run = v1.sha, v1.run


def build(_):
    if BUILD.exists(): shutil.rmtree(BUILD)
    BUILD.mkdir(parents=True)
    shutil.copytree(R6/'vendor/lean4export/Export', BUILD/'Export')
    shutil.copyfile(R6/'vendor/lean4export/Export.lean', BUILD/'Export.lean')
    shutil.copyfile(HERE/'Audit.lean', BUILD/'Audit.lean')
    (BUILD/'lakefile.toml').write_text('name = "r6qualauditv2"\n[[lean_lib]]\nname = "Export"\n'
                                       '[[lean_exe]]\nname = "r6-qualification-audit"\nroot = "Audit"\nsupportInterpreter = true\n')
    (BUILD/'lean-toolchain').write_text('leanprover/lean4:v4.32.2\n')
    run([str(TOOLCHAIN/'bin/lake'), 'build', 'r6-qualification-audit'], cwd=BUILD)
    run([sys.executable, str(HERE/'make_controls.py')])
    ctl = BUILD/'controls'; ctl.mkdir()
    shutil.copyfile(HERE/'R6AuditControlsV2.lean', ctl/'R6AuditControlsV2.lean')
    env = {'LEAN_PATH': f"{REPO/'lean-bridge/.lake/build/lib/lean'}:{ctl}", 'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(CONTROLS_TOOLCHAIN)}
    run([str(CONTROLS_TOOLCHAIN/'bin/lean'), 'R6AuditControlsV2.lean', '-o', 'R6AuditControlsV2.olean'], cwd=ctl, env=env,
        stdout=subprocess.DEVNULL)
    for c in EXPORTS:
        with open(ctl/f'{c}.ndjson', 'wb') as out:
            run([str(EXPORTER), 'R6AuditControlsV2', '--', f'R6Audit.{c}_local', f'R6Audit.{c}_whole'], cwd=ctl, stdout=out, env=env)
    v1.mutate_nat_rec(ctl/'c2.ndjson', ctl/'c7.ndjson')
    for name, rows in RENAMES.items():
        (ctl/f'rename-{name}.json').write_text(json.dumps({'rows': rows, 'context': R1_CONTEXT}, indent=1) + '\n')
    print(json.dumps({'tool': sha(TOOL), 'controls': controls_digests()}, indent=1))


def controls_digests():
    ctl = BUILD/'controls'
    return {p.name: sha(p) for p in sorted(ctl.glob('*.ndjson')) + sorted(ctl.glob('rename-*.json'))}


def audit_one(export, local, whole, residual, rename=None, force=False, synthetic=False):
    with tempfile.TemporaryDirectory(prefix='r6-qual-audit-v2-') as tmp:
        tmp = Path(tmp)
        if residual is not None: (tmp/'residual.txt').write_text(residual + '\n')
        if rename is not None: (tmp/'rename.json').write_text(json.dumps(rename))
        flags = (['--force-abstraction'] if force else []) + (['--synthetic'] if synthetic else []) + \
                ([f"--rename={tmp/'rename.json'}"] if rename is not None else [])
        cmd = [str(TOOL), *flags, str(export), local, whole, '-' if residual is None else str(tmp/'residual.txt'), str(tmp/'report.json')]
        proc = subprocess.run(cmd, capture_output=True, text=True, env={'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(TOOLCHAIN)})
        r = json.loads((tmp/'report.json').read_text()) if (tmp/'report.json').exists() else {'error': (proc.stdout + proc.stderr)[-2000:]}
        r['exit'] = proc.returncode
        return r


def names(section): return [h['name'] for h in (section or {}).get('hypotheses', [])]
def paths(section, name): return [h['path'][:1] for h in (section or {}).get('hypotheses', []) if h['name'] == name]
def cls(a, t): return (a.get(t) or {}).get('classification')
def check(pairs): return [m for m, bad in pairs if bad]


def walk_case(stem, internal):
    return lambda r, a: check([
        ('the parameters must be established, three', (a.get('parameters') or {}).get('count') != 3),
        ('the whole must be locatable', (a.get('whole') or {}).get('locatable') is not True),
        ('h must map through argument 1', paths(a.get('whole'), 'h') != [[f'parameter 1 of R6Audit.{stem}_local']]),
        ('hn must map through argument 2', paths(a.get('whole'), 'hn') not in ([], [[f'parameter 2 of R6Audit.{stem}_local']])),
        (f'{internal} may only be internal', any(p != ['internal to the local proof'] for p in paths(a.get('whole'), internal)))])


# amendment 1's controls: name -> (export stem, residual (None: synthetic), rename case, expectation)
R_RUNS = {
    'R1': ('r1', R1_RESIDUAL, 'R1', lambda r, a: check([
        ('binding must match after renaming', a.get('binding') != 'matches_residual_after_renaming'),
        ('the classification must be made, both targets', UNBOUND in (cls(a, 'local'), cls(a, 'whole')) or None in (cls(a, 'local'), cls(a, 'whole')))])),
    'R2': ('r1', R1_RESIDUAL, 'R2', lambda r, a: check([
        ('binding must be a mismatch', a.get('binding') != 'residual_mismatch'),
        ('both targets unbound', (cls(a, 'local'), cls(a, 'whole')) != (UNBOUND, UNBOUND))])),
    **{k: ('r1', R1_RESIDUAL, k, lambda r, a: check([
        ('binding must be rename_unverified', a.get('binding') != 'rename_unverified'),
        ('both targets unbound', (cls(a, 'local'), cls(a, 'whole')) != (UNBOUND, UNBOUND))])) for k in ('R3', 'R4', 'R5', 'R6')},
    'R7l': ('r7l', None, None, walk_case('r7l', '_q')),
    'R7n': ('r7n', None, None, walk_case('r7n', '_q')),
    'R7b': ('r7b', None, None, walk_case('r7b', '_r')),
    'R8': ('r8', None, None, lambda r, a: check([
        ('the parameters must be established, two', (a.get('parameters') or {}).get('count') != 2),
        ('the whole must not be locatable, by arity', (a.get('whole') or {}).get('locatable') is not False
         or 'arity #[3] for 2 parameters' not in (a.get('whole') or {}).get('reason', ''))])),
    'R9': ('r9', None, None, lambda r, a: check([
        ('the parameters must be unverified', (a.get('parameters') or {}).get('established') is not False
         or 'parameters_unverified' not in (a.get('parameters') or {}).get('reason', '')),
        ('the whole must not be locatable', (a.get('whole') or {}).get('locatable', False) is not False)])),
    'R9b': ('r9b', None, None, lambda r, a: check([
        ('the parameters must be unverified', (a.get('parameters') or {}).get('established') is not False),
        ('the whole must not be locatable', (a.get('whole') or {}).get('locatable') is not False)])),
}


def controls(args):
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    ctl = BUILD/'controls'; results, failures = {}, {}
    for c, (exp, stem, residual, force) in v1.RUNS.items():   # C1-C9: v1's runs and frozen expectations, on the amended program
        r = audit_one(ctl/f'{exp}.ndjson', f'R6Audit.{stem}_local', f'R6Audit.{stem}_whole', residual, force=force, synthetic=residual is None)
        a = r.get('audit', {})
        failures[f'C{c}'] = v1.EXPECT[c](r, a) if ('local' in a or c == 7) else ['no report: ' + json.dumps(r)[:300]]
        results[f'C{c}'] = r
    for name, (stem, residual, rename, expect) in R_RUNS.items():
        rename_input = json.loads((ctl/f'rename-{rename}.json').read_text()) if rename else None
        r = audit_one(ctl/f'{stem}.ndjson', f'R6Audit.{stem}_local', f'R6Audit.{stem}_whole', residual, rename=rename_input,
                      synthetic=residual is None)
        failures[name] = expect(r, r.get('audit', {})) if 'audit' in r else ['no report: ' + json.dumps(r)[:300]]
        results[name] = r
    for name, unmet in failures.items(): print(name, 'as expected' if not unmet else unmet, flush=True)
    passed = not any(failures.values())
    out.write_text(json.dumps({'passed': passed, 'failures': failures, 'results': results, 'tool_sha256': sha(TOOL),
                               'controls_sha256': controls_digests(), 'sources_sha256': {str(p.relative_to(REPO)): sha(p) for p in SOURCES},
                               'scope': 'synthetic controls only; no retained R6 or R6-015 export read'}, indent=1) + '\n')
    print(json.dumps({'passed': passed}))
    return 0 if passed else 1


def selection():
    """The three applications' inputs, every consumed artifact checked against its seal."""
    sys.path.insert(0, str(R6)); sys.dont_write_bytecode = True
    import site_task
    v1_selection = json.loads(v1.LOCK.read_text())['selection']
    v1_audit = json.loads(V1_AUDIT.read_text())['slots']
    regression, renamed = {}, {}
    for key, s in sorted(v1_selection.items()):
        a = v1_audit[key]['audit']; run_dir = REPO/s['run']
        seal = json.loads((run_dir/'seal.json').read_text())['retained_sha256']
        if sha(run_dir/'seal.json') != s['seal_sha256'] or sha(run_dir/'solution.ndjson.gz') != s['solution.ndjson.gz_sha256']:
            raise SystemExit(f'{key} differs from qualification-audit-v1')
        if cls(a, 'local') != UNBOUND:
            regression[key] = {**s, 'v1': {'local': cls(a, 'local'), 'whole': cls(a, 'whole'),
                                           'whole_hypotheses': (a.get('whole') or {}).get('hypotheses')}}
            continue
        reification = 'stages/preparation/output/reification.json'
        if seal.get(reification) != sha(run_dir/reification): raise SystemExit(f'{key}: {reification} differs from its seal')
        rows = [r for r in json.loads((run_dir/reification).read_text())['search_context'] if r['original_name'] != r['search_name']]
        site = key.split('/')[0]; task = site_task.get(site)
        context_path = task.path/'context/local-context.json'
        context = [{'index': e['index'], 'name': e['name'], 'included_in_telescope': e['included_in_telescope']}
                   for e in json.loads(context_path.read_text())['telescope']]
        renamed[key] = {**s, 'rename': {'rows': [{k: r[k] for k in ('index', 'original_name', 'search_name', 'fvar_in_original')} for r in rows],
                                        'context': context},
                        'reification_sha256': sha(run_dir/reification), 'context_sha256': sha(context_path)}
    if (len(regression), len(renamed)) != (32, 16): raise SystemExit(f'selection: {len(regression)} and {len(renamed)}')
    l175 = {}
    task = site_task.get('bracket-l175')
    for run_dir in sorted(R6015_RUNS.glob('l175-*')):
        verdict = json.loads((run_dir/'verdict.json').read_text())
        if verdict['outcome'] != 'proved': continue
        seal = json.loads((run_dir/'seal.json').read_text())['retained_sha256']
        for f in ('solution.ndjson.gz', 'residual.txt', 'verdict.json'):
            if seal.get(f) != sha(run_dir/f): raise SystemExit(f'{run_dir.name}/{f} differs from its seal')
        l175[run_dir.name] = {'run': str(run_dir.relative_to(REPO)), 'local': task.local, 'whole': task.whole,
                              'residual_goal': (run_dir/'residual.txt').read_text().rstrip('\n'), 'seal_sha256': sha(run_dir/'seal.json'),
                              'solution.ndjson.gz_sha256': sha(run_dir/'solution.ndjson.gz')}
    if len(l175) != 17: raise SystemExit(f'selection: {len(l175)} l175 proofs')
    return {'regression': regression, 'addendum2': renamed, 'l175': l175}


def lock_record():
    return {'schema_version': 'r6-qualification-audit-lock-2', 'tool_sha256': sha(TOOL),
            'toolchain': 'leanprover/lean4:v4.32.2', 'controls_toolchain': 'leanprover/lean4:v4.32.0',
            'sources_sha256': {str(p.relative_to(REPO)): sha(p) for p in SOURCES}, 'controls_sha256': controls_digests(),
            'exporter_sha256': sha(EXPORTER), 'qualification_audit_v1_lock_sha256': sha(v1.LOCK),
            'qualification_audit_v1_record_sha256': sha(V1_AUDIT), 'r6_015_lock_sha256': sha(R6015_LOCK),
            'selection': selection()}


def lock(_):
    if LOCK.exists(): raise SystemExit(f'refusing to overwrite {LOCK}')
    LOCK.write_text(json.dumps(lock_record(), indent=1, sort_keys=True) + '\n')
    print(sha(LOCK))


def verify_lock():
    if not LOCK.exists(): raise SystemExit('refused: no lock (the implementation review comes first)')
    frozen = json.loads(LOCK.read_text())
    if frozen != lock_record(): raise SystemExit('refused: the lock does not verify')
    return frozen


def verify_r6015():
    run([sys.executable, '-c', 'import sys; sys.path[:0] = [sys.argv[1], sys.argv[2]]; import replay_lock; replay_lock.verify_lock()',
         str(R6), str(R6/'r6-015')], stdout=subprocess.DEVNULL)


def application(name, args, evidence):
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    frozen = verify_lock(); evidence()
    results = {}
    for key, s in sorted(frozen['selection'][name].items()):
        with tempfile.TemporaryDirectory(prefix='r6-qual-v2-export-') as tmp:
            raw = (REPO/s['run']/'solution.ndjson.gz').read_bytes()
            if v1.hashlib.sha256(raw).hexdigest() != s['solution.ndjson.gz_sha256']: raise SystemExit(f'export changed: {key}')
            export = Path(tmp)/'solution.ndjson'; export.write_bytes(gzip.decompress(raw))
            results[key] = audit_one(export, s['local'], s['whole'], s['residual_goal'], rename=s.get('rename'))
        a = results[key].get('audit', {})
        print(key, a.get('binding'), cls(a, 'local'), cls(a, 'whole'), flush=True)
    evidence(); verify_lock()
    return out, frozen, results


def regression(args):
    out, frozen, results = application('regression', args, v1.verify_live_evaluation)
    differences = {}
    for key, s in frozen['selection']['regression'].items():
        a = results[key].get('audit', {})
        got = {'local': cls(a, 'local'), 'whole': cls(a, 'whole'), 'whole_hypotheses': (a.get('whole') or {}).get('hypotheses')}
        if got != s['v1']: differences[key] = {'v1': s['v1'], 'v2': got}
    out.write_text(json.dumps({'application': 'regression', 'reproduced': not differences, 'differences': differences, 'results': results,
                               'lock_sha256': sha(LOCK)}, indent=1) + '\n')
    print(json.dumps({'reproduced': not differences, 'differences': len(differences)}))
    return 0 if not differences else 1


def addendum2(args):
    out, frozen, results = application('addendum2', args, v1.verify_live_evaluation)
    out.write_text(json.dumps({'application': 'addendum2', 'results': results, 'lock_sha256': sha(LOCK),
                               'scope': "R6's 16 slots at l096 and l099; addendum 1 unchanged"}, indent=1) + '\n')


def l175(args):
    out, frozen, results = application('l175', args, verify_r6015)
    out.write_text(json.dumps({'application': 'l175', 'results': results, 'lock_sha256': sha(LOCK),
                               'scope': "R6-015's 17 proofs at l175, informational; R6-015's result and control 8 unchanged"}, indent=1) + '\n')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    sub.add_parser('build').set_defaults(f=build)
    for name, f in (('controls', controls), ('regression', regression), ('addendum2', addendum2), ('l175', l175)):
        c = sub.add_parser(name); c.add_argument('--output', required=True); c.set_defaults(f=f)
    sub.add_parser('lock').set_defaults(f=lock)
    args = p.parse_args()
    sys.exit(args.f(args) or 0)


if __name__ == '__main__':
    main()

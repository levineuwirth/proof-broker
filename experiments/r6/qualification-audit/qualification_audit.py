#!/usr/bin/env python3
"""Driver for the R6 qualification-1 audit (`experiments/r6/R6-QUALIFICATION-1-AUDIT-PROPOSAL.md`, revision 2), build revision 2.

    build              build the tool (Lean 4.32.2) and the controls (Lean 4.32.0, R6's pinned exporter)
    controls --output  run the tool on controls C1-C9 and assert their frozen expectations
    lock               freeze the tool, controls, driver, the 48-slot selection and every consumed artifact's digest
                       (only after the implementation review)
    audit --output     audit R6's 48 proof exports; refuses unless the lock verifies, and verifies it again afterwards

Offline: no provider, credential, episode or spending. R6's evidence is only read. The lock binds the analysis file that selects
the 48, each slot's targets and retained residual goal, and the digests of each run's seal, export and event chain (each also
checked against the seal); `audit` recomputes all of it before and after, and verifies `live-evaluation-v3` before and after.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
REPO = R6.parents[1]
BUILD = R6/'.cache/qualification-audit'
TOOLCHAIN = Path.home()/'build/elan/toolchains/leanprover--lean4---v4.32.2'   # the tool: R6's final-validation kernel
CONTROLS_TOOLCHAIN = Path.home()/'build/elan/toolchains/leanprover--lean4---v4.32.0'   # the controls: the lean-bridge's pin
EXPORTER = R6/'.cache/exporter/.lake/build/bin/lean4export'
TOOL = BUILD/'.lake/build/bin/r6-qualification-audit'
LOCK = R6/'policies/qualification-audit-v1.sha256.json'
ANALYSIS = R6/'reviews/2026-09-29/R6-014-BLOCK2-ANALYSIS.json'
SOURCES = [HERE/'Audit.lean', HERE/'make_controls.py', HERE/'R6AuditControls.lean', HERE/'R6AuditControls.provenance.json',
           Path(__file__).resolve(), R6/'vendor/lean4export/Export/Parse.lean', R6/'vendor/lean4export/Export.lean']
C2_RESIDUAL = '0 < 1 * (x - y) + 1 * (y + 1 - x)'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, **kw)


def build(_):
    if BUILD.exists(): shutil.rmtree(BUILD)
    BUILD.mkdir(parents=True)
    shutil.copytree(R6/'vendor/lean4export/Export', BUILD/'Export')
    shutil.copyfile(R6/'vendor/lean4export/Export.lean', BUILD/'Export.lean')
    shutil.copyfile(HERE/'Audit.lean', BUILD/'Audit.lean')
    (BUILD/'lakefile.toml').write_text('name = "r6qualaudit"\n[[lean_lib]]\nname = "Export"\n'
                                       '[[lean_exe]]\nname = "r6-qualification-audit"\nroot = "Audit"\nsupportInterpreter = true\n')
    (BUILD/'lean-toolchain').write_text('leanprover/lean4:v4.32.2\n')
    run([str(TOOLCHAIN/'bin/lake'), 'build', 'r6-qualification-audit'], cwd=BUILD)
    run([sys.executable, str(HERE/'make_controls.py')])
    ctl = BUILD/'controls'; ctl.mkdir()
    shutil.copyfile(HERE/'R6AuditControls.lean', ctl/'R6AuditControls.lean')
    env = {'LEAN_PATH': f"{REPO/'lean-bridge/.lake/build/lib/lean'}:{ctl}", 'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(CONTROLS_TOOLCHAIN)}
    run([str(CONTROLS_TOOLCHAIN/'bin/lean'), 'R6AuditControls.lean', '-o', 'R6AuditControls.olean'], cwd=ctl, env=env,
        stdout=subprocess.DEVNULL)
    for c in range(1, 7):
        with open(ctl/f'c{c}.ndjson', 'wb') as out:
            run([str(EXPORTER), 'R6AuditControls', '--', f'R6Audit.c{c}_local', f'R6Audit.c{c}_whole'], cwd=ctl, stdout=out, env=env)
    mutate_nat_rec(ctl/'c2.ndjson', ctl/'c7.ndjson')
    print(json.dumps({'tool': sha(TOOL), 'controls': {f'c{c}': sha(ctl/f'c{c}.ndjson') for c in range(1, 8)}}, indent=1))


def mutate_nat_rec(src, dst):
    """C7: C2's export with `Nat.rec`'s first rule's `nfields` changed from 0 to 1 (the review's mutation)."""
    lines = src.read_text().splitlines()
    names = {}
    for l in lines[1:]:
        o = json.loads(l)
        if 'in' in o and 'str' in o: names[o['in']] = (o['str']['pre'], o['str']['str'])
    def full(i):
        parts = []
        while i: pre, s = names[i]; parts.append(s); i = pre
        return '.'.join(reversed(parts))
    done = 0
    for k, l in enumerate(lines):
        o = json.loads(l)
        if 'inductive' in o:
            for rec in o['inductive']['recs']:
                if full(rec['name']) == 'Nat.rec' and rec['rules'][0]['nfields'] == 0:
                    rec['rules'][0]['nfields'] = 1; done += 1
            if done: lines[k] = json.dumps(o, separators=(',', ':')); break
    assert done == 1, done
    dst.write_text('\n'.join(lines) + '\n')


def audit_one(export, local, whole, residual, force=False, synthetic=False):
    with tempfile.TemporaryDirectory(prefix='r6-qual-audit-') as tmp:
        tmp = Path(tmp)
        if residual is not None: (tmp/'residual.txt').write_text(residual + '\n')
        flags = (['--force-abstraction'] if force else []) + (['--synthetic'] if synthetic else [])
        cmd = [str(TOOL), *flags, str(export), local, whole, '-' if residual is None else str(tmp/'residual.txt'), str(tmp/'report.json')]
        proc = subprocess.run(cmd, capture_output=True, text=True, env={'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(TOOLCHAIN)})
        if not (tmp/'report.json').exists():
            return {'error': (proc.stdout + proc.stderr)[-2000:], 'exit': proc.returncode}
        return json.loads((tmp/'report.json').read_text())


# Frozen expectations. Each returns the list of unmet ones.
def names(section): return [h['name'] for h in section.get('hypotheses', [])]
def ok(p): return bool(p and p.get('ok'))
def cls(a, t): return a.get(t, {}).get('classification')
def check(pairs): return [m for m, bad in pairs if bad]

EXPECT = {
    1: lambda r, a: check([
        ('Check 1 must report h', 'h' not in names(a['local'])),
        ('Check 2 must not be established', a['check2']['established']),
        ('the whole must reach h through parameter 2', not any(h['name'] == 'h' and h['path'][:1] == ['parameter 2 of R6Audit.c1_local'] for h in a['whole']['hypotheses']))]),
    2: lambda r, a: check([
        ('Check 2 must be established, kernel-checked', not a['check2']['established']),
        ('C2 GATE: unused hypotheses reported, so Check 1 cannot tell use from collection', bool({'hu1', 'hu2', 'hu3'} & set(names(a['local']))))]),
    3: lambda r, a: check([
        ('Check 2 must be established directly', not (ok(a['check2']['direct']) and a['check2']['established'])),
        ('the abstraction must succeed with a checked specialization', not (ok(a['check2']['abstraction']) and ok(a['check2']['specialization_atoms']))),
        ('the product must be the one atom', a['check2']['atoms'] != ['x * y'])]),
    4: lambda r, a: check([
        ('Check 1 must report h locally', 'h' not in names(a['local'])),
        ('the whole must name hpq through parameter 2', not any(h['name'] == 'hpq' and h['path'][:1] == ['parameter 2 of R6Audit.c4_local'] for h in a['whole']['hypotheses'])),
        ('the whole must not name hextra', 'hextra' in names(a['whole'])),
        ('local and whole must agree', cls(a, 'local') != cls(a, 'whole'))]),
    5: lambda r, a: check([
        ('Check 1 must report h through v', not any(h['name'] == 'h' and h['path'] == ['v'] for h in a['local']['hypotheses'])),
        ('the whole must reach h through parameter 0', not any(h['name'] == 'h' and h['path'][:1] == ['parameter 0 of R6Audit.c5_local'] for h in a['whole']['hypotheses'])),
        ('the definition of v must be dropped and restored by a checked specialization', not (a['check2']['definitions_dropped'] == ['v'] and ok(a['check2']['specialization_definitions']))),
        ('Check 2 must be established against the original, definitions retained', not a['check2']['established'])]),
    6: lambda r, a: check([
        ('the original must be proved directly, kernel-checked', not (ok(a['check2']['direct']) and a['check2']['established'])),
        ('the forced abstraction must not be established', ok(a['check2']['abstraction'])),
        ('the result must count as sufficient', cls(a, 'local') == 'sufficiency_not_established'),
        ('no mismatch may be reported', 'mismatch' in json.dumps(a['check2']))]),
    7: lambda r, a: check([('the mutated export must be refused', 'refused' not in r)]),
    8: lambda r, a: check([
        ('binding must report the mismatch', a.get('binding') != 'residual_mismatch'),
        ('no sufficiency classification may be made, local', cls(a, 'local') != 'unbound_residual_mismatch'),
        ('no sufficiency classification may be made, whole', cls(a, 'whole') != 'unbound_residual_mismatch')]),
    9: lambda r, a: check([
        ('binding must match', a.get('binding') != 'matches_residual'),
        ('the classification must be made', cls(a, 'local') in (None, 'unbound_residual_mismatch', 'sufficiency_not_established'))]),
}
# control -> (export, local/whole stem, residual (None: synthetic), force abstraction)
RUNS = {1: ('c1', 'c1', None, False), 2: ('c2', 'c2', None, False), 3: ('c3', 'c3', None, True), 4: ('c4', 'c4', None, False),
        5: ('c5', 'c5', None, False), 6: ('c6', 'c6', None, True), 7: ('c7', 'c2', None, False),
        8: ('c2', 'c2', '0 < 1 * (x - y) + 2 * (y + 1 - x)', False), 9: ('c2', 'c2', C2_RESIDUAL, False)}


def controls(args):
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    results, failures = {}, {}
    for c, (exp, stem, residual, force) in RUNS.items():
        r = audit_one(BUILD/f'controls/{exp}.ndjson', f'R6Audit.{stem}_local', f'R6Audit.{stem}_whole', residual,
                      force=force, synthetic=residual is None)
        a = r.get('audit', {})
        failures[f'C{c}'] = EXPECT[c](r, a) if ('local' in a or c == 7) else ['no report: ' + json.dumps(r)[:300]]
        results[f'C{c}'] = r
        print(f'C{c}:', 'as expected' if not failures[f'C{c}'] else failures[f'C{c}'], flush=True)
    passed = not any(failures.values())
    out.write_text(json.dumps({'passed': passed, 'failures': failures, 'results': results, 'tool_sha256': sha(TOOL),
                               'sources_sha256': {str(p.relative_to(REPO)): sha(p) for p in SOURCES},
                               'scope': 'synthetic controls only; no R6 export read'}, indent=1) + '\n')
    print(json.dumps({'passed': passed}))
    return 0 if passed else 1


def selection():
    """The 48 slots, their targets and retained residual goals, and every consumed artifact's digest (checked against the seal)."""
    sys.path.insert(0, str(R6)); sys.dont_write_bytecode = True
    import site_task
    analysis = json.loads(ANALYSIS.read_text())
    proved = sorted(k for k, s in analysis['per_slot'].items() if s['whole'])
    assert len(proved) == 48, len(proved)
    slots = {}
    for key in proved:
        site, draw = key.split('/'); run_dir = R6/f"cohort-live-v9/{site.removeprefix('bracket-')}-draw{draw}"
        seal = json.loads((run_dir/'seal.json').read_text())['retained_sha256']
        digests = {f: sha(run_dir/f) for f in ('solution.ndjson.gz', 'events.ndjson')}
        for f, d in digests.items():
            if d != seal[f]: raise SystemExit(f'seal mismatch: {run_dir/f}')
        rows = [json.loads(l) for l in (run_dir/'events.ndjson').read_text().splitlines()]
        goals = [r['payload'].get('data', r['payload']).get('goal') for r in rows if r['event'] == 'residual_started']
        assert len(goals) == 1, (key, len(goals))
        task = site_task.get(site)
        slots[key] = {'run': str(run_dir.relative_to(REPO)), 'local': task.local, 'whole': task.whole, 'residual_goal': goals[0],
                      'seal_sha256': sha(run_dir/'seal.json'), **{f'{f}_sha256': d for f, d in digests.items()}}
    return slots


def lock_record():
    return {'schema_version': 'r6-qualification-audit-lock-1', 'tool_sha256': sha(TOOL),
            'toolchain': 'leanprover/lean4:v4.32.2', 'controls_toolchain': 'leanprover/lean4:v4.32.0',
            'sources_sha256': {str(p.relative_to(REPO)): sha(p) for p in SOURCES},
            'controls_sha256': {f'c{c}': sha(BUILD/f'controls/c{c}.ndjson') for c in range(1, 8)},
            'exporter_sha256': sha(EXPORTER), 'analysis': str(ANALYSIS.relative_to(REPO)), 'analysis_sha256': sha(ANALYSIS),
            'selection': selection()}


def lock(_):
    if LOCK.exists(): raise SystemExit(f'refusing to overwrite {LOCK}')
    LOCK.write_text(json.dumps(lock_record(), indent=1, sort_keys=True) + '\n')
    print(sha(LOCK))


def verify_lock():
    if not LOCK.exists(): raise SystemExit('audit refused: no lock (the implementation review comes first)')
    frozen = json.loads(LOCK.read_text())
    if frozen != lock_record(): raise SystemExit('audit refused: the lock does not verify')
    return frozen


def verify_live_evaluation():
    run([sys.executable, str(R6/'reviews/2026-09-29/live_evaluation_lock_v3.py'), 'verify'], stdout=subprocess.DEVNULL)


def audit(args):
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    frozen = verify_lock(); verify_live_evaluation()
    slots = {}
    for key, s in sorted(frozen['selection'].items()):
        with tempfile.TemporaryDirectory(prefix='r6-qual-export-') as tmp:
            export = Path(tmp)/'solution.ndjson'
            raw = (REPO/s['run']/'solution.ndjson.gz').read_bytes()
            if hashlib.sha256(raw).hexdigest() != s['solution.ndjson.gz_sha256']: raise SystemExit(f'export changed: {key}')
            export.write_bytes(gzip.decompress(raw))
            slots[key] = audit_one(export, s['local'], s['whole'], s['residual_goal'])
        print(key, slots[key].get('audit', {}).get('local', {}).get('classification', slots[key].get('error', '')[:80]), flush=True)
    verify_live_evaluation(); verify_lock()   # the selection, the seals and every consumed artifact, recomputed after
    out.write_text(json.dumps({'slots': slots, 'lock_sha256': sha(LOCK),
                               'scope': "R6's 48 whole-validated proofs, read from their sealed exports; nothing rewritten"}, indent=1) + '\n')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    sub.add_parser('build').set_defaults(f=build)
    c = sub.add_parser('controls'); c.add_argument('--output', required=True); c.set_defaults(f=controls)
    sub.add_parser('lock').set_defaults(f=lock)
    a = sub.add_parser('audit'); a.add_argument('--output', required=True); a.set_defaults(f=audit)
    args = p.parse_args()
    sys.exit(args.f(args) or 0)


if __name__ == '__main__':
    main()

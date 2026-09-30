#!/usr/bin/env python3
"""Driver for the R6 qualification-1 audit (`experiments/r6/R6-QUALIFICATION-1-AUDIT-PROPOSAL.md`, revision 2).

    build              build the tool (Lean 4.32.0) and the six controls, and export the controls with R6's pinned exporter
    controls --output  run the tool on the controls and assert their frozen expectations
    lock               freeze the tool, controls and driver (only after the implementation review)
    audit --output     audit R6's 48 proof exports; refuses unless the lock verifies

Offline: no provider, credential, episode or spending. R6's evidence is only read; every export is checked against its run's
seal before it is read, and `live-evaluation-v3` is verified before and after the audit.
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
LEAN = Path.home()/'build/elan/toolchains/leanprover--lean4---v4.32.0/bin'
EXPORTER = R6/'.cache/exporter/.lake/build/bin/lean4export'
TOOL = BUILD/'.lake/build/bin/r6-qualification-audit'
LOCK = R6/'policies/qualification-audit-v1.sha256.json'
ANALYSIS = R6/'reviews/2026-09-29/R6-014-BLOCK2-ANALYSIS.json'
SOURCES = [HERE/'Audit.lean', HERE/'make_controls.py', HERE/'R6AuditControls.lean', HERE/'R6AuditControls.provenance.json',
           Path(__file__).resolve(), R6/'vendor/lean4export/Export/Parse.lean', R6/'vendor/lean4export/Export.lean']


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
    (BUILD/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
    run([str(LEAN/'lake'), 'build', 'r6-qualification-audit'], cwd=BUILD)
    run([sys.executable, str(HERE/'make_controls.py')])
    ctl = BUILD/'controls'; ctl.mkdir()
    shutil.copyfile(HERE/'R6AuditControls.lean', ctl/'R6AuditControls.lean')
    lean_path = f"{REPO/'lean-bridge/.lake/build/lib/lean'}:{ctl}"
    run([str(LEAN/'lean'), 'R6AuditControls.lean', '-o', 'R6AuditControls.olean'], cwd=ctl, env={'LEAN_PATH': lean_path, 'PATH': '/usr/bin:/bin'},
        stdout=subprocess.DEVNULL)
    for c in range(1, 7):
        with open(ctl/f'c{c}.ndjson', 'wb') as out:
            run([str(EXPORTER), 'R6AuditControls', '--', f'R6Audit.c{c}_local', f'R6Audit.c{c}_whole'], cwd=ctl, stdout=out,
                env={'LEAN_PATH': lean_path, 'PATH': '/usr/bin:/bin'})
    print(json.dumps({'tool': sha(TOOL), 'controls': [sha(ctl/f'c{c}.ndjson') for c in range(1, 7)]}, indent=1))


def audit_one(export, local, whole, residual, force=False):
    with tempfile.TemporaryDirectory(prefix='r6-qual-audit-') as tmp:
        tmp = Path(tmp); (tmp/'residual.txt').write_text(residual + '\n')
        cmd = [str(TOOL)] + (['--force-abstraction'] if force else []) + [str(export), local, whole, str(tmp/'residual.txt'), str(tmp/'report.json')]
        proc = subprocess.run(cmd, capture_output=True, text=True, env={'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(LEAN.parent)})
        if not (tmp/'report.json').exists():
            return {'error': (proc.stdout + proc.stderr)[-2000:], 'exit': proc.returncode}
        return json.loads((tmp/'report.json').read_text())


# The frozen expectations for C1-C6 (proposal revision 2). Each returns a list of failures.
def names(section): return [h['name'] for h in section.get('hypotheses', [])]
def ok(p): return bool(p and p.get('ok'))

EXPECT = {
    1: lambda a: [m for m, bad in [
        ('Check 1 must report h', 'h' not in names(a['local'])),
        ('Check 2 must not be established', ok(a['check2']['original']) or (ok(a['check2']['abstraction']) and ok(a['check2']['specialization']))),
        ('whole must reach h through the reference', not any(h['name'] == 'h' and h['path'][:1] == ['parameter 2 of R6Audit.c1_local'] for h in a['whole']['hypotheses']))] if bad],
    2: lambda a: [m for m, bad in [
        ('Check 2 must succeed, kernel-checked', not ok(a['check2']['original'])),
        ('C2 GATE: unused hypotheses reported, so Check 1 cannot tell use from collection', bool({'hu1', 'hu2', 'hu3'} & set(names(a['local']))))] if bad],
    3: lambda a: [m for m, bad in [
        ('Check 2 must succeed directly', not ok(a['check2']['original'])),
        ('Check 2 must succeed through abstraction with checked specialization', not (ok(a['check2']['abstraction']) and ok(a['check2']['specialization']))),
        ('the product must be the one atom', a['check2']['atoms'] != ['x * y'])] if bad],
    4: lambda a: [m for m, bad in [
        ('Check 1 must report h locally', 'h' not in names(a['local'])),
        ('the whole must name hpq through parameter 2', not any(h['name'] == 'hpq' and h['path'][:1] == ['parameter 2 of R6Audit.c4_local'] for h in a['whole']['hypotheses'])),
        ('the whole must not name hextra', 'hextra' in names(a['whole'])),
        ('local and whole must agree', a['local']['classification'] != a['whole']['classification'])] if bad],
    5: lambda a: [m for m, bad in [
        ('Check 1 must report h through v', not any(h['name'] == 'h' and h['path'] == ['v'] for h in a['local']['hypotheses'])),
        ('the whole must reach h through parameter 0', not any(h['name'] == 'h' and h['path'][:1] == ['parameter 0 of R6Audit.c5_local'] for h in a['whole']['hypotheses']))] if bad],
    6: lambda a: [m for m, bad in [
        ('the original must succeed, kernel-checked', not ok(a['check2']['original'])),
        ('the forced abstraction must not be established', ok(a['check2']['abstraction'])),
        ('the result must count as sufficient', a['local']['classification'] == 'sufficiency_not_established'),
        ('no mismatch may be reported', 'mismatch' in json.dumps(a))] if bad],
}
FORCE = {3, 6}


def controls(args):
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    results, failures = {}, {}
    for c in range(1, 7):
        r = audit_one(BUILD/f'controls/c{c}.ndjson', f'R6Audit.c{c}_local', f'R6Audit.c{c}_whole',
                      '(no retained residual goal for a synthetic control)', force=c in FORCE)
        a = r.get('audit', {})
        failures[f'C{c}'] = EXPECT[c](a) if 'local' in a else ['no report: ' + json.dumps(r)[:300]]
        results[f'C{c}'] = r
        print(f'C{c}:', 'as expected' if not failures[f'C{c}'] else failures[f'C{c}'])
    passed = not any(failures.values())
    out.write_text(json.dumps({'passed': passed, 'failures': failures, 'results': results,
                               'tool_sha256': sha(TOOL), 'sources_sha256': {str(p.relative_to(REPO)): sha(p) for p in SOURCES},
                               'scope': 'synthetic controls only; no R6 export read'}, indent=1) + '\n')
    print(json.dumps({'passed': passed}))
    return 0 if passed else 1


def lock_record():
    return {'schema_version': 'r6-qualification-audit-lock-1', 'tool_sha256': sha(TOOL),
            'sources_sha256': {str(p.relative_to(REPO)): sha(p) for p in SOURCES},
            'controls_sha256': {f'c{c}': sha(BUILD/f'controls/c{c}.ndjson') for c in range(1, 7)},
            'exporter_sha256': sha(EXPORTER), 'lean': 'leanprover/lean4:v4.32.0'}


def lock(_):
    if LOCK.exists(): raise SystemExit(f'refusing to overwrite {LOCK}')
    LOCK.write_text(json.dumps(lock_record(), indent=1, sort_keys=True) + '\n')
    print(sha(LOCK))


def verify_lock():
    if not LOCK.exists(): raise SystemExit('audit refused: no lock (the implementation review comes first)')
    if json.loads(LOCK.read_text()) != lock_record(): raise SystemExit('audit refused: the lock does not verify')


def verify_live_evaluation():
    run([sys.executable, str(R6/'reviews/2026-09-29/live_evaluation_lock_v3.py'), 'verify'], stdout=subprocess.DEVNULL)


def audit(args):
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    verify_lock(); verify_live_evaluation()
    sys.path.insert(0, str(R6)); sys.dont_write_bytecode = True
    import site_task
    analysis = json.loads(ANALYSIS.read_text())
    proved = sorted(k for k, s in analysis['per_slot'].items() if s['whole'])
    assert len(proved) == 48, len(proved)
    slots = {}
    for key in proved:
        site, draw = key.split('/'); run_dir = R6/f"cohort-live-v9/{site.removeprefix('bracket-')}-draw{draw}"
        seal = json.loads((run_dir/'seal.json').read_text())['retained_sha256']
        for f in ('solution.ndjson.gz', 'events.ndjson'):
            if sha(run_dir/f) != seal[f]: raise SystemExit(f'seal mismatch: {run_dir/f}')
        rows = [json.loads(l) for l in (run_dir/'events.ndjson').read_text().splitlines()]
        goals = [r['payload'].get('data', r['payload']).get('goal') for r in rows if r['event'] == 'residual_started']
        assert len(goals) == 1, (key, len(goals))
        task = site_task.get(site)
        with tempfile.TemporaryDirectory(prefix='r6-qual-export-') as tmp:
            export = Path(tmp)/'solution.ndjson'
            export.write_bytes(gzip.decompress((run_dir/'solution.ndjson.gz').read_bytes()))
            slots[key] = audit_one(export, task.local, task.whole, goals[0])
        print(key, slots[key].get('audit', {}).get('local', {}).get('classification', slots[key].get('error', '')[:80]), flush=True)
    verify_live_evaluation(); verify_lock()
    out.write_text(json.dumps({'slots': slots, 'lock_sha256': sha(LOCK), 'analysis_sha256': sha(ANALYSIS),
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

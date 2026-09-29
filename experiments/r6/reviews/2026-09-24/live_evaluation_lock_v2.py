#!/usr/bin/env python3
"""The R6-014 live-evaluation lock, version 2 (`policies/live-evaluation-v2.sha256.json`): amendment 1, post-collection, after its approval
(`reviews/2026-09-24/R6-014-AMENDMENT-1-REVIEW.md`, reviewed at 10c53c34). Version 1 (`live_evaluation_lock.py`, `live-evaluation-v1`) is
retained unchanged; version 2 differs only in evaluating with the amended auditor and its controls, and in binding version 1, the
amendment's decision and its review as records.

The version 1 description follows.

The R6-014 live-evaluation lock (`policies/live-evaluation-v1.sha256.json`), written once after the revision 4 approval
(`reviews/2026-09-23/R6-014-V4-REVIEW.md`, reviewed at 6e993510) and before any signature.

It freezes what will evaluate a live collection:
* `reviewed`: the evaluation sources, each byte-identical to the approved commit: the cohort v9 auditor and its controls (and the R6-013
  control population and auditor they import), the deterministic-arm auditor and its controls, the live-shaped fixture generator, the
  boundary-hook precondition, the operator-scan contract (the frozen scanner and its scanning module) and the frozen analysis;
* `import_closure`: every repository file those modules load, recorded at freeze, so that a changed dependency outside the reviewed list
  is detected too;
* `records`: the locks and reviewed records the evaluation relies on: the cohort v9, analysis v3, deterministic-arm and site-harness v4
  locks, the reviewed library inventory, the live fixture's manifest and the approving review.

The production policy is deliberately not frozen here: signing rewrites it, and the auditor binds it to its checkpoint and history.
`verify` recomputes every digest and is run before any live evaluation; any mismatch refuses. Read-only apart from the one exclusive write.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

R6 = Path(__file__).resolve().parents[2]; REPO = R6.parents[1]
LOCK = R6/'policies/live-evaluation-v2.sha256.json'
APPROVED_COMMIT = '10c53c34'
APPROVAL = 'experiments/r6/reviews/2026-09-24/R6-014-AMENDMENT-1-REVIEW.md'
REVIEWED = ('experiments/r6/reviews/2026-09-24/cohort_v9_audit_amended.py', 'experiments/r6/reviews/2026-09-24/cohort_v9_audit_amended_controls.py',
            'experiments/r6/reviews/2026-09-23/cohort_v9_audit.py', 'experiments/r6/reviews/2026-09-23/cohort_v9_audit_controls.py',
            'experiments/r6/reviews/2026-09-22/cohort_v6_audit.py', 'experiments/r6/reviews/2026-09-22/cohort_v6_audit_controls.py',
            'experiments/r6/reviews/2026-09-23/deterministic_audit.py', 'experiments/r6/reviews/2026-09-23/deterministic_audit_controls.py',
            'experiments/r6/reviews/2026-09-23/live_shape_v9.py', 'experiments/r6/reviews/2026-09-23/escape_hook_precondition.py',
            'experiments/r6/reviews/2026-09-13/operator_disclosure_scan.py', 'experiments/r6/publication.py',
            'experiments/r6/analysis_r6.py', 'experiments/r6/test_analysis_r6.py')
RECORDS = ('experiments/r6/policies/cohort-harness-v9.sha256.json', 'experiments/r6/policies/analysis-v3.sha256.json',
           'experiments/r6/policies/site-broker-harness-v1.sha256.json', 'experiments/r6/policies/site-broker-v1.json',
           'experiments/r6/policies/site-harness-v4.sha256.json', 'experiments/r6/reviews/2026-09-23/R6-013-V3-LIBRARY-INVENTORY.json',
           'experiments/r6/fixtures/r6-014-v3-live-revisions/FIXTURE.json', 'experiments/r6/policies/live-evaluation-v1.sha256.json',
           'experiments/r6/reviews/2026-09-24/R6-014-AMENDMENT-1-DECISION.md', 'experiments/r6/reviews/2026-09-24/R6-014-BLOCK1-LIVE-AUDIT-REJECTED.json', APPROVAL)
# Loaded in a fresh interpreter to find the import closure; none of these runs anything at import.
LOADS = ('experiments/r6/reviews/2026-09-24/cohort_v9_audit_amended_controls.py', 'experiments/r6/reviews/2026-09-23/deterministic_audit_controls.py',
         'experiments/r6/reviews/2026-09-23/live_shape_v9.py', 'experiments/r6/reviews/2026-09-13/operator_disclosure_scan.py', 'experiments/r6/analysis_r6.py')
CLOSURE = r'''
import importlib.util, json, sys
from pathlib import Path
repo = Path(sys.argv[1]); sys.path.insert(0, str(repo/'experiments/r6')); sys.dont_write_bytecode = True
for i, path in enumerate(sys.argv[2:]):
    spec = importlib.util.spec_from_file_location(f'_live_evaluation_{i}', repo/path); module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
files = set()
for m in list(sys.modules.values()):
    f = getattr(m, '__file__', None)
    if f and Path(f).resolve().is_relative_to(repo) and '.lake' not in Path(f).parts: files.add(str(Path(f).resolve().relative_to(repo)))
print(json.dumps(sorted(files)))
'''


def sha(path): return hashlib.sha256((REPO/path).read_bytes()).hexdigest()


def closure():
    out = subprocess.run([sys.executable, '-c', CLOSURE, str(REPO), *LOADS], capture_output=True, text=True, check=True, cwd=R6)
    return json.loads(out.stdout.strip().splitlines()[-1])


def record():
    at_commit = {p: hashlib.sha256(subprocess.run(['git', '-C', str(REPO), 'show', f'{APPROVED_COMMIT}:{p}'], capture_output=True, check=True).stdout).hexdigest()
                 for p in REVIEWED if p != APPROVAL}
    current = {p: sha(p) for p in REVIEWED}
    differing = [p for p in REVIEWED if current[p] != at_commit[p]]
    if differing: raise SystemExit('reviewed sources differ from the approved commit: '+', '.join(differing))
    return {'schema_version': 'r6-live-evaluation-lock-2', 'supersedes': 'experiments/r6/policies/live-evaluation-v1.sha256.json', 'approved_commit': APPROVED_COMMIT, 'approval': APPROVAL,
            'reviewed': current, 'import_closure': {p: sha(p) for p in closure()}, 'records': {p: sha(p) for p in RECORDS},
            'scope': 'frozen after approval and before any signature; the production policy is not frozen here (signing rewrites it); '
                     'verify before any live evaluation'}


def verify():
    lock = json.loads(LOCK.read_bytes())
    wanted = {**lock['reviewed'], **lock['import_closure'], **lock['records']}
    differing = sorted(p for p, h in wanted.items() if not (REPO/p).is_file() or sha(p) != h)
    extra = sorted(set(closure())-set(lock['import_closure']))
    if differing or extra: raise SystemExit(f'live evaluation refused: changed {differing}, newly imported {extra}')
    return {'verified': len(wanted), 'lock_sha256': hashlib.sha256(LOCK.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('freeze', 'verify'))
    args = parser.parse_args()
    if args.command == 'freeze':
        value = record()
        with LOCK.open('x') as f: f.write(json.dumps(value, indent=2, sort_keys=True)+'\n')
        print(json.dumps({'lock': str(LOCK.relative_to(REPO)), 'sha256': hashlib.sha256(LOCK.read_bytes()).hexdigest(),
                          'reviewed': len(value['reviewed']), 'import_closure': len(value['import_closure']), 'records': len(value['records'])}, indent=1))
    else: print(json.dumps(verify(), indent=1))


if __name__ == '__main__':
    main()

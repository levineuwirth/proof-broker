#!/usr/bin/env python3
"""Independent R6-013 audit revision 3 follow-up; copies only, cached tool builds invoked."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('v2_review_for_v3', HERE/'cohort_v6_v2_review_probes.py')
previous = importlib.util.module_from_spec(spec); spec.loader.exec_module(previous)
c = previous.c; ROOT = previous.ROOT
CASES = (*previous.ADDITIONAL, 'proof_reconstruction_helper_changed', 'library_pair_removed_in_one_run',
         'library_pair_added_to_every_assembly', 'challenge_path_inside_recorded_root')

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory_check():
    p = HERE/'R6-013-V3-LIBRARY-INVENTORY.json'; data = json.loads(p.read_bytes())
    assert digest(p) == c.audit.LIBRARY_INVENTORY_SHA256
    assert data['program_sha256'] == digest(HERE/'library_inventory.py')
    anchor = data['anchor_commit']
    # Run git at repository root, so pathspecs do not depend on a subdirectory cwd.
    repo = ROOT.parents[1]
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', anchor, '--', 'experiments/r6/cohort-runs-v6'], cwd=repo, text=True).splitlines()
    counts = {}
    for path in paths:
        if not path.endswith('/command.json') or '/stages/' not in path or '/proposal-1/' in path: continue
        stage = path.split('/stages/')[1].split('/')[0]
        argv = json.loads(subprocess.check_output(['git', 'show', anchor+':'+path], cwd=repo))['argv']
        pairs = [[argv[i+1], argv[i+2]] for i,x in enumerate(argv) if x == '--ro-bind' and argv[i+1].startswith('/usr/lib/')]
        assert pairs == data['stages'][stage], path
        counts[stage] = counts.get(stage, 0)+1
    assert counts == data['runs_per_stage'] and sum(counts.values()) == 108
    with tempfile.TemporaryDirectory(prefix='r6-inventory-review-') as tmp:
        altered = Path(tmp)/'inventory.json'; altered.write_bytes(p.read_bytes())
        with patch.object(c.audit, 'LIBRARY_INVENTORY', altered):
            assert c.audit.library_inventory()
            data['stages']['reconstruct'].append(['/usr/lib/review.so', '/usr/lib/review.so'])
            altered.write_text(json.dumps(data))
            try: c.audit.library_inventory()
            except ValueError as error: assert 'differs from the reviewed one' in str(error)
            else: raise AssertionError('changed library inventory accepted')
    return {'anchor_commit': anchor, 'inventory_sha256': digest(p), 'commands_checked': sum(counts.values()),
            'runs_per_stage': counts, 'changed_inventory_rejected': True}

def main():
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('--output', type=Path, required=True); args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite')
    inventory = inventory_check(); results = {}
    for name in CASES:
        with tempfile.TemporaryDirectory(prefix='r6-013-v3-review-') as tmp:
            tmp = Path(tmp); paths = {k: tmp/k for k in ('runs','ledgers','representability','v4','v5')}
            sources = {'runs': ROOT/c.audit.RUNS, 'ledgers': ROOT/'ledgers/campaigns', 'representability': ROOT/c.audit.REPRESENTABILITY,
                       'v4': ROOT/c.audit.HISTORY_V4['runs'], 'v5': ROOT/c.audit.HISTORY_V5['runs']}
            for k,p in sources.items(): shutil.copytree(p, paths[k])
            baseline = c.run_audit(paths); assert baseline['accepted'] is True and baseline['case_count'] == 665, baseline
            if name in previous.ADDITIONAL: previous.mutate(name, paths)
            else: c.mutate(name, paths)
            observed = c.run_audit(paths)
            if name == 'replay_challenge_unverified_location': assert observed['accepted'] is True and observed['case_count'] == 665, observed
            else: assert observed['accepted'] is False and observed['rejected_case'] == c.EXPECTED[name], observed
            results[name] = {'unmutated_copy_accepted': True, **observed}; print(name, json.dumps(observed), flush=True)
    assert tuple(results) == CASES
    args.output.write_text(json.dumps({'complete': True, 'expected_cases': list(CASES), 'results': results, 'inventory': inventory,
        'program_sha256': digest(Path(__file__)), 'prior_probe_program_sha256': digest(HERE/'cohort_v6_v2_review_probes.py'),
        'auditor_sha256': digest(ROOT/'reviews/2026-09-22/cohort_v6_audit.py'),
        'control_program_sha256': digest(ROOT/'reviews/2026-09-22/cohort_v6_audit_controls.py'),
        'scope': 'fresh copies; baseline 665 before every mutation; cached tool builds; no native episodes, proof replays, credentials or provider calls'}, indent=2)+'\n')

if __name__ == '__main__': main()

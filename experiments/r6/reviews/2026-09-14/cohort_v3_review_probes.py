#!/usr/bin/env python3
"""Independent copied-artifact probes of 7240ae5; no launch, provider, or credential.

Accepted corruptions are review findings, not passing conformance checks.
Every mutation starts from a separately accepted copy and uses the production
finalizer, so scan, terminal receipt and seal describe the changed bytes.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
spec = importlib.util.spec_from_file_location('cohort_v3_probe_helpers', Path(__file__).with_name('cohort_audit_controls.py'))
helper = importlib.util.module_from_spec(spec); spec.loader.exec_module(helper)
J, W = helper.J, helper.W
CASES = ('runtime_source_and_role_foreign', 'interpreter_source_and_role_foreign',
         'nonzero_assembly_exit_coherent', 'nonzero_whole_validation_exit_coherent',
         'extra_readonly_host_mount')


def mutate(name, run, rows):
    if name in ('runtime_source_and_role_foreign', 'interpreter_source_and_role_foreign', 'extra_readonly_host_mount'):
        cmd_path = run/'stages/proposal-1/command.json'; cmd = J(cmd_path); argv = cmd['argv']
        roles = J(run/'provenance/roles.json')
        if name == 'extra_readonly_host_mount':
            # Not executed: the command would expose the entire repository to the actor.
            # Existing expected mounts, writable-mount count and every role stay intact.
            assert '/extra-reference' not in argv
            source = str(ROOT.parents[1]); argv[1:1] = ['--ro-bind', source, '/extra-reference']
            detail = {'added_readonly_mount': [source, '/extra-reference']}
        else:
            key = 'runtime_path' if name.startswith('runtime') else 'python'
            old = roles[key]; new = '/tmp/r6-009-v3-unapproved/'+('stdlib' if key == 'runtime_path' else 'python3.14')
            hits = [i for i, v in enumerate(argv) if v == old and i > 0 and argv[i-1] == '--ro-bind']
            assert len(hits) == 1 and old != new
            argv[hits[0]] = new; roles[key] = new; W(run/'provenance/roles.json', roles)
            detail = {'role': key, 'old': old, 'new': new, 'runtime_pin_unchanged': True,
                      'python_runtime_inventory_unchanged': True, 'binary_inventory_unchanged': True}
        W(cmd_path, cmd)
        return detail
    stage = {'nonzero_assembly_exit_coherent': 'assembly', 'nonzero_whole_validation_exit_coherent': 'validation-whole'}[name]
    path = run/'stages'/stage/(stage+'.process.json'); record = J(path)
    assert record['exit_code'] == 0
    record['exit_code'] = 7; W(path, record)
    event = helper.event(rows, 'stage_finished', stage); event.clear(); event.update(record)
    return {'stage': stage, 'recorded_exit_code': 7, 'finish_receipt_equals_process_record': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scratch', type=Path, required=True); parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); assert not args.output.exists()
    result = {'complete': False, 'reviewed_commit': '7240ae5', 'expected_cases': list(CASES), 'results': {},
              'live_model_calls': 0, 'real_credentials_read': 0, 'native_episodes_rerun': 0,
              'scope': 'temporary copied artifacts and normal finalization; no changed command is executed',
              'auditor_sha256': helper.r6.sha(Path(__file__).with_name('cohort_audit.py')),
              'program_sha256': helper.r6.sha(Path(__file__))}
    W(args.output, result)
    for name in CASES:
        with tempfile.TemporaryDirectory(prefix=name+'-', dir=args.scratch) as temp:
            root, ledgers = Path(temp)/'runs', Path(temp)/'ledgers'
            shutil.copytree(ROOT/'cohort-runs-v3', root); shutil.copytree(ROOT/'ledgers/campaigns', ledgers)
            baseline = helper.run_audit(root, ledgers); assert baseline == {'accepted': True, 'case_count': 197}, baseline
            details = {}
            helper.refinalize(root/helper.LAST, lambda run, rows: details.update(mutate(name, run, rows)))
            observed = helper.run_audit(root, ledgers)
            result['results'][name] = {'unmutated_copy': baseline, 'mutated_copy': observed, 'detail': details}
            W(args.output, result); print(name, observed, flush=True)
    assert tuple(result['results']) == CASES
    result['complete'] = True; W(args.output, result)


if __name__ == '__main__': main()

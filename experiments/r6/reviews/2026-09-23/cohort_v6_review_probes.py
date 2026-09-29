#!/usr/bin/env python3
"""Independent review probes; temporary copies and production finalization only."""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('v6_controls_review', ROOT/'reviews/2026-09-22/cohort_v6_audit_controls.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
CASES = ('refused_dispatch_certificate', 'refused_dispatch_final_ir', 'refused_verification_started_certificate',
         'coherent_wrong_success_closer', 'refused_reconstruction_foreign_packet', 'historical_wrong_kernel_target')


def mutate(name, paths):
    if name.startswith('refused_dispatch') or name == 'refused_verification_started_certificate':
        def change(run, rows):
            event = 'certificate_verification_started' if name == 'refused_verification_started_certificate' else 'dispatch_received'
            key = 'final_ir' if name == 'refused_dispatch_final_ir' else 'certificate'
            data = c.child(rows, event)
            assert data[key] != {'review_probe': 'different_evidence'}
            data[key] = {'review_probe': 'different_evidence'}
        c.refinalize(paths['runs']/c.REF, change)
    elif name == 'coherent_wrong_success_closer':
        def change(run, rows):
            for event in ('closer_selected', 'reconstruction_finished'):
                data = c.child(rows, event)
                assert data['closer'] == 'term_mode_int'
                data['closer'] = 'term_mode_nat'
            c.rebind_verdict(run, rows, lambda v: v.__setitem__('closer', 'term_mode_nat'))
        c.refinalize(paths['runs']/c.LAST, change)
    elif name == 'refused_reconstruction_foreign_packet':
        def change(run, rows):
            def command(v):
                a = v['argv']; i = a.index('/evidence.json')
                assert a[i-2] == '--ro-bind' and '/l204-draw1/' in a[i-1]
                a[i-1] = a[i-1].replace('/l204-draw1/', '/l070-draw1/')
            c.change_json(run, 'stages/reconstruct/command.json', command)
        c.refinalize(paths['runs']/c.REF, change)
    elif name == 'historical_wrong_kernel_target':
        def change(run, rows):
            def verdict(v):
                target = v['final_validation']['local']['targets'][0]
                assert target['name'] != 'Unrelated.theorem'
                target['name'] = 'Unrelated.theorem'
            c.rebind_verdict(run, rows, verdict)
        c.reseal_history(paths['v5']/'l096-draw1', change)
    else:
        raise AssertionError(name)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite')
    results = {}
    for name in CASES:
        with tempfile.TemporaryDirectory(prefix='r6-013-review-') as tmp:
            tmp = Path(tmp)
            paths = {k: tmp/k for k in ('runs', 'ledgers', 'representability', 'v4', 'v5')}
            sources = {'runs': ROOT/c.audit.RUNS, 'ledgers': ROOT/'ledgers/campaigns',
                       'representability': ROOT/c.audit.REPRESENTABILITY,
                       'v4': ROOT/c.audit.HISTORY_V4['runs'], 'v5': ROOT/c.audit.HISTORY_V5['runs']}
            for key, src in sources.items(): shutil.copytree(src, paths[key])
            baseline = c.run_audit(paths)
            assert baseline['accepted'] is True and baseline['case_count'] == 628, baseline
            mutate(name, paths)
            observed = c.run_audit(paths)
            results[name] = {'unmutated_copy_accepted': True, **observed}
            print(name, json.dumps(observed), flush=True)
    assert tuple(results) == CASES
    args.output.write_text(json.dumps({'complete': True, 'expected_cases': list(CASES), 'results': results,
        'auditor_sha256': c.r6.sha(ROOT/'reviews/2026-09-22/cohort_v6_audit.py'),
        'program_sha256': c.r6.sha(Path(__file__)), 'native_runs': 0, 'provider_calls': 0,
        'scope': 'coherent changes on fresh copies; full 628-case audit before and after; production finalizer/sealer'}, indent=2)+'\n')


if __name__ == '__main__': main()

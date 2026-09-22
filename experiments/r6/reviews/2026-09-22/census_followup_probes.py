#!/usr/bin/env python3
"""Review probes against 0db6c9d; mutate copies only, no compilation or provider calls."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('census_audit_reviewed', HERE/'census_audit.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
CASES = ('source_binding_other_family', 'replay_wrong_solution_mount',
         'replay_command_missing', 'extra_freeze_output')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite output')
    results = {}
    for name in CASES:
        with tempfile.TemporaryDirectory(prefix='r6-010-followup-') as tmp:
            tmp = Path(tmp)
            c, f = tmp/'census', tmp/'freeze'
            shutil.copytree(audit.site_freeze.CENSUS_DIR, c)
            shutil.copytree(audit.ROOT/'census-runs/freeze-v1', f)
            baseline = audit.audit(c, f)
            assert baseline['accepted'] and baseline['case_count'] == 127
            site = f/'bracket-l069'
            if name == 'source_binding_other_family':
                for filename in ('verdict.json', 'verdict.raw.json.gz'):
                    src = f/'baseline-Bracket.threshold_unique/baseline-validation'/filename
                    dst = site/'source-binding-validation'/filename
                    assert src.read_bytes() != dst.read_bytes()
                    shutil.copyfile(src, dst)
                targets = json.loads((site/'source-binding-validation/verdict.json').read_bytes())['targets']
                assert [t['name'] for t in targets] == ['Bracket.threshold_unique']
                evidence = {'expected': 'Bracket.lift_cell', 'observed': [t['name'] for t in targets]}
            elif name == 'replay_wrong_solution_mount':
                p = site/'source-binding-validation/replay.command.json'
                command = json.loads(p.read_bytes())
                i = command['argv'].index('/solution.ndjson')
                old = command['argv'][i-1]
                assert '/bracket-l069/' in old
                command['argv'][i-1] = old.replace('/bracket-l069/', '/bracket-l099/')
                p.write_text(json.dumps(command))
                evidence = {'old': old, 'new': command['argv'][i-1]}
            elif name == 'replay_command_missing':
                p = site/'challenge-validation/replay.command.json'
                assert p.is_file()
                p.unlink()
                evidence = {'removed': str(p.relative_to(f))}
            else:
                p = site/'challenge/output/unlisted.json'
                assert not p.exists()
                p.write_text('{"unlisted":true}\n')
                evidence = {'added': str(p.relative_to(f))}
            try:
                observed = audit.audit(c, f)
                outcome = {'accepted': observed['accepted'], 'case_count': observed['case_count']}
            except audit.Rejection as rejection:
                outcome = {'accepted': False, 'rejected_case': rejection.case}
            results[name] = {'unmutated_copy_accepted': True, 'mutation': evidence, **outcome}
            print(name, json.dumps(outcome), flush=True)
    assert tuple(results) == CASES
    record = {'complete': True, 'reviewed_commit': '0db6c9d', 'expected_cases': list(CASES),
              'results': results, 'auditor_sha256': hashlib.sha256((HERE/'census_audit.py').read_bytes()).hexdigest(),
              'program_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'scope': 'copies of retained artifacts; no compilation, kernel replay, credential read or provider call'}
    args.output.write_text(json.dumps(record, indent=2)+'\n')


if __name__ == '__main__':
    main()

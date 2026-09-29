#!/usr/bin/env python3
"""Exact-name-gated controls for the corrected outer publication gate.

These live outside the frozen R6-004 source lock deliberately: the repair is in
the recount, and the v3 native episodes, adapter, auditor and policy are
untouched, so no further credential experiment is required. Each control copies
the retained v3 checkpoint, confirms the unmutated copy passes the full public
gate, then requires the mutated copy to be rejected at its own boundary.

Run with `python3 -B` so no bytecode is written into the scanned tree.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

import run as r6                                          # noqa: E402
from test_proposals import Suite, rejected, require        # noqa: E402

CASES = '''unmutated_checkpoint_accepted false_checkpoint_policy_hashes
false_native_seal_digest contradictory_native_observations
empty_preservation_inventory'''.split()


def load_gate():
    path = Path(__file__).parent/'credential_final_checks.py'
    spec = importlib.util.spec_from_file_location('credential_final_checks', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def full_gate(module, checkpoint):
    """The public command: the recount composed with its gate-suite record."""
    result = module.recount(checkpoint)
    result['gate_suite'] = module.gate_suite(checkpoint)
    result['total_checks'] += result['gate_suite']['count']
    require(not result['prior_changed_or_missing'], 'a pre-existing artifact changed')
    return result


def rebind_suite(copied, name):
    index = r6.read_json(copied/'checkpoint.json')
    index['suites'][name] = {'sha256': r6.sha(copied/name),
                             'count': r6.read_json(copied/name)['check_count']}
    r6.write_json(copied/'checkpoint.json', index)


def edit_native(copied, case, change):
    value = r6.read_json(copied/'credential-native.json')
    detail = next(c for c in value['checks'] if c['name'] == case)['detail']
    change(detail)
    r6.write_json(copied/'credential-native.json', value)
    rebind_suite(copied, 'credential-native.json')


def controls(checkpoint, output):
    suite = Suite(output, CASES)
    module = load_gate()

    def probe(name, change, contains):
        def test():
            with tempfile.TemporaryDirectory(prefix='r6-gate-control-') as directory:
                copied = Path(directory)/'checkpoint'
                shutil.copytree(checkpoint, copied)
                baseline = full_gate(module, copied)
                require(baseline['passed'] is True and baseline['total_checks'] == 67,
                        'the unmutated copy did not pass the public gate')
                change(copied)
                result = rejected(lambda: full_gate(module, copied), contains)
                return {**result, 'unmutated_copy_passes': True,
                        'gate': 'public recount and gate-suite record'}
        suite.case(name, test)

    def accepted():
        with tempfile.TemporaryDirectory(prefix='r6-gate-baseline-') as directory:
            copied = Path(directory)/'checkpoint'
            shutil.copytree(checkpoint, copied)
            result = full_gate(module, copied)
            require(result['passed'] is True and result['total_checks'] == 67, str(result)[:200])
            return {'passed': True, 'total_checks': result['total_checks'],
                    'prior_files_checked': result['prior_files_checked'],
                    'preservation': result['preservation'],
                    'checkpoint_declarations': result['checkpoint_declarations']}
    suite.case('unmutated_checkpoint_accepted', accepted)

    def false_policy(copied):
        index = r6.read_json(copied/'checkpoint.json')
        index['policy_sha256'] = index['source_lock_sha256'] = '0'*64
        r6.write_json(copied/'checkpoint.json', index)
    probe('false_checkpoint_policy_hashes', false_policy,
          'checkpoint policy digest differs from the frozen policy')

    probe('false_native_seal_digest',
          lambda c: edit_native(c, 'd1_valid', lambda d: d.update(seal_sha256='0'*64)),
          'native suite record seal digest differs from the episode')

    def contradictory(detail):
        detail.update(files_scanned=0, disclosures=999, outer_log_clean=False,
                      coverage={'recomputed': 0, 'recorded_not_recomputed': 0, 'files_scanned': 0})
    probe('contradictory_native_observations', lambda c: edit_native(c, 'd1_valid', contradictory),
          'native suite record scan count differs from the episode')

    probe('empty_preservation_inventory',
          lambda c: r6.write_json(c/'prior-artifacts.sha256.json', {}),
          'preservation inventory differs from the pinned commit population')
    suite.finish()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', type=Path, default=ROOT/'runs/credential-checkpoint-v3')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).parent/'R6-004-V3-GATE-CONTROLS.json')
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit('Refusing to overwrite an existing control record: '+str(args.output))
    controls(args.checkpoint.resolve(), args.output.resolve())
    print(json.dumps({'passed': True, 'cases': len(CASES), 'output': str(args.output)}, indent=1))


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Disposable R6-004 v3 review probes; no native episode or adapter execution."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path.cwd() / 'experiments/r6'
sys.path.insert(0, str(ROOT))
import credential
import publication
import test_credentials as tests

CHECKPOINT = ROOT / 'runs/credential-checkpoint-v3'
RECOUNT = ROOT / 'reviews/2026-09-09/credential_final_checks.py'


def read(path):
    return json.loads(path.read_bytes())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_public(checkpoint, destination):
    process = subprocess.run([sys.executable, '-B', str(RECOUNT), '--checkpoint', str(checkpoint),
                              '--output', str(destination)], capture_output=True, text=True)
    value = read(destination) if destination.exists() else None
    return {'exit_code': process.returncode, 'report_written': value is not None,
            'passed': value['passed'] if value else None,
            'total_checks': value['total_checks'] if value else None,
            'error': process.stderr.strip().splitlines()[-1] if process.stderr.strip() else None}


def context_probe():
    # Execute the independent v2 reproduction unchanged, with only its input
    # checkpoint selected explicitly. Its own baseline audit must pass first.
    path = ROOT / 'reviews/2026-09-09/r6_004_v2_review_probes.py'
    spec = importlib.util.spec_from_file_location('previous_review_probe', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.CHECKPOINT = CHECKPOINT
    result = module.context_probe()
    assert result['unmutated_audit_accepted'] is True
    assert result['audit_returned'] is False
    assert 'reconstruction context differs from the frozen obligation' in result['error']
    return result


def gate_record_probes():
    checker = tests.load_recount()
    results = []
    def absent(root):
        index = read(root / 'checkpoint.json')
        del index['gates']
        write(root / 'checkpoint.json', index)
    def changed(root, kind):
        file = root / tests.GATES_FILE
        value = read(file)
        if kind == 'missing_case':
            removed = value['checks'].pop()
            value['expected_cases'].remove(removed['name'])
            value['check_count'] -= 1
        elif kind == 'failed':
            value['passed'] = False
        elif kind == 'no_passing_baseline':
            value['checks'][0]['detail']['unmutated_copy_passes'] = False
        write(file, value)
        index = read(root / 'checkpoint.json')
        index['gates'].update(sha256=sha(file), count=value['check_count'])
        write(root / 'checkpoint.json', index)
    cases = [('missing_gate_record', absent, 'declares no gate-suite record'),
             ('missing_gate_case', lambda r: changed(r, 'missing_case'), 'case set differs'),
             ('failed_gate_suite', lambda r: changed(r, 'failed'), 'gate suite did not pass'),
             ('missing_gate_precondition', lambda r: changed(r, 'no_passing_baseline'),
              'did not first confirm its unmutated copy passes')]
    for name, change, message in cases:
        with tempfile.TemporaryDirectory(prefix='r6-v3-gate-record-') as td:
            root = Path(td)
            for file in ('checkpoint.json', tests.GATES_FILE):
                shutil.copyfile(CHECKPOINT / file, root / file)
            assert checker.gate_suite(root)['count'] == 6
            change(root)
            try:
                checker.gate_suite(root)
            except ValueError as error:
                assert message in str(error), str(error)
                results.append({'name': name, 'unmutated_copy_passes': True,
                                'rejected': True, 'error': str(error)})
            else:
                raise AssertionError(name + ' was accepted')
    return results


def publication_identity_probes():
    results = []
    with tempfile.TemporaryDirectory(prefix='r6-v3-public-gate-') as td:
        root = Path(td) / 'checkpoint'
        shutil.copytree(CHECKPOINT, root)
        baseline = run_public(root, Path(td) / 'baseline.json')
        assert baseline['exit_code'] == 0 and baseline['passed'] is True and baseline['total_checks'] == 67
        original_index = (root / 'checkpoint.json').read_bytes()
        original_native = (root / 'credential-native.json').read_bytes()

        index = read(root / 'checkpoint.json')
        index.update(policy_sha256='0' * 64, source_lock_sha256='1' * 64)
        write(root / 'checkpoint.json', index)
        observed = run_public(root, Path(td) / 'altered-policy.json')
        results.append({'name': 'checkpoint_policy_and_lock_binding', 'unmutated_copy_passes': True,
                        'mutation': 'Only checkpoint policy/source-lock hashes changed; episode policies untouched.',
                        'outcome': observed})
        (root / 'checkpoint.json').write_bytes(original_index)

        value = read(root / 'credential-native.json')
        chosen = [c for c in value['checks'] if c['name'] == 'd1_valid']
        assert len(chosen) == 1
        actual = sha(root / 'd1_valid/seal.json')
        assert chosen[0]['detail']['seal_sha256'] == actual
        chosen[0]['detail']['seal_sha256'] = '0' * 64
        write(root / 'credential-native.json', value)
        index = read(root / 'checkpoint.json')
        index['suites']['credential-native.json']['sha256'] = sha(root / 'credential-native.json')
        write(root / 'checkpoint.json', index)
        observed = run_public(root, Path(td) / 'altered-native-seal.json')
        results.append({'name': 'native_suite_seal_binding', 'unmutated_copy_passes': True,
                        'mutation': 'Native-suite d1_valid seal hash changed to zero; suite hash rebound; actual episode untouched.',
                        'actual_seal_sha256': actual, 'outcome': observed})
        (root / 'credential-native.json').write_bytes(original_native)
        (root / 'checkpoint.json').write_bytes(original_index)

        value = read(root / 'credential-native.json')
        chosen = [c for c in value['checks'] if c['name'] == 'd1_valid']
        assert len(chosen) == 1 and chosen[0]['detail']['files_scanned'] > 0
        chosen[0]['detail'].update(files_scanned=0, disclosures=999, outer_log_clean=False,
                                  coverage={'recorded_not_recomputed': 999})
        write(root / 'credential-native.json', value)
        index = read(root / 'checkpoint.json')
        index['suites']['credential-native.json']['sha256'] = sha(root / 'credential-native.json')
        write(root / 'checkpoint.json', index)
        observed = run_public(root, Path(td) / 'altered-native-observations.json')
        results.append({'name': 'native_suite_observation_binding', 'unmutated_copy_passes': True,
                        'mutation': 'd1_valid native-suite scan count, coverage, disclosure count and outer-log result contradicted; suite hash rebound.',
                        'outcome': observed})
        (root / 'credential-native.json').write_bytes(original_native)
        (root / 'checkpoint.json').write_bytes(original_index)

        prior = root / 'prior-artifacts.sha256.json'
        original_prior = prior.read_bytes()
        assert len(read(prior)) == 9986
        write(prior, {})
        observed = run_public(root, Path(td) / 'empty-preservation.json')
        recounted = read(Path(td) / 'empty-preservation.json') if observed['report_written'] else None
        results.append({'name': 'preservation_population_binding', 'unmutated_copy_passes': True,
                        'mutation': 'Replace the 9,986-entry prior-artifact inventory with an empty map; suite records untouched.',
                        'prior_files_checked': recounted['prior_files_checked'] if recounted else None,
                        'outcome': observed})
        prior.write_bytes(original_prior)
    return results


def safe_path_probe():
    nonce = credential.nonce()
    canary = credential.derive(nonce)
    with tempfile.TemporaryDirectory(prefix='r6-v3-safe-path-') as td:
        root = Path(td)
        ordinary = root / 'ordinary.txt'
        ordinary.write_text('clean\n')
        target = root / canary
        target.symlink_to(ordinary)
        assert target.is_symlink()
        result = publication.scan([root], canary, nonce)
        assert result['accepted'] is False
        assert canary not in json.dumps(result)
        entry = result['irregular_entries'][0]['entry']
        assert entry['name'] is None and entry['name_sha256'] == hashlib.sha256(canary.encode()).hexdigest()
    return {'symlink_precondition': True, 'publication_accepted': False,
            'diagnostic_contains_canary': False, 'name_is_null': True, 'name_digest_verified': True}


def main():
    output = Path(sys.argv[1])
    assert not output.exists()
    result = {'scope': __doc__, 'source_sha256': sha(Path(__file__)),
              'context': context_probe(), 'safe_paths': safe_path_probe(),
              'gate_suite_validation': gate_record_probes()}
    print('Context, path and gate-record controls passed', flush=True)
    result['publication_identity'] = publication_identity_probes()
    write(output, result)
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()

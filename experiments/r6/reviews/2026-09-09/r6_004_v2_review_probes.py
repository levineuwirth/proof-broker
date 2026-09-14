#!/usr/bin/env python3
"""Run from the Proof Broker root; disposable R6-004 v2 artifact review probes."""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path.cwd()/'experiments/r6'
sys.path.insert(0, str(ROOT))
import credential
import credential_audit as auditor
import credential_episode as harness
import events
import publication
import run as r6
import test_credentials as test
from test_task_identity import rehash

CHECKPOINT = ROOT/'runs/credential-checkpoint-v2'


def read(path):
    return json.loads(path.read_bytes())


def write(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rebind_scan(run):
    """Recompute scan-time observations and all later commitments on a copy."""
    original = read(run/'seal.json')
    nonce = read(run/'credential-canary.json')['nonce']
    value = credential.derive(nonce)
    patterns = publication.patterns(value)
    report = read(run/'publication-scan.json')
    for index, entry in enumerate(report['inventory']):
        name = entry['path']
        assert name is not None
        path = run/name
        if not path.exists():
            continue
        if name == 'events.ndjson':
            raw = b''.join(path.read_bytes().splitlines(keepends=True)[:-1])
            fresh = publication.scan_data(raw, patterns, publication.identify(name, patterns)[0])
        else:
            fresh = publication.scan_file(path, patterns, run)
        report['inventory'][index] = fresh
    report['disclosures'] = [{'path': e['path'], 'path_sha256': e['path_sha256'], **hit}
                              for e in report['inventory'] for hit in e['findings']]
    assert not report['disclosures']
    write(run/'publication-scan.json', report)
    write(run/'publication-final.json', publication.final_record(run/'publication-scan.json', value, nonce))
    rows = events.read(run/'events.ndjson')
    rows[-1]['payload']['publication_scan_sha256'] = sha(run/'publication-scan.json')
    rows[-1]['payload']['publication_final_sha256'] = sha(run/'publication-final.json')
    (run/'events.ndjson').write_bytes(rehash(rows))
    harness.seal(run, True, original['ephemeral_sha256'])


def context_probe():
    with tempfile.TemporaryDirectory(prefix='r6-004-v2-context-review-') as td:
        run = Path(td)/'d1_valid'
        shutil.copytree(CHECKPOINT/'d1_valid', run)
        assert auditor.audit(run, r6.D1)['accepted'] is True
        path = run/'stages/reconstruct/output/context.json'
        data = read(path)
        assert data['target'] != 'False'
        data['target'] = 'False'
        write(path, data)
        rows = events.read(run/'events.ndjson')
        matches = [r for r in rows if r['event'] == 'context_validated']
        assert len(matches) == 1
        matches[0]['payload']['captured_context_sha256'] = sha(path)
        (run/'events.ndjson').write_bytes(rehash(rows))
        rebind_scan(run)
        try:
            outcome = auditor.audit(run, r6.D1)
            return {'unmutated_audit_accepted': True, 'captured_target_mutated_to': 'False',
                    'differs_from_frozen_context': read(path) != read(r6.D1.path/'context/local-context.json'),
                    'events_scan_and_seal_rebound': True, 'audit_returned': True,
                    'accepted': outcome['accepted'], 'proof_accepted': outcome['proof_accepted'],
                    'publication_accepted': outcome['publication_accepted']}
        except (ValueError, AssertionError) as error:
            return {'unmutated_audit_accepted': True, 'events_scan_and_seal_rebound': True,
                    'audit_returned': False, 'error': str(error)}


def recount_probes():
    module = test.load_recount()
    result = []

    def missing_case(root):
        filename = 'credential-units.json'
        suite = read(root/filename)
        case = 'scan_unreadable_directory'
        assert sum(c['name'] == case for c in suite['checks']) == 1
        suite['checks'] = [c for c in suite['checks'] if c['name'] != case]
        suite['expected_cases'].remove(case)
        suite['check_count'] -= 1
        write(root/filename, suite)
        index = read(root/'checkpoint.json')
        index['suites'][filename] = {'sha256': sha(root/filename), 'count': suite['check_count']}
        write(root/'checkpoint.json', index)
        return {'deleted_frozen_case': case, 'suite_and_checkpoint_counts_and_hashes_updated': True}

    def substituted_case(root):
        target = root/'d1_missing_credential'
        shutil.rmtree(target)
        shutil.copytree(root/'d1_valid', target)
        assert read(target/'search-policy.json')['case'] == 'valid'
        return {'expected_directory': 'd1_missing_credential', 'actual_policy_case': 'valid',
                'valid_episode_substituted_for_negative_control': True}

    def false_checkpoint(root):
        index = read(root/'checkpoint.json')
        assert index['passed'] is True
        index['passed'] = False
        write(root/'checkpoint.json', index)
        return {'checkpoint_passed_flag': False}

    for name, change in [('deleted_frozen_check', missing_case), ('substituted_native_control', substituted_case),
                         ('checkpoint_still_red', false_checkpoint)]:
        with tempfile.TemporaryDirectory(prefix='r6-004-v2-recount-review-') as td:
            root = Path(td)/'checkpoint'
            shutil.copytree(CHECKPOINT, root)
            baseline = module.recount(root)
            assert baseline['passed'] is True and baseline['total_checks'] == 62
            detail = change(root)
            try:
                observed = module.recount(root)
                result.append({'name': name, 'unmutated_copy_passes': True, 'detail': detail,
                               'passed': observed['passed'], 'total_checks': observed['total_checks'],
                               'episode_count': len(observed['episodes']),
                               'episode_proof_accepted': {n: v['proof_accepted'] for n, v in observed['episodes'].items()},
                               'unexpected_disclosures': observed['disclosures_unexpected'],
                               'prior_changed_or_missing': observed['prior_changed_or_missing'],
                               'python_compile_exit': observed['python_compile_exit']})
            except (ValueError, AssertionError) as error:
                result.append({'name': name, 'unmutated_copy_passes': True, 'detail': detail,
                               'passed': False, 'error': str(error)})
        print(name+' completed', flush=True)
    return result


if __name__ == '__main__':
    out = Path(sys.argv[1])
    assert not out.exists()
    result = {'scope': 'Disposable artifact/audit probes; no native replay, adapter execution, real credential or live call',
              'source_sha256': sha(Path(__file__)), 'context': context_probe(), 'recount': recount_probes()}
    write(out, result)
    print(json.dumps(result, indent=2))

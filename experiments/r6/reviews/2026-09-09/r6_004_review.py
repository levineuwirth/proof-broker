#!/usr/bin/env python3
"""Review R6-004 using retained artifacts and disposable mutations, without native episodes."""
import argparse
import base64
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parents[1]
sys.path.insert(0, str(ROOT))

import credential
import credential_audit
import credential_contract
import credential_episode
import envelope_audit
import episode
import events
import provider_audit
import publication
import run as r6
import test_credentials
from test_task_identity import rehash

CHECKPOINT = ROOT/'runs/credential-checkpoint-v1'
BASE = 'ac0f50f'


def require(value, message):
    if not value:
        raise AssertionError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def write(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()


def canary_at(path):
    seed = read(path/'credential-canary.json')['nonce']
    return seed, credential.derive(seed)


def rebind(path):
    """Update report commitment, terminal receipt and seal after a disposable mutation."""
    seed, canary = canary_at(path)
    final = publication.final_record(path/'publication-scan.json', canary, seed)
    write(path/'publication-final.json', final)
    rows = events.read(path/'events.ndjson')
    for field, filename in [('summary_sha256', 'credential-summary.json'),
                            ('publication_scan_sha256', 'publication-scan.json'),
                            ('publication_final_sha256', 'publication-final.json')]:
        rows[-1]['payload'][field] = sha((path/filename).read_bytes())
    (path/'events.ndjson').write_bytes(rehash(rows))
    credential_episode.seal(path, rows[-1]['payload']['accepted'])


def retained_mutation(name, change):
    with tempfile.TemporaryDirectory(prefix='r6-004-review-mutation-') as td:
        path = Path(td)
        test_credentials.retained_copy(CHECKPOINT/'d1_valid', path)
        pre = {str(p.relative_to(path)): sha(p.read_bytes()) for p in path.rglob('*') if p.is_file()}
        detail = change(path)
        require(any(not (path/p).exists() or sha((path/p).read_bytes()) != digest
                    for p, digest in pre.items()), name+' changed nothing')
        rebind(path)
        try:
            value = credential_audit.audit(path, r6.D1)
            outcome = {'audit_returned': True, 'accepted': value['accepted'],
                       'publication_accepted': value['publication_accepted'],
                       'proof_accepted': value['proof_accepted'], 'files_scanned': value['files_scanned']}
        except (ValueError, AssertionError) as error:
            outcome = {'audit_returned': False, 'error': str(error)}
        return {'name': name, 'mutation_precondition': True, 'coherently_rehashed_and_resealed': True,
                'detail': detail, **outcome}


def review():
    submitted = [ROOT/name for name in credential_contract.FILES]
    submitted += [credential_contract.CONFIG, credential_contract.LOCK, ROOT/'R6-004.md',
                  Path(__file__).with_name('credential_final_checks.py')]
    submitted += [p for p in CHECKPOINT.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
    before = {str(p.relative_to(REPO)): sha(p.read_bytes()) for p in submitted}
    credential_contract.verify_sources()
    result = {'scope': 'Independent review of recorded artifacts, scanner probes and disposable mutations; '
              'no native episode, Lean replay, adapter execution, live call or real credential',
              'base_commit': BASE, 'review_source_sha256': sha(Path(__file__).read_bytes()),
              'submitted_source_and_artifact_hashes': before}
    checkpoint = read(CHECKPOINT/'checkpoint.json')
    suites = {}
    for name, expected in [('credential-units.json', test_credentials.UNIT_CASES),
                           ('credential-native.json', test_credentials.NATIVE_CASES),
                           ('credential-audits.json', test_credentials.AUDIT_CASES)]:
        raw = (CHECKPOINT/name).read_bytes()
        value = json.loads(raw)
        names = [x['name'] for x in value['checks']]
        require(len(names) == len(set(names)) == len(expected) == value['check_count'], 'suite count')
        require(set(names) == set(value['expected_cases']) == set(expected), 'suite names differ from source')
        require(value['passed'] is True and all(x['passed'] is True for x in value['checks']), 'suite failed')
        detail = {'sha256': sha(raw), 'count': len(names)}
        require(checkpoint['suites'][name] == detail, 'suite hash/count binding')
        suites[name] = detail
    result['suites'] = suites
    result['recorded_checks'] = sum(x['count'] for x in suites.values())
    prior = read(CHECKPOINT/'prior-artifacts.sha256.json')
    scopes = ['experiments/r6/'+p for p in ['tasks', 'runs', 'policies', 'schema', 'prompts']]
    scopes += ['experiments/c1-cert-recovery']
    rows = subprocess.check_output(['git', 'ls-tree', '-r', '-z', BASE, *scopes], cwd=REPO).split(b'\0')
    tree = {}
    for row in rows:
        if row:
            header, name = row.split(b'\t', 1)
            mode, kind, oid = header.split()
            require(kind == b'blob', 'non-blob in preserved set')
            tree[name.decode()] = oid
    require(set(tree) == set(prior), 'prior population differs from pinned commit')
    child = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=REPO, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    blobs = {}
    try:
        for name, oid in tree.items():
            if oid not in blobs:
                child.stdin.write(oid+b'\n'); child.stdin.flush()
                header = child.stdout.readline().split()
                require(header[1] == b'blob', 'blob response')
                data = child.stdout.read(int(header[2])); require(child.stdout.read(1) == b'\n', 'blob framing')
                blobs[oid] = sha(data)
            require(blobs[oid] == prior[name] == sha((REPO/name).read_bytes()), 'preserved file changed: '+name)
    finally:
        child.stdin.close(); child.stdout.close(); require(child.wait() == 0, 'git cat-file failed')
    result['preservation'] = {'files': len(prior), 'pinned_commit_population_matches': True, 'changed': 0, 'missing': 0}
    print('Source locks, exact suite sets, and 9986 pinned prior files verified.', flush=True)

    native, n_events, n_sealed, n_scanned, n_hits = {}, 0, 0, 0, 0
    for name in test_credentials.NATIVE_CASES:
        path = CHECKPOINT/name
        seal = read(path/'seal.json')
        previous = '0'*64
        rows = [json.loads(line) for line in (path/'events.ndjson').read_bytes().splitlines()]
        for index, row in enumerate(rows):
            body = {k: v for k, v in row.items() if k != 'event_hash'}
            require(body['sequence'] == index and body['previous_hash'] == previous and sha(canonical(body)) == row['event_hash'], 'receipt chain')
            previous = row['event_hash']
        require(seal['event_count'] == len(rows) and seal['last_event_hash'] == previous, 'terminal seal')
        require(all(sha((path/p).read_bytes()) == digest for p, digest in seal['retained_sha256'].items()), 'seal bytes')
        seed = read(path/'credential-canary.json')['nonce']
        independent = 'R6CANARY'+sha(('r6-004-synthetic-canary-v1:'+seed).encode())
        require(independent == credential.derive(seed), 'derivation differs')
        fresh = publication.scan([path, CHECKPOINT/(name+'.log')], independent, seed)
        audit = credential_audit.audit(path, r6.D1)
        n_events += len(rows); n_sealed += len(seal['retained_sha256'])
        n_scanned += fresh['files_scanned']; n_hits += len(fresh['disclosures'])
        native[name] = {'events': len(rows), 'sealed_entries': len(seal['retained_sha256']),
                        'files_rescanned': fresh['files_scanned'], 'actual_disclosures': fresh['disclosures'],
                        'audit': audit}
    result['native_artifact_recomputation'] = native
    result['totals'] = {'events': n_events, 'sealed_entries': n_sealed, 'files_rescanned': n_scanned,
                        'actual_disclosures_all_five_episodes': n_hits,
                        'reported_canary_values_found_in_publication': read(CHECKPOINT/'final-checks.json')['canary_values_found_in_publication']}
    visible = subprocess.check_output(['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z', str(CHECKPOINT.relative_to(REPO))], cwd=REPO).decode().split('\0')
    sizes = [(len((REPO/name).read_bytes()), sha((REPO/name).read_bytes())) for name in set(visible)
             if name and not name.endswith('/final-checks.json')]
    unique = {digest: count for count, digest in sizes}
    result['retention_excluding_final_checks'] = {'files': len(sizes), 'apparent_bytes': sum(c for c, _ in sizes),
          'unique_contents': len(unique), 'unique_bytes': sum(unique.values())}
    print('Five episodes re-audited; actual disclosure count is '+str(n_hits)+'.', flush=True)
    historical = {}
    for label, source, task in [('broker_v1', 'golden-broker-v1', r6.D1), ('broker_v2', 'golden-broker-v2', r6.D1),
        ('broker_v3', 'golden-broker-v3', r6.D1), ('c8', 'golden-c8-v1', r6.C8),
        ('d1_fixture', 'proposal-checkpoint-v2/d1_valid', r6.D1), ('c8_fixture', 'proposal-checkpoint-v2/c8_valid', r6.C8),
        ('d1_envelope', 'envelope-checkpoint-v1/d1_valid', r6.D1), ('c8_envelope', 'envelope-checkpoint-v1/c8_valid', r6.C8),
        ('alternate_envelope', 'envelope-checkpoint-v1/d1_alternate_encoding', r6.D1),
        ('d1_provider', 'provider-checkpoint-v1/d1_valid', r6.D1), ('c8_provider', 'provider-checkpoint-v1/c8_valid', r6.C8),
        ('alternate_provider', 'provider-checkpoint-v1/d1_alternate_encoding', r6.D1)]:
        auditor = provider_audit.audit if source.startswith('provider-') else envelope_audit.audit if source.startswith('envelope-') else episode.audit
        historical[label] = auditor(ROOT/'runs'/source, task)['accepted']
        require(historical[label] is True, 'historical audit failed')
    result['historical_audits'] = historical
    print('Twelve historical audits pass.', flush=True)

    probes = {}
    seed = '1'*64; canary = credential.derive(seed)
    with tempfile.TemporaryDirectory(prefix='r6-004-review-directory-') as td:
        root = Path(td); hidden = root/'unreadable'; hidden.mkdir()
        (hidden/'header.log').write_text(credential.header(canary)); hidden.chmod(0)
        try:
            try: list(hidden.iterdir()); denied = False
            except PermissionError: denied = True
            require(denied, 'unreadable-directory precondition not established')
            fresh = publication.scan([root], canary, seed)
            probes['unreadable_directory'] = {'permission_denied_precondition': True,
                'accepted': fresh['accepted'], 'files_scanned': fresh['files_scanned'], 'incomplete': fresh['incompletely_scanned']}
        finally:
            hidden.chmod(0o700)
    with tempfile.TemporaryDirectory(prefix='r6-004-review-encoding-') as td:
        root = Path(td); data = base64.b64encode(credential.header(canary).encode())
        (root/'authorization.log').write_bytes(data)
        require(base64.b64decode(data) == credential.header(canary).encode(), 'encoded-header precondition')
        fresh = publication.scan([root], canary, seed)
        probes['base64_full_authorization'] = {'exact_header_encoded': True, 'accepted': fresh['accepted'], 'findings': len(fresh['disclosures'])}
    probes['safe_record_canary_key'] = {'accepts_full_canary_as_key': publication.safe_record({canary: True}),
                                       'scope': 'helper shape claim; full auditor scans post-scan files separately'}
    with tempfile.TemporaryDirectory(prefix='r6-004-review-report-path-') as td:
        root = Path(td); (root/canary).write_text('clean content')
        fresh = publication.scan([root], canary, seed)
        probes['canary_filename'] = {'scan_accepted': fresh['accepted'], 'report_reemits_canary_in_path': canary in json.dumps(fresh),
                                    'scope': 'report construction; separate report scan is a later detector'}
    result['scanner_probes'] = probes

    def scan_hashes(path):
        report = read(path/'publication-scan.json')
        entry = next(e for e in report['inventory'] if e['path'] == 'accounting.json')
        original = entry['sha256']; entry['sha256'] = '0'*64; entry['bytes'] = 987654321
        require(original != entry['sha256'], 'hash mutation precondition')
        write(path/'publication-scan.json', report)
        return {'entry': 'accounting.json', 'sha256_forged': True, 'bytes_forged': True}

    def phantom(path):
        report = read(path/'publication-scan.json'); fake = copy.deepcopy(report['inventory'][0])
        fake.update(path='nonexistent-review-target.json', sha256='0'*64, bytes=123, streams=['raw'], scanned=True, error=None, findings=[])
        require(not (path/fake['path']).exists(), 'phantom must be absent')
        report['inventory'].append(fake); report['files_scanned'] += 1
        write(path/'publication-scan.json', report)
        return {'nonexistent_target_claimed_scanned': True}

    def duplicate(path):
        report = read(path/'publication-scan.json')
        report['inventory'].append(copy.deepcopy(report['inventory'][0]))
        write(path/'publication-scan.json', report)
        return {'duplicate_inventory_entry': True}

    def mutate_event(path, event, replacement):
        rows = events.read(path/'events.ndjson')
        selected = [row for row in rows if row['source'] == 'supervisor' and row['event'] == event]
        require(len(selected) == 1 and selected[0]['payload'] != replacement, 'event mutation precondition')
        selected[0]['payload'] = replacement
        (path/'events.ndjson').write_bytes(rehash(rows))
        return {'event': event, 'replaced_payload': replacement}

    def client_arguments(path):
        value = read(path/'client-arguments.json')
        value['input'][0]['content'] += '\nUNAUTHORIZED REVIEW MESSAGE\n'
        write(path/'client-arguments.json', value)
        return {'altered_recorded_adapter_input': True, 'outbound_bytes_unchanged': True}

    def verdict_identity(path):
        value = read(path/'verdict.json'); value['manifest_sha256'] = '0'*64; value['challenge_sha256'] = '0'*64
        write(path/'verdict.json', value)
        rows = events.read(path/'events.ndjson')
        for row in rows:
            if row['event'] == 'proof_validated': row['payload']['verdict_sha256'] = sha((path/'verdict.json').read_bytes())
        (path/'events.ndjson').write_bytes(rehash(rows))
        return {'verdict_manifest_and_challenge_forged': True}

    changes = [('forged_scan_hash_and_size', scan_hashes), ('phantom_scan_target', phantom), ('duplicate_scan_target', duplicate),
        ('altered_request_reservation', lambda p: mutate_event(p, 'request_reserved', {'attempt': 0, 'request_sha256': '0'*64})),
        ('altered_route_attribution', lambda p: mutate_event(p, 'recovery_started', {'route': 'unrecorded_fallback', 'proposer': 'unrecorded_model'})),
        ('altered_client_arguments', client_arguments), ('forged_verdict_task_binding', verdict_identity)]
    result['resealed_mutations'] = [retained_mutation(name, change) for name, change in changes]
    print('Seven coherent artifact mutations completed.', flush=True)

    spec = importlib.util.spec_from_file_location('submitted_recount', Path(__file__).with_name('credential_final_checks.py'))
    recount_module = importlib.util.module_from_spec(spec); spec.loader.exec_module(recount_module)
    def recount_copy(name, change):
        with tempfile.TemporaryDirectory(prefix='r6-004-review-recount-') as td:
            target = Path(td)/'checkpoint'; shutil.copytree(CHECKPOINT, target)
            detail = change(target)
            try:
                value = recount_module.recount(target)
                return {'name': name, 'detail': detail, 'returned_passed': value['passed'],
                    'episodes_checked': value['episode_count'], 'files_rescanned': value['files_rescanned'],
                    'reported_canary_values_found_in_publication': value['canary_values_found_in_publication'],
                    'prior_changed_or_missing': value['prior_changed_or_missing'], 'python_compile_exit': value['python_compile_exit']}
            except (ValueError, AssertionError) as error:
                return {'name': name, 'detail': detail, 'returned_passed': False, 'error': str(error)}
    def missing_episode(target):
        shutil.rmtree(target/'d1_http503')
        return {'removed_expected_episode': 'd1_http503', 'native_suite_still_lists_five': True}
    def missing_log(target):
        (target/'d1_valid.log').unlink()
        return {'removed_required_outer_log': 'd1_valid.log'}
    def leaked_suite(target):
        seed, value = canary_at(target/'d1_valid')
        suite_path = target/'credential-native.json'; suite = read(suite_path)
        suite['review_injected_debug'] = credential.header(value); write(suite_path, suite)
        index = read(target/'checkpoint.json'); index['suites']['credential-native.json']['sha256'] = sha(suite_path.read_bytes())
        write(target/'checkpoint.json', index)
        require(value in suite_path.read_text(), 'suite leak precondition')
        return {'ordinary_checkpoint_artifact_contains_exact_header': True, 'suite_hash_rebound': True}
    result['recount_mutations'] = [recount_copy(name, change) for name, change in [
        ('missing_episode', missing_episode), ('missing_outer_log', missing_log), ('canary_in_suite_artifact', leaked_suite)]]
    result['submitted_bytes_unchanged'] = all((REPO/name).is_file() and sha((REPO/name).read_bytes()) == digest for name, digest in before.items())
    require(result['submitted_bytes_unchanged'], 'review changed submitted artifacts')
    result['review_execution'] = {'native_episodes': 0, 'live_calls': 0, 'real_credentials': 0,
                                 'submitted_recount_invocations': 3,
                                 'python_py_compile_invoked_by_submitted_recount': True}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    require(not args.output.exists(), 'review output already exists')
    result = review()
    with args.output.open('x') as handle:
        handle.write(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ['recorded_checks', 'totals', 'retention_excluding_final_checks',
                   'scanner_probes', 'resealed_mutations', 'recount_mutations', 'submitted_bytes_unchanged']}, indent=2))


if __name__ == '__main__':
    main()

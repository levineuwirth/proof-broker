#!/usr/bin/env python3
"""R6-004 exact-name-gated credential, publication and retained-audit controls."""
import argparse
import gzip
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest import mock

import credential
import credential_audit as auditor
import credential_contract as contract
import credential_episode as harness
import credential_http
import envelope_audit
import episode
import events
import instrument
import provider_audit
import publication
import run as r6
from test_proposals import Suite, assert_complete, rejected, require
from test_task_identity import rehash

GATES_FILE = 'credential-gates.json'
UNIT_CASES = '''canary_derivation_frozen canary_nonce_validated canary_record_omits_value
delivery_outside_artifact_tree delivery_value_absent_from_command
encoded_forms_declared scan_detects_each_form scan_authorization_representation scan_detects_gzip_member
scan_decompression_limit scan_unreadable_rejects scan_unreadable_directory scan_symlink_rejected
scan_findings_omit_value scan_path_disclosure scan_irregular_name_safe
scan_inventory_independent scan_missing_target_rejected
final_record_structurally_safe safe_record_exact_keys finalization_order_declared
receipt_requires_exact_value receipt_expectation_derived
source_lock_guard missing_case_rejected duplicate_case_rejected'''.split()
NATIVE_CASES = ['d1_valid', 'd1_http503', 'd1_missing_credential', 'd1_wrong_credential', 'd1_reflected_canary']
AUDIT_CASES = '''d1_retained_only reflected_canary_audited
injected_log_leak injected_metadata_leak injected_gzip_leak
missing_scanner omitted_scan_target forged_passing_report forged_receipt_digest
forged_scan_hash_and_size phantom_scan_target duplicate_scan_target
altered_request_reservation altered_route_attribution altered_client_arguments
forged_verdict_task_binding altered_reconstruction_context
legacy_broker_v1 legacy_broker_v2 legacy_broker_v3 legacy_c8_v1
legacy_d1_fixture legacy_c8_fixture
legacy_d1_envelope legacy_c8_envelope legacy_alternate_envelope
legacy_d1_provider legacy_c8_provider legacy_alternate_provider
prior_artifacts_preserved'''.split()
# The publication gate is exercised against a partial run; the complete-checkpoint
# contract is exercised against the finished checkpoint. Neither weakens the other.
GATE_CASES = '''recount_missing_episode recount_missing_log recount_suite_artifact_leak
recount_incomplete_status recount_substituted_episode recount_incomplete_case_set'''.split()
SUITE_CASES = {'credential-units.json': UNIT_CASES, 'credential-native.json': NATIVE_CASES,
               'credential-audits.json': AUDIT_CASES}
NATIVE_CONTRACT = {
    'd1_valid': {'task_id': 'verinf-d1-70', 'case': 'valid', 'accepted': True,
                 'credential_receipt_accepted': True, 'publication_accepted': True, 'failure_category': None},
    'd1_http503': {'task_id': 'verinf-d1-70', 'case': 'http503', 'accepted': False,
                   'credential_receipt_accepted': True, 'publication_accepted': True,
                   'failure_category': 'provider_http_error'},
    'd1_missing_credential': {'task_id': 'verinf-d1-70', 'case': 'missing_credential', 'accepted': False,
                              'credential_receipt_accepted': False, 'publication_accepted': True,
                              'failure_category': 'credential_receipt_failure'},
    'd1_wrong_credential': {'task_id': 'verinf-d1-70', 'case': 'wrong_credential', 'accepted': False,
                            'credential_receipt_accepted': False, 'publication_accepted': True,
                            'failure_category': 'credential_receipt_failure'},
    'd1_reflected_canary': {'task_id': 'verinf-d1-70', 'case': 'reflected_canary', 'accepted': False,
                            'credential_receipt_accepted': True, 'publication_accepted': False,
                            'failure_category': 'provider_http_error'}}
BASE = 'ac0f50f'


def units(root):
    suite = Suite(root/'credential-units.json', UNIT_CASES)
    seed = credential.nonce()
    canary = credential.derive(seed)
    header = credential.header(canary)
    pats = publication.patterns(canary)

    def derivation():
        require(credential.derive(seed) == canary and canary.startswith(credential.TAG))
        require(credential.derive(credential.nonce()) != canary, 'derivation ignores its nonce')
        require(canary == credential.TAG+r6.hashlib.sha256((credential.DOMAIN+':'+seed).encode()).hexdigest())
        return {'derivation': credential.DOMAIN, 'tag': credential.TAG,
                'canary_sha256': r6.hashlib.sha256(canary.encode()).hexdigest()}
    suite.case('canary_derivation_frozen', derivation)
    suite.case('canary_nonce_validated', lambda: [rejected(lambda v=v: credential.derive(v), 'nonce')
                                                  for v in ['', 'zz', seed.upper(), seed[:-1], None]] and 'rejected')

    def record_shape():
        value = credential.record(seed)
        blob = json.dumps(value)
        require(canary not in blob and header not in blob, 'record retains the value')
        require(value['nonce'] == seed and value['value_retained'] is False)
        require(value['authorization_sha256'] == credential.commitment(canary))
        return value
    suite.case('canary_record_omits_value', record_shape)

    def delivery():
        with credential.delivery(seed) as (value, path):
            require(value == canary and credential.read(path) == header)
            require(not path.is_relative_to(r6.ROOT), 'credential materialized inside the artifact tree')
            require(oct(path.stat().st_mode)[-3:] == '600', 'credential file is not private')
            kept = path
        require(not kept.exists() and not kept.parent.exists(), 'credential survived the episode')
        return {'mode': '600', 'outside_artifact_tree': True, 'removed_after_use': True}
    suite.case('delivery_outside_artifact_tree', delivery)

    def absent_from_command():
        source = (r6.ROOT/'credential_episode.py').read_text()
        require("'--credential-file', contract.GUEST_CREDENTIAL" in source, 'adapter receives a path, not a value')
        require('--setenv' not in (r6.ROOT/'credential_http.py').read_text())
        argv = ['--credential-file', contract.GUEST_CREDENTIAL, '--case', 'valid']
        environment = {'PATH': '/no-programs', 'LEAN_ABORT_ON_PANIC': '1'}
        joined = '\x00'.join(argv)+'\x00'+'\x00'.join(f'{k}={v}' for k, v in environment.items())
        require(canary not in joined and header not in joined)
        return {'argv_carries': 'guest path only', 'environment_carries': sorted(environment)}
    suite.case('delivery_value_absent_from_command', absent_from_command)

    def declared():
        require(len(pats) == 14 and all(pats.values()))
        require(sorted(pats) == sorted(r+':'+f for r in publication.REPRESENTATIONS for f in publication.FORMS))
        return {'representations': list(publication.REPRESENTATIONS), 'forms': list(publication.FORMS)}
    suite.case('encoded_forms_declared', declared)

    def each_form():
        detected = {}
        with tempfile.TemporaryDirectory(prefix='r6-scan-forms-') as directory:
            base = Path(directory)
            for name, pattern in pats.items():
                (base/name.replace(':', '.')).write_bytes(b'prefix '+pattern+b' suffix')
            report = publication.scan([base], canary, seed)
            for hit in report['disclosures']:
                detected.setdefault(hit['path'], set()).add(hit['representation']+':'+hit['form'])
            require(report['accepted'] is False, 'declared forms went undetected')
            for name in pats:
                where = name.replace(':', '.')
                require(name in detected.get(where, set()), 'undetected in its own file: '+name)
        return {'patterns_detected': len(pats), 'disclosures': len(report['disclosures'])}
    suite.case('scan_detects_each_form', each_form)

    def authorization_representation():
        # Encoding the whole header changes alignment: token patterns miss it.
        encoded = r6.hashlib.sha256(b'').hexdigest() and __import__('base64').b64encode(header.encode())
        require(__import__('base64').b64encode(canary.encode()) not in encoded, 'precondition absent: alignment unchanged')
        require(not publication.occurrences(encoded, {k: v for k, v in pats.items() if k.startswith('token:')}),
                'token-only patterns already matched')
        hits = publication.occurrences(encoded, pats)
        require([h['representation']+':'+h['form'] for h in hits] == ['authorization:base64'], str(hits))
        with tempfile.TemporaryDirectory(prefix='r6-scan-auth-') as directory:
            base = Path(directory)
            (base/'encoded-header.txt').write_bytes(encoded)
            report = publication.scan([base], canary, seed)
            require(report['accepted'] is False and len(report['disclosures']) == 1)
            require(__import__('base64').b64decode(encoded).decode() == header, 'decoding does not reproduce the header')
        return {'representation': 'authorization', 'form': 'base64', 'token_patterns_matched': 0}
    suite.case('scan_authorization_representation', authorization_representation)

    def gzip_member():
        with tempfile.TemporaryDirectory(prefix='r6-scan-gzip-') as directory:
            base = Path(directory)
            with gzip.open(base/'artifact.ndjson.gz', 'wb') as handle:
                handle.write(b'{"note":"'+canary.encode()+b'"}\n')
            require(canary.encode() not in (base/'artifact.ndjson.gz').read_bytes(), 'compression precondition absent')
            report = publication.scan([base], canary, seed)
            hits = [h for h in report['disclosures'] if h['stream'] == 'gzip']
            require(report['accepted'] is False and len(hits) == 1 and report['gzip_streams_scanned'] == 1)
        return {'gzip_streams_scanned': 1, 'raw_stream_clean': True, 'findings': hits}
    suite.case('scan_detects_gzip_member', gzip_member)

    def limit():
        with tempfile.TemporaryDirectory(prefix='r6-scan-limit-') as directory:
            base = Path(directory)
            with gzip.open(base/'large.gz', 'wb') as handle:
                handle.write(b'0'*4096)
            report = publication.scan([base], canary, seed, limit=1024)
            require(report['accepted'] is False and [e['path'] for e in report['incompletely_scanned']] == ['large.gz'])
            require(report['inventory'][0]['error'] == 'decompression_limit_exceeded'
                    and report['inventory'][0]['scanned'] is False)
        return {'limit_bytes': 1024, 'incompletely_scanned': ['large.gz']}
    suite.case('scan_decompression_limit', limit)

    def unreadable_file():
        with tempfile.TemporaryDirectory(prefix='r6-scan-unreadable-') as directory:
            base = Path(directory)
            target = base/'locked.json'
            target.write_bytes(b'{}')
            os.chmod(target, 0o000)
            try:
                if os.access(target, os.R_OK):
                    return {'skipped': 'privileged reader can read a mode-000 file', 'enforced': False}
                report = publication.scan([base], canary, seed)
                require(report['accepted'] is False and [e['path'] for e in report['incompletely_scanned']] == ['locked.json'])
                require(report['inventory'][0]['error'].startswith('unreadable'))
            finally:
                os.chmod(target, 0o600)
        return {'incompletely_scanned': ['locked.json'], 'enforced': True}
    suite.case('scan_unreadable_rejects', unreadable_file)

    def unreadable_directory():
        with tempfile.TemporaryDirectory(prefix='r6-scan-dir-') as directory:
            base = Path(directory)
            hidden = base/'hidden'
            hidden.mkdir()
            (hidden/'leak.log').write_bytes(b'Authorization: '+header.encode())
            os.chmod(hidden, 0o000)
            try:
                try:
                    list(hidden.iterdir())
                    return {'skipped': 'privileged reader can enumerate a mode-000 directory', 'enforced': False}
                except PermissionError:
                    pass
                report = publication.scan([base], canary, seed)
                require(report['accepted'] is False, 'an unenumerable subtree was accepted')
                require([u['directory']['name'] for u in report['unreadable_directories']] == ['hidden'],
                        str(report['unreadable_directories']))
                require(report['files_scanned'] == 0)
            finally:
                os.chmod(hidden, 0o700)
            # Prove the hidden subtree really did contain a target.
            opened = publication.scan([base], canary, seed)
            require(opened['accepted'] is False and len(opened['disclosures']) >= 1, 'hidden target precondition absent')
        return {'unreadable_directories': ['hidden'], 'target_present_once_readable': True}
    suite.case('scan_unreadable_directory', unreadable_directory)

    def symlink():
        with tempfile.TemporaryDirectory(prefix='r6-scan-link-') as directory:
            base = Path(directory)
            (base/'real.json').write_bytes(b'{}')
            (base/'link.json').symlink_to(base/'real.json')
            report = publication.scan([base], canary, seed)
            require(report['accepted'] is False, 'a symlink was silently followed or ignored')
            require([e['kind'] for e in report['irregular_entries']] == ['symlink']
                    and [e['entry']['name'] for e in report['irregular_entries']] == ['link.json'])
            require(report['files_scanned'] == 1, 'the symlink target was scanned twice or skipped')
        return {'policy': 'symlinks are rejected, never followed', 'irregular_entries': 1}
    suite.case('scan_symlink_rejected', symlink)

    def omit_value():
        with tempfile.TemporaryDirectory(prefix='r6-scan-quiet-') as directory:
            base = Path(directory)
            (base/'leak.log').write_bytes(b'authorization '+header.encode())
            report = publication.scan([base], canary, seed)
            blob = json.dumps(report)
            require(report['accepted'] is False and report['disclosures'])
            require(canary not in blob and canary.lower() not in blob.lower(), 'report re-emits the detected value')
            require(all(set(h) == {'path', 'path_sha256', 'stream', 'representation', 'form', 'offset'}
                        for h in report['disclosures']))
        return {'findings_record': sorted(report['disclosures'][0]), 'value_reemitted': False}
    suite.case('scan_findings_omit_value', omit_value)

    def path_disclosure():
        with tempfile.TemporaryDirectory(prefix='r6-scan-path-') as directory:
            base = Path(directory)
            (base/('receipt-'+canary+'.log')).write_bytes(b'clean content')
            report = publication.scan([base], canary, seed)
            require(report['accepted'] is False, 'a canary-bearing filename was accepted')
            require([h['stream'] for h in report['disclosures']] == ['path'], str(report['disclosures']))
            require(report['inventory'][0]['path'] is None and len(report['inventory'][0]['path_sha256']) == 64)
            require(canary not in json.dumps(report), 'the report re-emitted the filename')
        return {'stream': 'path', 'identifier': 'path_sha256', 'name_reemitted': False}
    suite.case('scan_path_disclosure', path_disclosure)

    def irregular_name_safe():
        with tempfile.TemporaryDirectory(prefix='r6-scan-linkname-') as directory:
            base = Path(directory)
            (base/'ordinary.txt').write_text('clean')
            (base/canary).symlink_to(base/'ordinary.txt')
            report = publication.scan([base], canary, seed)
            require(report['accepted'] is False, 'a canary-named symlink was accepted')
            entry = report['irregular_entries'][0]
            require(entry['kind'] == 'symlink' and entry['entry']['name'] is None
                    and len(entry['entry']['name_sha256']) == 64, str(entry))
            require(canary not in json.dumps(report), 'the diagnostic record re-emitted the value')
        return {'kind': 'symlink', 'identifier': 'name_sha256', 'name_reemitted': False}
    suite.case('scan_irregular_name_safe', irregular_name_safe)

    def independent():
        with tempfile.TemporaryDirectory(prefix='r6-scan-walk-') as directory:
            base = Path(directory)
            (base/'nested').mkdir()
            for name in ['a.json', 'nested/b.log', 'nested/c.gz']:
                (base/name).write_bytes(b'clean')
            walked = sorted(str(p.relative_to(base)) for p, _ in publication.inventory([base], pats)[0])
            require(walked == ['a.json', 'nested/b.log', 'nested/c.gz'], 'walk missed a file')
            report = publication.scan([base], canary, seed)
            require(sorted(e['path'] for e in report['inventory']) == walked and report['accepted'])
        return {'walked': walked, 'source': 'filesystem walk; no reported target list'}
    suite.case('scan_inventory_independent', independent)
    suite.case('scan_missing_target_rejected',
               lambda: rejected(lambda: publication.scan([r6.ROOT/'no-such-target'], canary, seed), 'missing'))

    def structural():
        with tempfile.TemporaryDirectory(prefix='r6-final-') as directory:
            report = Path(directory)/'publication-scan.json'
            report.write_bytes(b'{"disclosures":[]}')
            value = publication.final_record(report, canary, seed)
            require(value['report_clean'] is True and value['report_findings'] == 0)
            report.write_bytes(b'{"leak":"'+header.encode()+b'"}')
            dirty = publication.final_record(report, canary, seed)
            require(dirty['report_clean'] is False and dirty['report_findings'] >= 1)
            require(canary not in json.dumps(dirty), 'terminal record re-emits the value')
        return {'safe_shapes': ['sha256', 'int', 'bool', 'null'], 'report_scanned_separately': True}
    suite.case('final_record_structurally_safe', structural)

    def exact_keys():
        allowed = ['alpha', 'beta']
        require(publication.safe_record({'alpha': '0'*64, 'beta': 1}, allowed))
        require(not publication.safe_record({'alpha': '0'*64}, allowed), 'missing key accepted')
        require(not publication.safe_record({'alpha': '0'*64, 'beta': 1, 'extra': True}, allowed), 'extra key accepted')
        require(not publication.safe_record({canary: True}, allowed), 'canary key accepted')
        require(not publication.safe_record({'alpha': 'free text', 'beta': 1}, allowed), 'free text accepted')
        require(not publication.safe_record({'alpha': ['x'], 'beta': 1}, allowed), 'list value accepted')
        return {'enforced': 'exact key set plus digest/int/bool/null values'}
    suite.case('safe_record_exact_keys', exact_keys)

    def order():
        require(publication.FINALIZATION == ('artifacts', 'scan', 'scan_report', 'report_scan', 'terminal_event', 'seal'))
        source = (r6.ROOT/'credential_episode.py').read_text()
        body = source[source.index('def finalize('):source.index('def seal(')]
        positions = [body.index(marker) for marker in
                     ['publication.scan(', "'publication-scan.json'", 'publication.final_record(',
                      "'publication-final.json'", 'events.append(', 'seal(run']]
        require(positions == sorted(positions), 'finalization writes are out of declared order')
        require('safe_record(payload, publication.TERMINAL_KEYS)' in body, 'terminal receipt is not key-restricted')
        return {'order': list(publication.FINALIZATION), 'post_scan_writes': 'exact key set of digests, counts, booleans'}
    suite.case('finalization_order_declared', order)

    def exact_receipt():
        expected = credential.commitment(canary)
        for value, ok in [(header, True), (credential_http.WRONG, False), (header+' ', False), (None, False)]:
            observed = None if value is None else r6.hashlib.sha256(value.encode()).hexdigest()
            require((observed == expected) is ok, 'receipt comparison is not exact')
        require(credential_http.authorization('missing_credential', canary) is None)
        require(credential_http.authorization('wrong_credential', canary) == credential_http.WRONG)
        require(credential_http.authorization('valid', header) == header)
        return {'presence_bit_sufficient': False, 'declared_wrong_value': credential_http.WRONG}
    suite.case('receipt_requires_exact_value', exact_receipt)

    def derived_expectation():
        record = credential.record(seed)
        require(credential.commitment(credential.derive(record['nonce'])) == record['authorization_sha256'])
        forged = {**record, 'authorization_sha256': '0'*64}
        require(credential.commitment(credential.derive(forged['nonce'])) != forged['authorization_sha256'])
        return {'source': 'retained nonce and frozen generator'}
    suite.case('receipt_expectation_derived', derived_expectation)

    def lock_guard():
        original = r6.sha
        def changed(path): return '0'*64 if Path(path) == r6.ROOT/'credential_http.py' else original(path)
        with mock.patch.object(r6, 'sha', side_effect=changed):
            return rejected(contract.verify_sources, 'frozen source revision')
    suite.case('source_lock_guard', lock_guard)
    suite.case('missing_case_rejected', lambda: rejected(lambda: assert_complete(['a'], ['a', 'b']), 'missing'))
    suite.case('duplicate_case_rejected', lambda: rejected(lambda: assert_complete(['a', 'a'], ['a']), 'duplicate'))
    suite.finish()


def native(root):
    suite = Suite(root/'credential-native.json', NATIVE_CASES)
    expected = {'valid': (True, True, True, None),
                'http503': (False, True, True, 'provider_http_error'),
                'missing_credential': (False, False, True, 'credential_receipt_failure'),
                'wrong_credential': (False, False, True, 'credential_receipt_failure'),
                'reflected_canary': (False, True, False, 'provider_http_error')}
    for name in NATIVE_CASES:
        control, case = name.split('_', 1)
        task = r6.D1 if control == 'd1' else r6.C8

        def test(name=name, case=case, task=task):
            target = root/name
            command = [sys.executable, str(r6.ROOT/'credential_episode.py'), 'run', '--task', task.id,
                       '--case', case, '--run-dir', str(target)]
            if contract.CONFIG.parent != r6.ROOT/'policies':
                command += ['--development-policy-dir', str(contract.CONFIG.parent)]
            with (root/(name+'.log')).open('w') as log:
                subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
            require((target/'seal.json').exists(), name+' produced no sealed episode; see its log')
            result = auditor.audit(target, task)
            accept, receipt_ok, publish_ok, category = expected[case]
            require((result['accepted'], result['credential_receipt_accepted'],
                     result['publication_accepted']) == (accept, receipt_ok, publish_ok), str(result))
            require(result['failure_category'] == category, str(result))
            scan = r6.read_json(target/'publication-scan.json')
            nonce = r6.read_json(target/'credential-canary.json')['nonce']
            if case == 'reflected_canary':
                paths = {h['path'] for h in scan['disclosures']}
                require('stages/proposal-1/output/provider-response.json' in paths, 'reflection precondition absent')
                require(result['proof_accepted'] is False and not (target/'verdict.json').exists())
            else:
                require(scan['disclosures'] == [] and scan['incompletely_scanned'] == [])
            require(scan['unreadable_directories'] == [] and scan['irregular_entries'] == [])
            if case == 'valid':
                verdict = r6.read_json(target/'verdict.json')
                require(all(not d['added'] and not d['removed'] for d in verdict['axiom_delta'].values()))
            # The outer process log is publication surface the episode cannot scan.
            outer = publication.scan([root/(name+'.log')], credential.derive(nonce), nonce)
            require(outer['accepted'], 'the episode log discloses the canary')
            return {'accepted': result['accepted'], 'credential_receipt_accepted': result['credential_receipt_accepted'],
                    'publication_accepted': result['publication_accepted'], 'failure_category': category,
                    'files_scanned': result['files_scanned'], 'coverage': result['coverage'],
                    'disclosures': len(scan['disclosures']), 'outer_log_clean': True,
                    'seal_sha256': r6.sha(target/'seal.json')}
        suite.case(name, test)
    suite.finish()


def retained_copy(source, destination):
    seal = r6.read_json(source/'seal.json')
    for name in ['seal.json', *seal['retained_sha256']]:
        p = destination/name
        p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source/name, p)


def reseal(root, accepted, ephemeral):
    rows = events.read(root/'events.ndjson')
    (root/'events.ndjson').write_bytes(rehash(rows))
    harness.seal(root, accepted, ephemeral)


def recompute_publication(root, accepted, ephemeral):
    """Reseal a mutation the way the episode would: rescan, recommit, reseal.

    The scan runs over the tree without its terminal receipt, exactly as the
    episode's does, so stale scan provenance is never the detector.
    """
    nonce = r6.read_json(root/'credential-canary.json')['nonce']
    canary = credential.derive(nonce)
    rows = events.read(root/'events.ndjson')
    terminal = rows.pop()
    for name in ('publication-scan.json', 'publication-final.json', 'seal.json'):
        (root/name).unlink()
    (root/'events.ndjson').write_bytes(rehash(rows))
    r6.write_json(root/'publication-scan.json', publication.scan([root], canary, nonce))
    r6.write_json(root/'publication-final.json',
                  publication.final_record(root/'publication-scan.json', canary, nonce))
    terminal['payload'].update(summary_sha256=r6.sha(root/'credential-summary.json'),
                               publication_scan_sha256=r6.sha(root/'publication-scan.json'),
                               publication_final_sha256=r6.sha(root/'publication-final.json'))
    rows.append(terminal)
    (root/'events.ndjson').write_bytes(rehash(rows))
    harness.seal(root, accepted, ephemeral)


def audits(root):
    suite = Suite(root/'credential-audits.json', AUDIT_CASES)

    def standalone(name, task, accepted):
        with tempfile.TemporaryDirectory(prefix='r6-credential-publication-') as directory:
            copied = Path(directory)
            retained_copy(root/name, copied)
            result = auditor.audit(copied, task)
            require(result['accepted'] is accepted, str(result))
            return {'accepted': result['accepted'], 'publication_accepted': result['publication_accepted'],
                    'retained_files': len(r6.read_json(copied/'seal.json')['retained_sha256']),
                    'coverage': result['coverage']}
    suite.case('d1_retained_only', lambda: standalone('d1_valid', r6.D1, True))

    def reflected():
        result = standalone('d1_reflected_canary', r6.D1, False)
        require(result['publication_accepted'] is False)
        return {**result, 'scope': 'sealed evidence preserved through a publication rejection'}
    suite.case('reflected_canary_audited', reflected)

    def mutate(name, change, contains, *, source='d1_valid', accepted=False, deep=False):
        def test():
            with tempfile.TemporaryDirectory(prefix='r6-credential-mutation-') as directory:
                copied = Path(directory)
                original = r6.read_json(root/source/'seal.json')
                retained_copy(root/source, copied)
                before = {str(p.relative_to(copied)): r6.sha(p) for p in copied.rglob('*') if p.is_file()}
                change(copied)
                after = {str(p.relative_to(copied)): r6.sha(p) for p in copied.rglob('*') if p.is_file()}
                require(before != after, 'corruption matched nothing')
                (recompute_publication if deep else reseal)(copied, accepted, original['ephemeral_sha256'])
                result = rejected(lambda: auditor.audit(copied, r6.D1), contains)
                return {**result, 'coherently_resealed': True,
                        'changed_artifacts': sorted(k for k in before.keys() | after.keys() if before.get(k) != after.get(k))}
        suite.case(name, test)

    def edit(root_dir, name, change):
        value = r6.read_json(root_dir/name)
        change(value)
        r6.write_json(root_dir/name, value)

    def canary_of(copied):
        return credential.derive(r6.read_json(copied/'credential-canary.json')['nonce'])

    def inject_log(copied):
        target = copied/'stages/proposal-1/supervisor.stderr'
        require(target.exists(), 'no ordinary log to taint')
        target.write_bytes(target.read_bytes()+b'\nAuthorization: '+credential.header(canary_of(copied)).encode()+b'\n')
    mutate('injected_log_leak', inject_log, 'recorded findings differ')

    def inject_metadata(copied):
        edit(copied, 'provider-metadata.json',
             lambda v: v.update(identity_scope={'nested': {'header': credential.header(canary_of(copied))}}))
    mutate('injected_metadata_leak', inject_metadata, 'recorded findings differ')

    def inject_gzip(copied):
        target = copied/'solution.ndjson.gz'
        require(target.exists(), 'no compressed artifact to taint')
        plain = gzip.decompress(target.read_bytes())
        with gzip.open(target, 'wb') as handle:
            handle.write(plain+b'{"leak":"'+canary_of(copied).encode()+b'"}\n')
    mutate('injected_gzip_leak', inject_gzip, 'recorded findings differ')

    mutate('missing_scanner', lambda c: (c/'publication-scan.json').unlink(), 'not retained')

    def omit_target(copied):
        report = r6.read_json(copied/'publication-scan.json')
        dropped = next(e for e in report['inventory'] if e['path'] == 'accounting.json')
        report['inventory'].remove(dropped)
        report['files_scanned'] -= 1
        r6.write_json(copied/'publication-scan.json', report)
    mutate('omitted_scan_target', omit_target, 'omits a publication target')

    def forge_report(copied):
        report = r6.read_json(copied/'publication-scan.json')
        require(report['disclosures'], 'forgery precondition absent: no genuine disclosure')
        require(any(e['findings'] for e in report['inventory']), 'no inventory finding to contradict')
        report['disclosures'] = []
        report['accepted'] = True
        r6.write_json(copied/'publication-scan.json', report)
    mutate('forged_passing_report', forge_report, 'reported disclosures differ', source='d1_reflected_canary')

    def forge_receipt(copied):
        edit(copied, 'credential-receipt.json',
             lambda v: v.update(expected_authorization_sha256='0'*64, observed_authorization_sha256='0'*64))
    mutate('forged_receipt_digest', forge_receipt, 'credential receipt differs')

    def forge_provenance(copied):
        report = r6.read_json(copied/'publication-scan.json')
        entry = next(e for e in report['inventory'] if e['path'] == 'accounting.json')
        entry['sha256'], entry['bytes'] = '0'*64, 987654321
        r6.write_json(copied/'publication-scan.json', report)
    mutate('forged_scan_hash_and_size', forge_provenance, 'scan provenance differs')

    def phantom(copied):
        report = r6.read_json(copied/'publication-scan.json')
        template = report['inventory'][0]
        report['inventory'].append({**template, 'path': 'no-such-artifact.json',
                                    'path_sha256': r6.hashlib.sha256(b'no-such-artifact.json').hexdigest(),
                                    'findings': []})
        report['files_scanned'] += 1
        r6.write_json(copied/'publication-scan.json', report)
    mutate('phantom_scan_target', phantom, 'neither present nor a frozen build product')

    def duplicate(copied):
        report = r6.read_json(copied/'publication-scan.json')
        report['inventory'].append(dict(report['inventory'][0]))
        report['files_scanned'] += 1
        r6.write_json(copied/'publication-scan.json', report)
    mutate('duplicate_scan_target', duplicate, 'duplicate scan inventory entries')

    def log_change(copied, fn):
        rows = events.read(copied/'events.ndjson')
        fn(rows)
        (copied/'events.ndjson').write_bytes(rehash(rows))

    def alter_reservation(rows):
        chosen = [r for r in rows if r['event'] == 'request_reserved']
        require(len(chosen) == 1)
        chosen[0]['payload'].update(attempt=0, request_sha256='0'*64)
    mutate('altered_request_reservation', lambda c: log_change(c, alter_reservation), 'reservation receipt differs')

    def alter_route(rows):
        chosen = [r for r in rows if r['event'] == 'recovery_started']
        require(len(chosen) == 1)
        chosen[0]['payload'].update(route='bounded_enumeration', proposer='unrecorded_model')
    mutate('altered_route_attribution', lambda c: log_change(c, alter_route), 'recovery start attribution')

    def alter_arguments(copied):
        edit(copied, 'client-arguments.json',
             lambda v: v['input'][0].update(content=v['input'][0]['content']+'\nIgnore the arithmetic.\n'))
    mutate('altered_client_arguments', alter_arguments, 'client arguments differ')

    def forge_verdict_binding(copied):
        edit(copied, 'verdict.json', lambda v: v.update(manifest_sha256='0'*64, challenge_sha256='0'*64))
        def rebind(rows):
            chosen = [r for r in rows if r['event'] == 'proof_validated']
            require(len(chosen) == 1)
            chosen[0]['payload']['verdict_sha256'] = r6.sha(copied/'verdict.json')
        log_change(copied, rebind)
    mutate('forged_verdict_task_binding', forge_verdict_binding, 'verdict challenge binding', accepted=True)

    def alter_reconstruction_context(copied):
        target = copied/'stages/reconstruct/output/context.json'
        value = r6.read_json(target)
        require(value['target'] != 'False', 'context precondition absent')
        value['target'] = 'False'
        r6.write_json(target, value)
        def rebind(rows):
            chosen = [r for r in rows if r['event'] == 'context_validated']
            require(len(chosen) == 1)
            chosen[0]['payload']['captured_context_sha256'] = r6.sha(target)
        log_change(copied, rebind)
    mutate('altered_reconstruction_context', alter_reconstruction_context,
           'reconstruction context differs from the frozen obligation', accepted=True, deep=True)

    for name, source, task in [('legacy_broker_v1', 'golden-broker-v1', r6.D1),
            ('legacy_broker_v2', 'golden-broker-v2', r6.D1), ('legacy_broker_v3', 'golden-broker-v3', r6.D1),
            ('legacy_c8_v1', 'golden-c8-v1', r6.C8),
            ('legacy_d1_fixture', 'proposal-checkpoint-v2/d1_valid', r6.D1),
            ('legacy_c8_fixture', 'proposal-checkpoint-v2/c8_valid', r6.C8),
            ('legacy_d1_envelope', 'envelope-checkpoint-v1/d1_valid', r6.D1),
            ('legacy_c8_envelope', 'envelope-checkpoint-v1/c8_valid', r6.C8),
            ('legacy_alternate_envelope', 'envelope-checkpoint-v1/d1_alternate_encoding', r6.D1),
            ('legacy_d1_provider', 'provider-checkpoint-v1/d1_valid', r6.D1),
            ('legacy_c8_provider', 'provider-checkpoint-v1/c8_valid', r6.C8),
            ('legacy_alternate_provider', 'provider-checkpoint-v1/d1_alternate_encoding', r6.D1)]:
        def historical(source=source, task=task):
            check = (provider_audit.audit if source.startswith('provider-')
                     else envelope_audit.audit if source.startswith('envelope-') else episode.audit)
            return {'accepted': check(r6.ROOT/'runs'/source, task)['accepted']}
        suite.case(name, historical)

    def preservation():
        values = r6.read_json(root/'prior-artifacts.sha256.json')
        require(all((instrument.REPO/p).is_file() and r6.sha(instrument.REPO/p) == h for p, h in values.items()),
                'a pre-existing artifact changed')
        return {'checked_files': len(values), 'changed': 0, 'missing': 0, 'git_base': BASE}
    suite.case('prior_artifacts_preserved', preservation)
    suite.finish()


def gates(root):
    """Both gates run against the finished three-suite checkpoint.

    The publication probes call `publication_gate`, which reads no suite file;
    the contract probes call the full `recount`. Every probe first requires the
    unmutated copy to pass, so no gate is weakened to make a baseline succeed.
    """
    suite = Suite(root/GATES_FILE, GATE_CASES)
    module = load_recount()

    def probe(name, change, contains, complete):
        def test():
            with tempfile.TemporaryDirectory(prefix='r6-credential-gate-') as directory:
                copied = Path(directory)/'checkpoint'
                shutil.copytree(root, copied)
                gate = module.recount if complete else module.publication_gate
                gate(copied)
                change(copied)
                result = rejected(lambda: gate(copied), contains)
                return {**result, 'gate': 'complete_checkpoint' if complete else 'publication',
                        'unmutated_copy_passes': True}
        suite.case(name, test)

    def drop_episode(copied):
        shutil.rmtree(copied/'d1_http503')
        (copied/'d1_http503.log').unlink()
    probe('recount_missing_episode', drop_episode, 'episode population differs', False)
    probe('recount_missing_log', lambda c: (c/'d1_valid.log').unlink(), 'missing episode process log', False)

    def suite_leak(copied):
        nonce = r6.read_json(copied/'d1_valid/credential-canary.json')['nonce']
        value = r6.read_json(copied/'credential-native.json')
        value['operator_note'] = 'Authorization: '+credential.header(credential.derive(nonce))
        r6.write_json(copied/'credential-native.json', value)
    probe('recount_suite_artifact_leak', suite_leak, 'unexpected canary disclosure', False)

    def incomplete_status(copied):
        index = r6.read_json(copied/'checkpoint.json')
        index['passed'] = False
        r6.write_json(copied/'checkpoint.json', index)
    probe('recount_incomplete_status', incomplete_status, 'checkpoint is not marked complete', True)

    def substitute_episode(copied):
        # An internally valid episode under another control's expected name.
        shutil.rmtree(copied/'d1_missing_credential')
        shutil.copytree(copied/'d1_valid', copied/'d1_missing_credential')
        shutil.copyfile(copied/'d1_valid.log', copied/'d1_missing_credential.log')
    probe('recount_substituted_episode', substitute_episode,
          'episode directory holds a different canned case', True)

    def incomplete_case_set(copied):
        value = r6.read_json(copied/'credential-units.json')
        dropped = next(c for c in value['checks'] if c['name'] == 'scan_unreadable_directory')
        value['checks'].remove(dropped)
        value['expected_cases'] = [n for n in value['expected_cases'] if n != dropped['name']]
        value['check_count'] = len(value['checks'])
        r6.write_json(copied/'credential-units.json', value)
        index = r6.read_json(copied/'checkpoint.json')
        index['suites']['credential-units.json'] = {'sha256': r6.sha(copied/'credential-units.json'),
                                                    'count': value['check_count']}
        r6.write_json(copied/'checkpoint.json', index)
    probe('recount_incomplete_case_set', incomplete_case_set,
          'suite case set differs from the frozen module', True)
    suite.finish()


def load_recount():
    import importlib.util
    path = r6.ROOT/'reviews/2026-09-09/credential_final_checks.py'
    spec = importlib.util.spec_from_file_location('credential_final_checks', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def snapshot(root):
    records = {}
    paths = r6.command(['git', '-C', instrument.REPO, 'ls-tree', '-r', '--name-only', BASE,
        'experiments/r6/tasks', 'experiments/r6/runs', 'experiments/r6/policies', 'experiments/r6/schema',
        'experiments/r6/prompts', 'experiments/c1-cert-recovery']).splitlines()
    for path in paths:
        content = subprocess.check_output(['git', '-C', str(instrument.REPO), 'show', BASE+':'+path])
        records[path] = r6.hashlib.sha256(content).hexdigest()
    r6.write_json(root/'prior-artifacts.sha256.json', records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--units-only', action='store_true')
    parser.add_argument('--development-policy-dir', type=Path)
    args = parser.parse_args()
    if args.development_policy_dir: contract.development(args.development_policy_dir)
    root = args.run_dir.resolve()
    root.mkdir(parents=True, exist_ok=False)
    r6.write_json(root/'checkpoint.json', {'passed': False})
    units(root)
    if args.units_only:
        return
    snapshot(root)
    native(root)
    audits(root)
    write_checkpoint(root)
    gates(root)
    write_checkpoint(root, gates_recorded=True)


def write_checkpoint(root, gates_recorded=False):
    index = {'passed': True, 'live_model_calls': 0,
        'scope': 'synthetic canary over an isolated local HTTP fixture; no real credential, TLS, '
                 'remote receipt, compilation or inference attestation',
        'canary_derivation': credential.DOMAIN, 'policy_sha256': r6.sha(contract.CONFIG),
        'source_lock_sha256': r6.sha(contract.LOCK),
        'publication_representations': list(publication.REPRESENTATIONS),
        'publication_encoded_forms': list(publication.FORMS),
        'suites': {name: {'sha256': r6.sha(root/name), 'count': r6.read_json(root/name)['check_count']}
                   for name in SUITE_CASES}}
    if gates_recorded:
        index['gates'] = {'sha256': r6.sha(root/GATES_FILE),
                          'count': r6.read_json(root/GATES_FILE)['check_count'],
                          'scope': 'gate probes run against this checkpoint before this record existed'}
    r6.write_json(root/'checkpoint.json', index)


if __name__ == '__main__':
    main()

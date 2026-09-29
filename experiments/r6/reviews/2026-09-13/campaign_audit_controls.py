#!/usr/bin/env python3
"""Controls for the R6-008 campaign auditor: single-relationship mutations on copies.

Runs and the rehearsal ledger are copied together, so shared-ledger relationships
are exercised on the copy. Mutations that would be caught first by the
reconciliation evidence digests are tested at the predicate level instead, so
each named case is shown to reject on its own relationship.
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
import campaign_episode as driver
import campaign_ledger as ledger
import credential
import events
import publication
import run as r6


def load_module(name):
    spec = importlib.util.spec_from_file_location('r6_review_'+name, Path(__file__).with_name(name+'.py'))
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


audit = load_module('campaign_audit')
HERE = Path(__file__).resolve().parent
RUNS = ROOT/'campaign-runs-v7'
J = lambda p: json.loads(Path(p).read_bytes())
W = lambda p, v: Path(p).write_bytes(events.canonical(v)+b'\n')
EXPECTED = {
    'run_added': 'population:exactly_three_runs',
    'failure_run_unsealed': 'rehearsal-1:seal:retained_hashes',
    'retained_policy_live_enabled': 'rehearsal-3:versions:policy_lock_sources_bound',
    'duplicate_receipt_added': 'rehearsal-3:chain:expected_sequence',
    'attribution_retrofitted': 'rehearsal-3:proof:attribution_passed_through',
    'outbound_altered': 'rehearsal-3:transport:local_send_and_remote_receipt',
    'invalid_proof_export': 'rehearsal-3:proof:shared_checker',
    'shared_ledger_truncated': 'shared_ledger:rows_present_and_consistent',
    'shared_ledger_missing_reconciliation': 'shared_ledger:rows_present_and_consistent',
    'grant_file_altered': 'rehearsal-3:ledger:permit_and_reconciliation_bound',
    'http_record_altered': 'rehearsal-3:ledger:permit_and_reconciliation_bound',
    'reservation_rebound': 'rehearsal-3:ledger:permit_and_reconciliation_bound',
    # the second review's four auditor gaps
    'source_lock_rebound': 'rehearsal-3:versions:policy_lock_sources_bound',
    'publication_scan_rejected': 'rehearsal-3:publication:recomputed',
    'disclosure_overridden_by_terminal': 'rehearsal-3:publication:recomputed',
    'false_terminal_summary_digest': 'rehearsal-3:terminal:commitments_bound',
    'retained_module_altered': 'modules:bound_to_retained_copies',
    'file_added_after_sealing': 'rehearsal-1:seal:retained_hashes',
    'slot_marker_removed': 'rehearsal-1:slot:authoritative_matches_retained',
    # the third review's auditor gaps, applied with the review's own mutation code
    'release_despite_live_workload': 'rehearsal-1:ledger:disposition_derived',
    'authoritative_grant_altered': 'rehearsal-3:ledger:disposition_derived',
    'authoritative_marker_altered': 'rehearsal-1:slot:authoritative_matches_retained',
    'ledger_mount_changed': 'rehearsal-3:mounts:authority_bound',
    'grant_mount_changed': 'rehearsal-3:mounts:authority_bound',
    'scan_event_hash_forged': 'rehearsal-3:publication:recomputed',
    'scan_event_length_forged': 'rehearsal-3:publication:recomputed',
    'retained_campaign_module_altered_current_revision': 'modules:campaign_revision',
    # the fourth review's auditor gaps
    'retained_episode_module_altered': 'modules:campaign_revision',
    'scan_stream_mutation': 'rehearsal-3:publication:recomputed',
    'marker_digest_rebound': 'rehearsal-1:slot:authoritative_matches_retained',
    'attempt_identity_rebound': 'rehearsal-3:ledger:permit_and_reconciliation_bound',
    # the fifth review's auditor gaps
    'attempt_event_removed': 'rehearsal-3:chain:expected_sequence',
    'attempt_field_removed': 'rehearsal-3:ledger:permit_and_reconciliation_bound',
    'attempt_identity_removed': 'rehearsal-3:chain:expected_sequence',
    'attempt_identity_empty': 'rehearsal-3:ledger:permit_and_reconciliation_bound',
    'summary_evidence_contradiction': 'rehearsal-3:terminal:commitments_bound',
    'torn_marker_receipt': 'rehearsal-1:slot:authoritative_matches_retained',
    # the sixth review's summary bindings, kept as three separate mutations
    'summary_nested_evidence': 'rehearsal-3:summary:bound_to_audited_records',
    'summary_nested_allowance': 'rehearsal-3:summary:bound_to_audited_records',
    'summary_task_identity': 'rehearsal-3:summary:bound_to_audited_records',
}
LAYOUT_POSITIVE = 'repeated_marker_recovery_layout_accepted'
PREDICATE = {'grant_out_of_order': 'rehearsal-3:grant:ordered_before_first_header_byte',
             'commitment_mismatch': 'rehearsal-3:commitment:bound_to_mounted_canary',
             'receipt_disagrees_with_process': 'rehearsal-3:receipts:single_pair_bound_to_process',
             'missing_durability_field': 'rehearsal-3:grant:consistent_with_outcome'}


def run_audit(root, ledgers):
    try: result = audit.audit(root, ledgers)
    except audit.Rejection as rejection:
        return {'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}
    return {'accepted': result['accepted'], 'case_count': result['case_count']}


def rechain(run, rows):
    previous = '0'*64
    for i, row in enumerate(rows):
        row.update(sequence=i, previous_hash=previous); row.pop('event_hash', None)
        row['event_hash'] = events.digest(row); previous = row['event_hash']
    (run/'events.ndjson').write_bytes(b''.join(events.canonical(r)+b'\n' for r in rows))


def refinalize(run, change):
    """Drop the terminal event, apply one change, regenerate scan, terminal event and seal with the real finalizer."""
    rows = events.read(run/'events.ndjson'); live = J(run/'search-policy.json')['mode'] == 'live'
    assert rows[-1]['event'] in ('episode_finished', 'episode_rejected'); rows.pop()
    change(run, rows); rechain(run, rows)
    for n in ('publication-scan.json', 'publication-final.json', 'seal.json'): (run/n).unlink()
    nonce = J(run/'credential-canary.json')['nonce']
    driver.finalize(run, credential.derive(nonce), nonce, J(run/'credential-summary.json'), live)


def mutate(root, ledgers, name):
    r3 = root/'rehearsal-3'; digest = J(r3/'search-policy.json')['config_sha256']
    shared = ledgers/'rehearsal'/(digest+'.ndjson')
    if name == 'run_added': shutil.copytree(r3, root/'rehearsal-4')
    elif name == 'failure_run_unsealed': (root/'rehearsal-1/seal.json').unlink()
    elif name == 'retained_policy_live_enabled':
        def change(run, rows):
            p = next((run/'provenance/campaign-harness/policies').glob('responses-campaign-v*.json')); v = J(p); v['live_enabled'] = True; W(p, v)
        refinalize(r3, change)
    elif name == 'duplicate_receipt_added':
        def change(run, rows):
            i = next(i for i, r in enumerate(rows) if r['stage'] == 'proposal-1' and r['event'] == 'stage_finished')
            rows.insert(i+1, json.loads(json.dumps(rows[i])))
        refinalize(r3, change)
    elif name == 'attribution_retrofitted':
        def change(run, rows):
            next(r for r in rows if r['event'] == 'recovery_finished')['payload']['proposer'] = 'live_model_response'
        refinalize(r3, change)
    elif name == 'outbound_altered':
        def change(run, rows):
            p = run/'stages/proposal-1/output/outbound-body.json'; p.write_bytes(p.read_bytes()+b' ')
        refinalize(r3, change)
    elif name == 'invalid_proof_export':
        import gzip
        def change(run, rows): (run/'solution.ndjson.gz').write_bytes(gzip.compress(b'invalid proof export\n', mtime=0))
        refinalize(r3, change)
    elif name == 'shared_ledger_truncated':
        p = shared; lines = p.read_bytes().splitlines(True); p.write_bytes(b''.join(lines[:-1]))
    elif name == 'shared_ledger_missing_reconciliation':
        p = shared; lines = p.read_bytes().splitlines(True)
        head = p.with_name(p.name.replace('.ndjson', '.head.json'))
        kept = lines[:-1]; p.write_bytes(b''.join(kept))
        rows = [json.loads(l) for l in kept]; W(head, {'policy_sha256': rows[0]['policy_sha256'], 'rows': len(rows), 'last_hash': rows[-1]['row_hash']})
    elif name == 'grant_file_altered':
        def change(run, rows):
            p = run/'stages/proposal-1/grant/send-grant.json'; v = J(p); v['at_ns'] += 1; W(p, v)
        refinalize(r3, change)
    elif name == 'http_record_altered':
        def change(run, rows):
            p = run/'stages/proposal-1/output/http.json'; v = J(p); v['credential_commitment_sha256'] = '0'*64; W(p, v)
        refinalize(r3, change)
    elif name == 'reservation_rebound':
        def change(run, rows):
            p = run/'reservation.json'; v = J(p); v['reserved_micro_usd'] = 1; W(p, v)
        refinalize(r3, change)
    elif name == 'source_lock_rebound':
        def change(run, rows):
            ph = run/'provenance/campaign-harness'; p = ph/'campaign_https.py'; p.write_bytes(p.read_bytes()+b'\n# altered source without changing policy\n')
            lock = next(ph.glob('policies/campaign-harness-v*.sha256.json')); v = J(lock); v['campaign_https.py'] = r6.sha(p); W(lock, v)
            sp = J(run/'search-policy.json'); sp['source_lock_sha256'] = r6.sha(lock); W(run/'search-policy.json', sp)
            rows[0]['payload']['policy_sha256'] = r6.sha(run/'search-policy.json')
        refinalize(r3, change)
    elif name == 'publication_scan_rejected':
        rows = events.read(r3/'events.ndjson')
        p = r3/'publication-scan.json'; v = J(p); assert v['accepted'] is True; v['accepted'] = False; W(p, v)
        rows[-1]['payload']['publication_scan_sha256'] = r6.sha(p); rechain(r3, rows); driver.publication_driver.seal(r3, True)
    elif name == 'disclosure_overridden_by_terminal':
        def change(run, rows):
            nonce = J(run/'credential-canary.json')['nonce']; (run/'synthetic-disclosure.txt').write_text(credential.header(credential.derive(nonce)))
        refinalize(r3, change)
        scan = J(r3/'publication-scan.json'); assert scan['accepted'] is False and scan['disclosures']
        rows = events.read(r3/'events.ndjson'); assert rows[-1]['event'] == 'episode_rejected'
        rows[-1]['event'] = 'episode_finished'; rows[-1]['payload'].update(accepted=True, publication_accepted=True)
        rechain(r3, rows); driver.publication_driver.seal(r3, True)
    elif name == 'false_terminal_summary_digest':
        rows = events.read(r3/'events.ndjson'); rows[-1]['payload']['summary_sha256'] = '0'*64
        rechain(r3, rows); driver.publication_driver.seal(r3, True)
    elif name == 'retained_module_altered':
        def change(run, rows):
            p = run/'provenance/harness/events.py'; p.write_bytes(p.read_bytes()+b'\n# altered retained checker module\n')
        refinalize(r3, change)
    elif name == 'file_added_after_sealing':
        (root/'rehearsal-1/added-later.json').write_bytes(b'{}\n')
    elif name == 'slot_marker_removed':
        for slot in (ledgers/'rehearsal'/(digest+'.slots')).iterdir():
            for marker in slot.iterdir(): marker.unlink()
    elif name == 'release_despite_live_workload': false_termination(root, ledgers)
    elif name == 'authoritative_grant_altered': authority_slot(root, ledgers)
    elif name == 'authoritative_marker_altered':  # the ledger-side release marker, which no evidence digest covers
        permit = J(root/'rehearsal-1/campaign-permit.json'); marker = ledgers/'rehearsal'/(digest+'.slots')/permit['reservation_id']/'release.json'
        v = J(marker); v['row_hash'] = '0'*64; W(marker, v)
    elif name == 'ledger_mount_changed': mount_change(root, ledgers, '/ledger.ndjson')
    elif name == 'grant_mount_changed': mount_change(root, ledgers, '/grant')
    elif name == 'scan_event_hash_forged': scan_metadata(root, ledgers, 'sha256')
    elif name == 'scan_event_length_forged': scan_metadata(root, ledgers, 'bytes')
    elif name == 'retained_campaign_module_altered_current_revision':
        def change(run, rows):
            p = run/'provenance/campaign-harness/campaign_ledger.py'; p.write_bytes(p.read_bytes()+b'\n# altered retained campaign module\n')
        refinalize(r3, change)
    elif name == 'retained_episode_module_altered':
        def change(run, rows):
            p = run/'provenance/campaign-harness/campaign_episode.py'; p.write_bytes(p.read_bytes()+b'\n# altered accounting source\n')
        refinalize(r3, change)
    elif name == 'scan_stream_mutation':
        run = r3; path = run/'publication-scan.json'; report = J(path)
        entry = next(e for e in report['inventory'] if e['path'] == 'solution.ndjson.gz'); assert 'gzip' in entry['streams']
        entry['streams'] = ['raw']; report['gzip_streams_scanned'] -= 1; W(path, report)
        nonce = J(run/'credential-canary.json')['nonce']; W(run/'publication-final.json', publication.final_record(path, credential.derive(nonce), nonce))
        rows = events.read(run/'events.ndjson')
        rows[-1]['payload'].update(publication_scan_sha256=r6.sha(path), publication_final_sha256=r6.sha(run/'publication-final.json'))
        rechain(run, rows); driver.publication_driver.seal(run, True)
    elif name == 'marker_digest_rebound':  # the authoritative release marker rewritten coherently except for the row's digest of it
        permit = J(root/'rehearsal-1/campaign-permit.json'); marker = ledgers/'rehearsal'/(digest+'.slots')/permit['reservation_id']/'release.json'
        v = J(marker); v['reconciled_at_unix'] += 1; W(marker, v); shutil.copyfile(marker, root/'rehearsal-1/stages/proposal-1/grant/release.json')
        rows = events.read(root/'rehearsal-1/events.ndjson'); rechain(root/'rehearsal-1', rows); driver.publication_driver.seal(root/'rehearsal-1', False)
    elif name == 'attempt_identity_rebound':
        def change(run, rows):
            next(r for r in rows if r['event'] == 'reservation_attempted')['payload']['attempt_id'] = 'f'*64
        refinalize(r3, change)
    elif name in ('attempt_event_removed', 'attempt_field_removed', 'attempt_identity_removed', 'attempt_identity_empty'):
        rewrite_attempt_identity(root, ledgers, name)
    elif name == 'summary_evidence_contradiction':  # the summary mirror flipped; terminal claims restored to success and resealed
        def change(run, rows):
            p = run/'credential-summary.json'; v = J(p); assert v['evidence_complete'] is True; v['evidence_complete'] = False; W(p, v)
        refinalize(r3, change)
        rows = events.read(r3/'events.ndjson'); assert rows[-1]['event'] == 'episode_rejected'
        rows[-1]['event'] = 'episode_finished'; rows[-1]['payload'].update(accepted=True, evidence_complete=True)
        rechain(r3, rows); driver.publication_driver.seal(r3, True)
    elif name == 'torn_marker_receipt':  # the authoritative release receipt replaced by seven bytes, its digest rebound everywhere coherently
        run = root/'rehearsal-1'; permit = J(run/'campaign-permit.json'); book = ledger.Ledger(ledgers/'rehearsal', digest)
        marker = book.slot(permit['reservation_id'])/'release.json'; torn = marker.read_bytes()[:7]
        marker.write_bytes(torn); (run/'stages/proposal-1/grant/release.json').write_bytes(torn)
        rebind_rows(root, ledgers, digest, lambda row: row.update(marker_sha256=r6.sha(marker)) if row.get('kind') == 'release' and row['reservation_id'] == permit['reservation_id'] else None)
    elif name in ('summary_nested_evidence', 'summary_nested_allowance', 'summary_task_identity'):
        def change(run, rows):
            p = run/'credential-summary.json'; v = J(p)
            if name == 'summary_nested_evidence': assert v['accounting']['evidence_complete'] is True; v['accounting']['evidence_complete'] = False
            elif name == 'summary_nested_allowance': assert v['accounting']['allowance_consumed'] == 1; v['accounting']['allowance_consumed'] = 0
            else: assert v['task_id'] == 'verinf-d1-70'; v['task_id'] = 'c1-c8-2p18'
            W(p, v)
        refinalize(r3, change)
    else: raise AssertionError(name)


def rebind_rows(root, ledgers, digest, mutate_row):
    """Apply one row mutation to the shared ledger and rehash every mirror coherently (the review's false_termination discipline)."""
    book = ledger.Ledger(ledgers/'rehearsal', digest)
    all_rows = ledger.parse(book.path.read_bytes()); replacements = {}; previous = '0'*64
    for row in all_rows:
        old = row['row_hash']; mutate_row(row)
        row['previous_hash'] = previous; row.pop('row_hash'); row['row_hash'] = ledger.digest(row); previous = row['row_hash']; replacements[old] = row
    book.path.write_bytes(b''.join(events.canonical(r)+b'\n' for r in all_rows))
    W(book.head, {'policy_sha256': digest, 'rows': len(all_rows), 'last_hash': all_rows[-1]['row_hash']})
    for item in sorted(p for p in root.iterdir() if p.is_dir()):
        for name in ('campaign-permit.json', 'campaign-reconciliation.json'):
            W(item/name, replacements[J(item/name)['row_hash']])
        for name in ('transport-ledger.ndjson', 'ledger-after.ndjson'):
            p = item/name; p.write_bytes(b''.join(events.canonical(replacements[json.loads(l)['row_hash']])+b'\n' for l in p.read_bytes().splitlines()))
        reservation = J(item/'reservation.json')
        reservation.update(ledger_row_hash=J(item/'campaign-permit.json')['row_hash'], ledger_sha256=r6.sha(item/'transport-ledger.ndjson')); W(item/'reservation.json', reservation)
        def change(current, rows):
            for row in rows:
                if row['event'] == 'request_reserved': row['payload'] = J(current/'reservation.json')
                elif row['event'] == 'reservation_reconciled':
                    row['payload'].update(row_hash=J(current/'campaign-reconciliation.json')['row_hash'], ledger_sha256=r6.sha(current/'ledger-after.ndjson'))
            for name in ('accounting.json', 'credential-summary.json'):
                v = J(current/name); record = v if name == 'accounting.json' else v['accounting']; record['reservation'] = J(current/'reservation.json'); W(current/name, v)
        refinalize(item, change)


def rewrite_attempt_identity(root, ledgers, name):
    """Remove or blank rehearsal-3's attempt identity in the permit and/or its receipt, rehashing every mirror."""
    run = root/'rehearsal-3'; digest = J(run/'search-policy.json')['config_sha256']; rid = J(run/'campaign-permit.json')['reservation_id']
    def mutate(row):
        if row.get('kind') == 'reservation' and row['reservation_id'] == rid:
            if name in ('attempt_field_removed', 'attempt_identity_removed'): row.pop('attempt_id', None)
            elif name == 'attempt_identity_empty': row['attempt_id'] = ''
    rebind_rows(root, ledgers, digest, mutate)
    if name in ('attempt_event_removed', 'attempt_identity_removed'):
        def change(current, rows):
            rows[:] = [r for r in rows if r['event'] != 'reservation_attempted']
        refinalize(run, change)


def predicate_controls(root):
    """Predicates whose inputs are otherwise pinned by the reconciliation evidence digests."""
    results = {}
    r3 = root/'rehearsal-3'; permit = J(r3/'campaign-permit.json'); http = J(r3/'stages/proposal-1/output/http.json')
    a = audit.Audit(); bad = dict(http); bad['header_send_at_ns'] = bad['tls_verified_at_ns']  # grant can no longer precede the header
    try: audit.grant(a, r3, 'rehearsal-3', 'proof', permit, bad, audit.RULES[J(r3/'search-policy.json')['name']]); raise AssertionError('accepted')
    except audit.Rejection as rej: results['grant_out_of_order'] = rej.case
    a = audit.Audit(); bad = dict(http); bad['credential_commitment_sha256'] = '0'*64
    try: audit.commitment(a, r3, 'rehearsal-3', bad); raise AssertionError('accepted')
    except audit.Rejection as rej: results['commitment_mismatch'] = rej.case
    a = audit.Audit(); rows = events.read(r3/'events.ndjson')
    hit = next(r for r in rows if r['stage'] == 'proposal-1' and r['event'] == 'stage_finished'); hit['payload'] = dict(hit['payload'], exit_code=1)
    try: audit.receipts(a, r3, 'rehearsal-3', rows); raise AssertionError('accepted')
    except audit.Rejection as rej: results['receipt_disagrees_with_process'] = rej.case
    # positive: the layout a repeated torn-marker repair leaves (torn release beside the valid unknown receipt, row completed_from_marker) is accepted
    with tempfile.TemporaryDirectory() as tmp:
        d = Path(tmp); book = ledger.Ledger(d/'ledger', permit['policy_sha256']); book.activate(J(r3/'transport-policy.json')['ledger']['rehearsal_authorization'], 'rehearsal')
        p2, _ = book.reserve('layout', {'reserved_micro_usd': 1}, {'request_sha256': 'b'*64, 'arguments_sha256': 'c'*64}, {})
        slot = book.slot(p2['reservation_id']); (slot/'release.json').write_bytes(b'{"kind"')
        row, _ = book.reconcile(p2, None, None, {})  # torn release -> unknown with a valid unknown.json; torn association kept
        assert row['kind'] == 'unknown' and row['torn_marker'] == 'release.json'
        fake_run = d/'run'; (fake_run/'stages/proposal-1/grant').mkdir(parents=True)
        for f in slot.iterdir(): shutil.copyfile(f, fake_run/'stages/proposal-1/grant'/f.name)
        a = audit.Audit(); audit.slot_contents(a, fake_run, 'rehearsal-3', audit.RULES['responses_campaign_v6'], p2, row, book)
        assert a.cases == {'rehearsal-3:slot:authoritative_matches_retained': True}
        results[LAYOUT_POSITIVE] = 'accepted'
    a = audit.Audit(); bad = dict(http); del bad['grant_durable_at_ns']  # a revision that promises the durability instant must record it
    try: audit.grant(a, r3, 'rehearsal-3', 'proof', permit, bad, audit.RULES[J(r3/'search-policy.json')['name']]); raise AssertionError('accepted')
    except audit.Rejection as rej: results['missing_durability_field'] = rej.case
    assert {k: v for k, v in results.items() if k != LAYOUT_POSITIVE} == PREDICATE and results[LAYOUT_POSITIVE] == 'accepted', results
    return results


# --- the second review's mutations (campaign_v2_review_probes.py), copied so that this module has no circular import ---
def authority_slot(root, books):
    run = root/'rehearsal-3'; permit = J(run/'campaign-permit.json')
    book = ledger.Ledger(books/'rehearsal', permit['policy_sha256'])
    p = book.slot(permit['reservation_id'])/ledger.GRANT_FILE
    assert p.read_bytes() == (run/'stages/proposal-1/grant/send-grant.json').read_bytes()
    W(p, {'wrong_reservation': True})
    try:
        ledger.read_grant(p.parent, permit)
    except ledger.Failure as error:
        return {'only_authoritative_slot_changed': True, 'production_reader_rejects': error.code}
    raise AssertionError('corrupted grant unexpectedly parsed')


def mount_change(root, books, guest):
    def change(run, rows):
        p = run/'stages/proposal-1/command.json'; command = J(p); argv = command['argv']
        matches = [i for i, a in enumerate(argv) if a == guest and i >= 2 and argv[i-2] in ('--bind', '--ro-bind')]
        assert len(matches) == 1, matches
        index = matches[0]-1
        assert argv[index] != '/tmp/unrelated-review-slot'
        argv[index] = '/tmp/unrelated-review-slot'; W(p, command)
    refinalize(root/'rehearsal-3', change)
    return {'guest_mount': guest, 'host_mount_changed': True, 'normal_finalizer': True}


def scan_metadata(root, books, field):
    run = root/'rehearsal-3'; path = run/'publication-scan.json'; report = J(path)
    entries = [e for e in report['inventory'] if e['path'] == 'events.ndjson']
    assert len(entries) == 1
    value = '0'*64 if field == 'sha256' else 0
    assert entries[0][field] != value
    entries[0][field] = value; W(path, report)
    nonce = J(run/'credential-canary.json')['nonce']
    W(run/'publication-final.json', publication.final_record(path, credential.derive(nonce), nonce))
    rows = events.read(run/'events.ndjson')
    rows[-1]['payload'].update(publication_scan_sha256=r6.sha(path),
                               publication_final_sha256=r6.sha(run/'publication-final.json'))
    rechain(run, rows); driver.publication_driver.seal(run, True)
    return {'one_inventory_field_changed': field, 'terminal_and_seal_rebound': True}


def false_termination(root, books):
    """Coherently bind a non-terminated supervisor record to an asserted release."""
    run = root/'rehearsal-1'; path = run/'stages/proposal-1/proposal-1.process.json'
    process = J(path); assert ledger.termination_established(process)
    process['workload_empty_after_cleanup'] = False; W(path, process)
    assert not ledger.termination_established(process)
    permit = J(run/'campaign-permit.json')
    book = ledger.Ledger(books/'rehearsal', permit['policy_sha256'])
    all_rows = ledger.parse(book.path.read_bytes()); replacements = {}; previous = '0'*64
    for row in all_rows:
        old = row['row_hash']
        if row['kind'] == 'release' and row['reservation_id'] == permit['reservation_id']:
            row['evidence']['process_sha256'] = r6.sha(path)
        row['previous_hash'] = previous; row.pop('row_hash')
        row['row_hash'] = ledger.digest(row); previous = row['row_hash']; replacements[old] = row
    def new_raw(rows):
        return b''.join(events.canonical(replacements[r['row_hash']])+b'\n' for r in rows)
    book.path.write_bytes(b''.join(events.canonical(r)+b'\n' for r in all_rows))
    W(book.head, {'policy_sha256': permit['policy_sha256'], 'rows': len(all_rows), 'last_hash': all_rows[-1]['row_hash']})
    for item in root.iterdir():
        for name in ('campaign-permit.json', 'campaign-reconciliation.json'):
            p = item/name; W(p, replacements[J(p)['row_hash']])
        for name in ('transport-ledger.ndjson', 'ledger-after.ndjson'):
            p = item/name; p.write_bytes(new_raw([json.loads(line) for line in p.read_bytes().splitlines()]))
        p = item/'reservation.json'; reservation = J(p)
        reservation.update(ledger_row_hash=J(item/'campaign-permit.json')['row_hash'],
                           ledger_sha256=r6.sha(item/'transport-ledger.ndjson')); W(p, reservation)
        for base in (item/'stages/proposal-1/grant', book.slot(J(item/'campaign-permit.json')['reservation_id'])):
            for marker in ('release.json', 'unknown.json'):
                p = base/marker
                if p.exists():
                    v = J(p); v['row_hash'] = J(item/'campaign-reconciliation.json')['row_hash']; W(p, v)
        def change(current, rows):
            for row in rows:
                if row['event'] == 'request_reserved': row['payload'] = J(current/'reservation.json')
                elif row['event'] == 'reservation_reconciled':
                    row['payload'].update(row_hash=J(current/'campaign-reconciliation.json')['row_hash'],
                                          ledger_sha256=r6.sha(current/'ledger-after.ndjson'))
                elif current.name == 'rehearsal-1' and row['stage'] == 'proposal-1' and row['event'] == 'stage_finished':
                    row['payload'] = process
            for name in ('accounting.json', 'credential-summary.json'):
                p = current/name; v = J(p)
                record = v if name == 'accounting.json' else v['accounting']
                record['reservation'] = J(current/'reservation.json'); W(p, v)
        refinalize(item, change)
    return {'recorded_termination_established': True, 'recomputed_termination_established': False,
            'retained_release': True, 'ledger_and_all_mirrors_rehashed': True}



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    results = {}
    with tempfile.TemporaryDirectory(prefix='r6-008-controls-') as temp:
        root = Path(temp)/'campaign-runs'; ledgers = Path(temp)/'ledgers'
        shutil.copytree(RUNS, root); shutil.copytree(ROOT/'ledgers', ledgers)
        baseline = run_audit(root, ledgers); assert baseline == {'accepted': True, 'case_count': len(audit.CASES)}, baseline
        results['unmutated_copy_accepted'] = baseline
        results['predicate_controls'] = predicate_controls(root)
    for older in ('campaign-runs', 'campaign-runs-v2', 'campaign-runs-v3', 'campaign-runs-v4', 'campaign-runs-v5', 'campaign-runs-v6'):
        with tempfile.TemporaryDirectory(prefix='r6-008-controls-') as temp:
            root = Path(temp)/'campaign-runs'; ledgers = Path(temp)/'ledgers'
            shutil.copytree(ROOT/older, root); shutil.copytree(ROOT/'ledgers', ledgers)
            observed = run_audit(root, ledgers); assert observed == {'accepted': True, 'case_count': len(audit.CASES)}, (older, observed)
            results['superseded_revision_audited:'+older] = {**observed, 'dispatch': audit.audit(root, ledgers)['modules']}
    for name, case in EXPECTED.items():
        with tempfile.TemporaryDirectory(prefix='r6-008-controls-') as temp:
            root = Path(temp)/'campaign-runs'; ledgers = Path(temp)/'ledgers'
            shutil.copytree(RUNS, root); shutil.copytree(ROOT/'ledgers', ledgers)
            assert run_audit(root, ledgers)['accepted'] is True
            mutate(root, ledgers, name)
            observed = run_audit(root, ledgers)
            assert observed['accepted'] is False and observed['rejected_case'] == case, (name, observed)
            results[name] = {'rejected': True, 'rejected_case': observed['rejected_case']}
    record = {'passed': True, 'controls': len(EXPECTED)+len(PREDICATE)+1, 'named_cases': len(audit.CASES), 'results': results,
              'auditor_sha256': r6.sha(HERE/'campaign_audit.py'), 'program_sha256': r6.sha(Path(__file__)),
              'live_model_calls': 0, 'credentials_read': 0, 'scope': 'temporary copies of runs and ledgers; one relationship per mutation'}
    r6.write_json(args.output, record)
    print(json.dumps({k: record[k] for k in ('passed', 'controls', 'named_cases')}, indent=1))
    print(json.dumps({k: (v['rejected_case'] if isinstance(v, dict) and 'rejected_case' in v else v) for k, v in results.items()}, indent=1))


if __name__ == '__main__':
    main()

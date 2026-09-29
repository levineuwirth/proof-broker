#!/usr/bin/env python3
"""Controls for the block 2 runner's continuation gate (`run_block2.py`). SYNTHETIC: every case is a copy of an audited block 1 run,
retargeted to draw 2 consistently at every identity, changed in one relationship, and resealed with the production seal; the sender and the
live ledger are mocked, so no subprocess is launched, no credential is read and nothing is sent.

Revision 3 (block 2 runner revision 2 review). Positive fixtures are internally consistent: the permit and reconciliation rows are rewritten
to the draw-2 slot and episode and the ledger chain re-hashed from there, the run's own ledger snapshots regenerated from those rows, the
chain's ledger receipts repointed, the event chain's run identity renamed and re-hashed, and the terminal receipt's digests refreshed. Each
case then changes exactly one relationship. Added: the review's probes (a verifier receipt accepting l170 against a rejecting record, l170's
summary claiming a proof, a proof whose verifier receipt rejects, a proof without its consumption receipt, an empty seal inventory, another
slot's genuine reconciliation) and further controls for each relationship the gate now checks.

Revision 4 (block 2 runner revision 3 review). The fixture builder also refreshes, after any record change, the receipts that mirror the
changed records (as the driver writes them), so each case still changes one relationship; the review's two probes (a transport receipt
reporting a failed binding against a clean record, a terminal reporting failed publication against clean publication records) and each other
mirrored receipt are isolated receipt-only controls. The positive cases carry the frozen live terminal (publication pending, not accepted).

Revision 5 (block 2 runner revision 4 review). The review's two probes (the export's process record deleted and the run resealed; a
stage-finish receipt with no process record) and two further one-to-one and sequence controls (a stage directory without receipts; two
receipts reordered). The invalid-response fixture follows the frozen `response_invalid` sequence (no assembly, check or recovery receipts).

Revision 6 (R6-014 amendment 2). The release cases use the SYNTHETIC release and retry of `fixtures/r6-014-v4-live-release` as templates,
never the collected release: a verified release is retried as the slot's next attempt; a release followed by the sent retry continues to
the next slot; at the pre-send limit the slot is exhausted and pauses; and each release relationship broken alone pauses (a header send, a
grant, a category outside the connection phase, verified TLS, a non-zero exit, a record past the send, a ledger that does not hold it as
this attempt, a sent retry whose slot does not show its prior releases). The existing cases' ledger state now carries the pre-send limit
and the slot's released count.

Each case runs through the production `main()` twice, with the same expected decision:
* **fresh** — the mocked sender materializes the case as the episode's result; the runner then gates it;
* **restart** — the case already exists when the runner starts; the runner must gate it before any launch.
"continued" means the runner went on to attempt the next slot (the mock stops it there); "paused" and "integrity_stop" mean it stopped
without attempting another launch.
"""
import argparse
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

HERE = Path(__file__).resolve().parent; R6 = HERE.parents[1]
sys.path.insert(0, str(R6))
import cohort_ledger as ledger
import events
import run as r6
import site_network

spec = importlib.util.spec_from_file_location('block2_runner', HERE/'run_block2.py'); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
BLOCK1 = R6/'cohort-live-v9'
FIXTURE_V4 = R6/'fixtures/r6-014-v4-live-release/runs'  # revision 6: the SYNTHETIC release and its retry (amendment 2), never the collected release
TEMPLATES = {'release': FIXTURE_V4/'l096-draw2', 'retry': FIXTURE_V4/'l096-draw2-attempt2'}
J = lambda p: json.loads(Path(p).read_bytes()); W = lambda p, v: r6.write_json(p, v)
CASES = {  # name: (template site, expected decision)
    'proof_continues': ('l069', 'continued'),
    'closer_refusal_continues': ('l166', 'continued'),
    'negative_control_rejected_continues': ('l170', 'continued'),
    'invalid_response_continues': ('l170', 'continued'),
    'sealed_release_pauses': ('l069', 'paused'),
    'unknown_send_pauses': ('l069', 'paused'),
    'returned_binding_failure_pauses': ('l069', 'paused'),
    'provider_error_pauses': ('l069', 'paused'),
    'publication_failure_pauses': ('l069', 'paused'),
    'proof_certificate_record_rejects_pauses': ('l069', 'paused'),
    'proof_verifier_receipt_rejects_pauses': ('l069', 'paused'),
    'proof_consumption_receipt_missing_pauses': ('l069', 'paused'),
    'proof_kernel_receipt_disagrees_pauses': ('l069', 'paused'),
    'refusal_receipt_disagrees_pauses': ('l166', 'paused'),
    'terminal_disagrees_pauses': ('l069', 'paused'),
    'missing_evidence_pauses': ('l069', 'paused'),
    'empty_seal_inventory_pauses': ('l069', 'paused'),
    'seal_missing_summary_entry_pauses': ('l069', 'paused'),
    'seal_missing_events_entry_pauses': ('l069', 'paused'),
    'seal_digest_broken_pauses': ('l069', 'paused'),
    'unlisted_file_pauses': ('l069', 'paused'),
    'unsealed_run_pauses': ('l069', 'paused'),
    'other_slot_pauses': ('l069', 'paused'),
    'chain_of_another_run_pauses': ('l069', 'paused'),
    'foreign_reconciliation_pauses': ('l069', 'paused'),
    'ledger_row_mismatch_pauses': ('l069', 'paused'),
    'ledger_receipt_mismatch_pauses': ('l069', 'paused'),
    'unreviewed_outcome_pauses': ('l069', 'paused'),
    # revision 4: receipt-only disagreements, each with its record unchanged (the review's two first)
    'transport_receipt_disagrees_pauses': ('l069', 'paused'),
    'terminal_publication_failed_pauses': ('l069', 'paused'),
    'terminal_publication_not_pending_pauses': ('l069', 'paused'),
    'terminal_accepted_claimed_pauses': ('l069', 'paused'),
    'terminal_event_finished_on_refusal_pauses': ('l166', 'paused'),
    'transport_receipt_missing_pauses': ('l069', 'paused'),
    'transport_receipt_duplicated_pauses': ('l069', 'paused'),
    'https_receipt_disagrees_pauses': ('l069', 'paused'),
    'credential_receipt_disagrees_pauses': ('l069', 'paused'),
    'reservation_receipt_disagrees_pauses': ('l069', 'paused'),
    'stage_receipt_disagrees_pauses': ('l069', 'paused'),
    'transport_authorization_other_slot_pauses': ('l069', 'paused'),
    'assembly_receipt_disagrees_pauses': ('l069', 'paused'),
    # revision 5: stage receipts one to one with stage records, and the whole chain the frozen sequence (the review's two first)
    'stage_process_record_deleted_pauses': ('l069', 'paused'),
    'stage_receipt_without_record_pauses': ('l069', 'paused'),
    'stage_directory_without_receipts_pauses': ('l069', 'paused'),
    'receipts_reordered_pauses': ('l069', 'paused'),
    # revision 6: a verified pre-send release is retried as the next attempt; anything else about a release pauses
    'release_is_retried': ('l096', 'retried'),
    'release_then_sent_retry_continues': ('l096', 'continued'),
    'release_exhausted_pauses': ('l096', 'paused'),
    'release_with_header_send_pauses': ('l096', 'paused'),
    'release_with_grant_pauses': ('l096', 'paused'),
    'release_category_not_connection_phase_pauses': ('l096', 'paused'),
    'release_tls_verified_pauses': ('l096', 'paused'),
    'release_nonzero_exit_pauses': ('l096', 'paused'),
    'release_records_past_send_pauses': ('l096', 'paused'),
    'release_ledger_count_mismatch_pauses': ('l096', 'paused'),
    'sent_retry_release_count_mismatch_pauses': ('l096', 'paused'),
    'negative_control_certificate_record_accepts_stops': ('l170', 'integrity_stop'),
    'negative_control_verifier_receipt_accepts_stops': ('l170', 'integrity_stop'),
    'negative_control_summary_claims_proof_stops': ('l170', 'integrity_stop'),
    'negative_control_verdict_stops': ('l170', 'integrity_stop'),
    'negative_control_consumer_reached_stops': ('l170', 'integrity_stop'),
}
NEXT = {'l069': 'l070', 'l166': 'l175', 'l170': 'l175', 'l096': 'l166'}
RELEASE_CASES = {name for name in CASES if name.startswith('release_') or name.startswith('sent_retry_')}
TWO_ATTEMPTS = ('release_then_sent_retry_continues', 'sent_retry_release_count_mismatch_pauses')  # a release, then a sent retry of the slot


def rehash_ledger(rows, start):
    for i in range(start, len(rows)):
        row = {k: v for k, v in rows[i].items() if k != 'row_hash'}
        if i: row['previous_hash'] = rows[i-1]['row_hash']
        rows[i] = {**row, 'row_hash': ledger.digest(row)}


def ledger_bytes(rows): return b''.join(ledger.canonical(r)+b'\n' for r in rows)


def rechain(run, rows):
    previous = events.ZERO
    for row in rows:
        row.pop('event_hash', None); row['previous_hash'] = previous; row['event_hash'] = events.digest(row); previous = row['event_hash']
    (run/'events.ndjson').write_bytes(b''.join(events.canonical(r)+b'\n' for r in rows))


def supervisor(rows, stage, event): return next(r for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event)


def build(name, site, target):
    """The case at `target` (a consistent draw-2 retargeting of the audited draw-1 run, then one change) and its live-ledger view."""
    template = TEMPLATES['retry'] if name == '_sent_retry' else TEMPLATES['release'] if name in RELEASE_CASES else BLOCK1/f'{site}-draw1'
    shutil.copytree(template, target); run_name = target.name; task = f'bracket-{site}'
    sp = J(target/'search-policy.json'); sp['draw'] = 2; W(target/'search-policy.json', sp)
    # the slot identity: permit and reconciliation rows for draw 2 and this episode, the chain re-hashed from the permit
    rows = ledger.parse((target/'ledger-after.ndjson').read_bytes()); permit, recon = J(target/'campaign-permit.json'), J(target/'campaign-reconciliation.json')
    pi, ti = rows.index(permit), rows.index(recon)
    for i in (pi, ti): rows[i] = {**rows[i], 'draw': 2, 'episode_id': run_name}
    if name == 'sealed_release_pauses': rows[ti] = {**rows[ti], 'kind': 'release', 'send_outcome': None}
    if name == 'unknown_send_pauses': rows[ti] = {**rows[ti], 'kind': 'unknown', 'send_outcome': 'unknown'}
    rehash_ledger(rows, pi); permit, recon = rows[pi], rows[ti]
    W(target/'campaign-permit.json', permit); W(target/'campaign-reconciliation.json', recon)
    (target/'transport-ledger.ndjson').write_bytes(ledger_bytes(rows[:pi+1])); (target/'ledger-after.ndjson').write_bytes(ledger_bytes(rows[:ti+1]))
    reservation = J(target/'reservation.json'); reservation.update(ledger_row_hash=permit['row_hash'], ledger_sha256=r6.sha(target/'transport-ledger.ndjson'))
    W(target/'reservation.json', reservation)
    chain = events.read(target/'events.ndjson')
    if name != 'chain_of_another_run_pauses':
        for r in chain: r['run_id'] = run_name
    supervisor(chain, 'campaign-ledger', 'request_reserved')['payload'] = reservation
    supervisor(chain, 'campaign-ledger', 'reservation_reconciled')['payload'].update(row_hash=recon['row_hash'], kind=recon['kind'], send_outcome=recon.get('send_outcome'),
                                                                                     ledger_sha256=r6.sha(target/'ledger-after.ndjson'))
    authorization = supervisor(chain, 'proposal', 'live_transport_authorized')['payload']; authorization['slot'] = {'task_id': task, 'draw': 2}
    consumed = recon['kind'] in ('send_grant', 'unknown')
    # the one change
    if name == 'invalid_response_continues':
        chain = [r for r in chain if r['stage'] not in ('assembly', 'certificate-check') and r['event'] != 'recovery_finished']  # the frozen response_invalid sequence
        for stage in ('assembly', 'certificate-check'): shutil.rmtree(target/'stages'/stage)
        for f in ('certificate-verdict.json', 'validated-response.json', 'evidence.json'): (target/f).unlink(missing_ok=True)
        s = J(target/'credential-summary.json'); s['failure_category'] = 'response_schema'; W(target/'credential-summary.json', s)
        v = J(target/'transport-validation.json'); v.update(failure_category='response_schema', failure_phase='proposal'); W(target/'transport-validation.json', v)
    elif name == 'release_with_header_send_pauses':
        h = J(target/'stages/proposal-1/output/http.json'); h['header_sends_started'] = 1; W(target/'stages/proposal-1/output/http.json', h)
    elif name == 'release_with_grant_pauses':
        h = J(target/'stages/proposal-1/output/http.json'); h['grant_committed'] = True; W(target/'stages/proposal-1/output/http.json', h)
    elif name == 'release_category_not_connection_phase_pauses':
        for f in ('stages/proposal-1/output/http.json', 'transport-validation.json', 'credential-summary.json'):
            v = J(target/f); v['failure_category'] = 'credential_format'; W(target/f, v)
    elif name == 'release_tls_verified_pauses':
        h = J(target/'stages/proposal-1/output/http.json'); h['tls'] = {'verified': True}; W(target/'stages/proposal-1/output/http.json', h)
    elif name == 'release_nonzero_exit_pauses':
        p = J(target/'stages/proposal-1/proposal-1.process.json'); p['exit_code'] = 1; W(target/'stages/proposal-1/proposal-1.process.json', p)
        supervisor(chain, 'proposal-1', 'stage_finished')['payload'] = p  # its stage receipt, as the supervisor writes it
    elif name == 'release_records_past_send_pauses': shutil.copyfile(BLOCK1/'l170-draw1/certificate-verdict.json', target/'certificate-verdict.json')
    elif name == 'returned_binding_failure_pauses':
        v = J(target/'transport-validation.json'); v['response_request_binding']['accepted'] = False
        v.update(failure_category='transport_capture_failure', failure_phase='https_transport'); W(target/'transport-validation.json', v)
    elif name == 'provider_error_pauses':
        h = J(target/'stages/proposal-1/output/http.json'); h['http_status'] = 401; W(target/'stages/proposal-1/output/http.json', h)
    elif name == 'publication_failure_pauses':
        p = J(target/'publication-final.json'); p['report_clean'] = False; W(target/'publication-final.json', p)
    elif name == 'proof_certificate_record_rejects_pauses':
        c = J(target/'certificate-verdict.json'); c['accepted'] = False; W(target/'certificate-verdict.json', c)
    elif name in ('proof_verifier_receipt_rejects_pauses', 'negative_control_verifier_receipt_accepts_stops'):
        receipt = supervisor(chain, 'certificate-check', 'independent_certificate_verdict'); receipt['payload'] = {**receipt['payload'], 'accepted': name.startswith('negative')}
    elif name == 'proof_consumption_receipt_missing_pauses':
        chain = [r for r in chain if not (r['source'] == 'child_report' and r['event'] == 'reconstruction_finished')]
    elif name == 'proof_kernel_receipt_disagrees_pauses':
        receipt = supervisor(chain, 'validation-whole', 'kernel_verdict'); receipt['payload'] = {**receipt['payload'], 'accepted': False}
    elif name == 'refusal_receipt_disagrees_pauses':
        receipt = supervisor(chain, 'reconstruct', 'reconstruction_refused'); receipt['payload'] = {**receipt['payload'], 'diagnosis': 'other'}
    elif name == 'other_slot_pauses': sp['draw'] = 3; W(target/'search-policy.json', sp)
    elif name == 'foreign_reconciliation_pauses':  # the review's probe: l099's genuine reconciliation, which the live ledger also holds
        foreign = J(BLOCK1/'l099-draw1/campaign-reconciliation.json'); W(target/'campaign-reconciliation.json', foreign)
    elif name == 'ledger_receipt_mismatch_pauses': supervisor(chain, 'campaign-ledger', 'reservation_reconciled')['payload']['row_hash'] = '0'*64
    elif name == 'unreviewed_outcome_pauses':
        s = J(target/'credential-summary.json'); s.update(failure_category='mystery', proof_accepted=False); W(target/'credential-summary.json', s)
    elif name == 'negative_control_certificate_record_accepts_stops':
        c = J(target/'certificate-verdict.json'); c['accepted'] = True; W(target/'certificate-verdict.json', c)
    elif name == 'negative_control_summary_claims_proof_stops':
        s = J(target/'credential-summary.json'); s['proof_accepted'] = True; W(target/'credential-summary.json', s)
    elif name == 'negative_control_verdict_stops': shutil.copyfile(BLOCK1/'l069-draw1/verdict.json', target/'verdict.json')
    elif name == 'negative_control_consumer_reached_stops':
        at = chain.index(supervisor(chain, 'certificate-check', 'independent_certificate_verdict'))
        chain.insert(at+1, {**chain[at], 'stage': 'reconstruct', 'event': 'stage_started', 'payload': {'command_file': 'stages/reconstruct/command.json'}})
    # revision 4: the receipts that mirror a changed record refreshed, as the driver writes them, then the receipt-only change
    if (target/'transport-validation.json').exists(): supervisor(chain, 'proposal', 'transport_validated')['payload'] = J(target/'transport-validation.json')
    supervisor(chain, 'episode', 'episode_started')['payload']['policy_sha256'] = r6.sha(target/'search-policy.json')
    out = target/'stages/proposal-1/output'
    supervisor(chain, 'proposal', 'https_observed')['payload'] = {'http_sha256': r6.sha(out/'http.json'), 'server_sha256': r6.sha(out/'server.json'),
                                                                  'pricing_check_sha256': r6.sha(out/'pricing-check.json')}
    if name == 'transport_receipt_disagrees_pauses':  # the review's probe: the receipt reports a failed request binding, the record a good one
        receipt = supervisor(chain, 'proposal', 'transport_validated'); receipt['payload'] = json.loads(json.dumps(receipt['payload']))
        receipt['payload']['response_request_binding']['accepted'] = False
    elif name == 'transport_receipt_missing_pauses': chain.remove(supervisor(chain, 'proposal', 'transport_validated'))
    elif name == 'transport_receipt_duplicated_pauses':
        receipt = supervisor(chain, 'proposal', 'transport_validated'); chain.insert(chain.index(receipt)+1, json.loads(json.dumps(receipt)))
    elif name == 'https_receipt_disagrees_pauses': supervisor(chain, 'proposal', 'https_observed')['payload']['http_sha256'] = '0'*64
    elif name == 'credential_receipt_disagrees_pauses':
        receipt = supervisor(chain, 'credential-receipt', 'credential_use_checked'); receipt['payload'] = {**receipt['payload'], 'credential_use_accepted': False}
    elif name == 'reservation_receipt_disagrees_pauses':
        receipt = supervisor(chain, 'campaign-ledger', 'request_reserved'); receipt['payload'] = {**receipt['payload'], 'message_utf8_bytes': receipt['payload']['message_utf8_bytes']+1}
    elif name == 'stage_receipt_disagrees_pauses':
        receipt = supervisor(chain, 'proposal-1', 'stage_finished'); receipt['payload'] = {**receipt['payload'], 'wall_seconds': receipt['payload']['wall_seconds']+1}
    elif name == 'transport_authorization_other_slot_pauses':
        receipt = supervisor(chain, 'proposal', 'live_transport_authorized'); receipt['payload'] = {**receipt['payload'], 'slot': {**receipt['payload']['slot'], 'draw': 3}}
    elif name == 'stage_receipt_without_record_pauses':  # the review's probe: a finish receipt for a stage that left no process record
        receipt = supervisor(chain, 'export', 'stage_finished'); chain.insert(chain.index(receipt)+1, {**json.loads(json.dumps(receipt)), 'stage': 'phantom'})
    elif name == 'receipts_reordered_pauses':
        a, b = supervisor(chain, 'proposal', 'https_observed'), supervisor(chain, 'proposal', 'transport_validated')
        i, j = chain.index(a), chain.index(b); clock = ('receipt_monotonic_ns', 'receipt_utc')  # each position keeps its receipt time
        chain[i], chain[j] = {**b, **{k: a[k] for k in clock if k in a}}, {**a, **{k: b[k] for k in clock if k in b}}
    elif name == 'assembly_receipt_disagrees_pauses':
        receipt = supervisor(chain, 'assembly', 'certificate_assembled'); receipt['payload'] = {**receipt['payload'], 'response_sha256': '0'*64}
    # the terminal receipt's digests refreshed (except where the terminal disagreement is the case), the chain re-hashed, the run resealed
    terminal = chain[-1]['payload']; summary = J(target/'credential-summary.json')  # derived from the summary, as `finalize` derives it
    terminal.update({k: bool(summary[k]) for k in ('proof_accepted', 'credential_use_accepted', 'ledger_reconciled', 'evidence_complete')})
    chain[-1]['event'] = 'episode_finished' if (summary['proof_accepted'] and summary['failure_category'] is None and summary['evidence_complete']
                                                 and summary['ledger_reconciled']) else 'episode_rejected'
    if name == 'terminal_disagrees_pauses': terminal['proof_accepted'] = False
    elif name == 'terminal_publication_failed_pauses': terminal['publication_accepted'] = False  # the review's probe
    elif name == 'terminal_publication_not_pending_pauses': terminal['publication_pending'] = False
    elif name == 'terminal_accepted_claimed_pauses': terminal['accepted'] = True
    elif name == 'terminal_event_finished_on_refusal_pauses': chain[-1]['event'] = 'episode_finished'
    terminal.update(summary_sha256=r6.sha(target/'credential-summary.json'), publication_final_sha256=r6.sha(target/'publication-final.json'),
                    publication_scan_sha256=r6.sha(target/'publication-scan.json'))
    for i, r in enumerate(chain): r['sequence'] = i
    rechain(target, chain)
    if name == 'missing_evidence_pauses': (target/'transport-validation.json').unlink()
    if name == 'stage_process_record_deleted_pauses': (target/'stages/export/export.process.json').unlink()  # the review's probe, then resealed
    if name == 'stage_directory_without_receipts_pauses':
        (target/'stages/phantom').mkdir(); shutil.copyfile(target/'stages/export/export.process.json', target/'stages/phantom/phantom.process.json')
    site_network.seal(target, J(target/'seal.json')['accepted'])
    seal = J(target/'seal.json')
    if name == 'empty_seal_inventory_pauses': seal['retained_sha256'] = {}; W(target/'seal.json', seal)
    elif name == 'seal_missing_summary_entry_pauses': del seal['retained_sha256']['credential-summary.json']; W(target/'seal.json', seal)
    elif name == 'seal_missing_events_entry_pauses': del seal['retained_sha256']['events.ndjson']; W(target/'seal.json', seal)
    elif name == 'seal_digest_broken_pauses': p = target/'runtime.json'; p.write_text(p.read_text()+'\n')  # a sealed file no receipt mirrors
    elif name == 'unlisted_file_pauses': (target/'unlisted.json').write_text('{}\n')
    elif name == 'unsealed_run_pauses': (target/'seal.json').unlink()
    view = [dict(r) for r in rows]+([J(BLOCK1/'l099-draw1/campaign-reconciliation.json')] if name == 'foreign_reconciliation_pauses' else [])
    if name == 'release_ledger_count_mismatch_pauses':  # another release row for this slot ahead of this one: this is not attempt 1 on the ledger
        view.insert(ti, {**view[ti], 'reservation_id': '0'*32, 'row_hash': '0'*64})
    released = sum(r['kind'] == 'release' and r.get('task_id') == task and r.get('draw') == 2 for r in view)
    if name == 'ledger_row_mismatch_pauses': view[ti] = {**view[ti], 'reconciled_at_unix': view[ti]['reconciled_at_unix']+1}
    state = {'open_reservations': [], 'transmissions_consumed': 12, 'committed_micro_usd': 1228800, 'maximum_presend_attempts': 1 if name == 'release_exhausted_pauses' else 3,
             'slots': {f'{task}/2': {'consumed': consumed, 'released': released}}}
    return view, state


class NextLaunch(Exception): pass


def exercise(name, site, mode):
    with tempfile.TemporaryDirectory(prefix='block2-runner-') as temp:
        temp = Path(temp); runs = temp/'runs'; runs.mkdir(); target = runs/f'{site}-draw2'; staged = temp/'staged'/target.name
        staged.parent.mkdir(); view = build(name, site, staged); launches = []; stages = {target: staged}
        if name in TWO_ATTEMPTS:  # revision 6: the slot's second attempt is the synthetic sent retry, whose ledger view includes the release
            second = runs/f'{site}-draw2-attempt2'; staged2 = temp/'staged'/second.name; view = build('_sent_retry', site, staged2); stages[second] = staged2
            if name == 'sent_retry_release_count_mismatch_pauses': view[1]['slots'][f'bracket-{site}/2']['released'] = 2
        if mode == 'restart':
            for live, source in stages.items(): shutil.copytree(source, live)
        def sender(argv, **kwargs):
            run = Path(argv[argv.index('--run-dir')+1]); launches.append(run.name)
            if mode == 'fresh' and run in stages: shutil.copytree(stages[run], run); return SimpleNamespace(returncode=0)
            raise NextLaunch()
        out = io.StringIO()
        with patch.object(m, 'RUNS', runs), patch.object(m, 'ORDER', (site, NEXT[site])), patch.object(m, 'DRAWS', (2,)), \
             patch.object(m, 'ledger_snapshot', lambda: view), patch.object(m, 'subprocess', SimpleNamespace(run=sender)), patch.object(m.time, 'sleep', lambda s: None), \
             patch.object(sys, 'argv', ['run_block2.py', '--credential-file', str(temp/'never-created')]), contextlib.redirect_stdout(out):
            try: m.main(); observed = 'completed'
            except NextLaunch: observed = 'retried' if launches and launches[-1] == f'{site}-draw2-attempt2' and name not in TWO_ATTEMPTS else 'continued'
            except SystemExit as e: observed = 'integrity_stop' if str(e).startswith('INTEGRITY STOP') else 'paused' if str(e).startswith('PAUSE') else str(e)
        lines = [json.loads(l) for l in out.getvalue().splitlines() if l.startswith('{')]; line = lines[-1] if lines else {}  # the decisive (last) gate line
        return {'observed': observed, 'launches': launches, 'decision': line.get('decision'), 'outcome': line.get('outcome'), 'reasons': line.get('reasons')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    results = {}
    for name, (site, expected) in CASES.items():
        for mode in ('fresh', 'restart'):
            got = exercise(name, site, mode)
            first, retry, following = f'{site}-draw2', f'{site}-draw2-attempt2', f'{NEXT[site]}-draw2'
            if name in TWO_ATTEMPTS:  # revision 6
                expected_launches = ([first, retry] if mode == 'fresh' else []) + ([following] if expected == 'continued' else [])
            elif expected == 'retried': expected_launches = [first, retry] if mode == 'fresh' else [retry]
            else:
                expected_launches = [first, following] if (mode == 'fresh' and expected == 'continued') else \
                                    [following] if expected == 'continued' else [first] if mode == 'fresh' else []
            assert got['observed'] == expected and got['launches'] == expected_launches, (name, mode, got)
            if expected in ('continued', 'retried'): assert got['reasons'] == [], (name, mode, got)
            results[f'{name}:{mode}'] = got; print(name, mode, got['observed'], got['outcome'], got['reasons'], flush=True)
    baselines = {site: list(m.gate(BLOCK1/f'{site}-draw1', f'bracket-{site}', 1)) for site in m.ORDER}  # the audited block 1 runs, read-only
    assert all(d[0] == 'continue' and d[2] == [] for d in baselines.values()), baselines
    r6.write_json(args.output, {'passed': True, 'cases': len(CASES), 'records': len(results), 'results': results, 'block1_baselines': baselines,
                                'runner_sha256': r6.sha(HERE/'run_block2.py'), 'program_sha256': r6.sha(Path(__file__)), 'transmissions': 0, 'credentials_read': 0,
                                'scope': 'synthetic copies of audited block 1 runs, consistent at every identity; mocked sender and ledger; continuation decisions only'})
    print(json.dumps({'passed': True, 'cases': len(CASES), 'records': len(results)}))


if __name__ == '__main__':
    main()

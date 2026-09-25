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
    'negative_control_certificate_record_accepts_stops': ('l170', 'integrity_stop'),
    'negative_control_verifier_receipt_accepts_stops': ('l170', 'integrity_stop'),
    'negative_control_summary_claims_proof_stops': ('l170', 'integrity_stop'),
    'negative_control_verdict_stops': ('l170', 'integrity_stop'),
    'negative_control_consumer_reached_stops': ('l170', 'integrity_stop'),
}
NEXT = {'l069': 'l070', 'l166': 'l175', 'l170': 'l175'}


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
    shutil.copytree(BLOCK1/f'{site}-draw1', target); run_name = target.name; task = f'bracket-{site}'
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
    consumed = recon['kind'] in ('send_grant', 'unknown')
    # the one change
    if name == 'invalid_response_continues':
        chain = [r for r in chain if r['stage'] not in ('assembly', 'certificate-check')]
        (target/'certificate-verdict.json').unlink()
        s = J(target/'credential-summary.json'); s['failure_category'] = 'response_schema'; W(target/'credential-summary.json', s)
        v = J(target/'transport-validation.json'); v.update(failure_category='response_schema', failure_phase='proposal'); W(target/'transport-validation.json', v)
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
        s = J(target/'credential-summary.json'); s['failure_category'] = 'mystery'; W(target/'credential-summary.json', s)
    elif name == 'negative_control_certificate_record_accepts_stops':
        c = J(target/'certificate-verdict.json'); c['accepted'] = True; W(target/'certificate-verdict.json', c)
    elif name == 'negative_control_summary_claims_proof_stops':
        s = J(target/'credential-summary.json'); s['proof_accepted'] = True; W(target/'credential-summary.json', s)
    elif name == 'negative_control_verdict_stops': shutil.copyfile(BLOCK1/'l069-draw1/verdict.json', target/'verdict.json')
    elif name == 'negative_control_consumer_reached_stops':
        at = chain.index(supervisor(chain, 'certificate-check', 'independent_certificate_verdict'))
        chain.insert(at+1, {**chain[at], 'stage': 'reconstruct', 'event': 'stage_started', 'payload': {'command_file': 'stages/reconstruct/command.json'}})
    # the terminal receipt's digests refreshed (except where the terminal disagreement is the case), the chain re-hashed, the run resealed
    terminal = chain[-1]['payload']
    if name == 'terminal_disagrees_pauses': terminal['proof_accepted'] = False
    else: terminal.update(summary_sha256=r6.sha(target/'credential-summary.json'), publication_final_sha256=r6.sha(target/'publication-final.json'),
                          publication_scan_sha256=r6.sha(target/'publication-scan.json'))
    for i, r in enumerate(chain): r['sequence'] = i
    rechain(target, chain)
    if name == 'missing_evidence_pauses': (target/'transport-validation.json').unlink()
    site_network.seal(target, J(target/'seal.json')['accepted'])
    seal = J(target/'seal.json')
    if name == 'empty_seal_inventory_pauses': seal['retained_sha256'] = {}; W(target/'seal.json', seal)
    elif name == 'seal_missing_summary_entry_pauses': del seal['retained_sha256']['credential-summary.json']; W(target/'seal.json', seal)
    elif name == 'seal_missing_events_entry_pauses': del seal['retained_sha256']['events.ndjson']; W(target/'seal.json', seal)
    elif name == 'seal_digest_broken_pauses': p = target/'input-ir.json'; p.write_text(p.read_text()+'\n')
    elif name == 'unlisted_file_pauses': (target/'unlisted.json').write_text('{}\n')
    elif name == 'unsealed_run_pauses': (target/'seal.json').unlink()
    view = [dict(r) for r in rows]+([J(BLOCK1/'l099-draw1/campaign-reconciliation.json')] if name == 'foreign_reconciliation_pauses' else [])
    if name == 'ledger_row_mismatch_pauses': view[ti] = {**view[ti], 'reconciled_at_unix': view[ti]['reconciled_at_unix']+1}
    state = {'open_reservations': [], 'transmissions_consumed': 12, 'committed_micro_usd': 1228800, 'slots': {f'{task}/2': {'consumed': consumed}}}
    return view, state


class NextLaunch(Exception): pass


def exercise(name, site, mode):
    with tempfile.TemporaryDirectory(prefix='block2-runner-') as temp:
        temp = Path(temp); runs = temp/'runs'; runs.mkdir(); target = runs/f'{site}-draw2'; staged = temp/'staged'/target.name
        staged.parent.mkdir(); view = build(name, site, staged); launches = []
        if mode == 'restart': shutil.copytree(staged, target)
        def sender(argv, **kwargs):
            run = Path(argv[argv.index('--run-dir')+1]); launches.append(run.name)
            if mode == 'fresh' and run == target: shutil.copytree(staged, target); return SimpleNamespace(returncode=0)
            raise NextLaunch()
        out = io.StringIO()
        with patch.object(m, 'RUNS', runs), patch.object(m, 'ORDER', (site, NEXT[site])), patch.object(m, 'DRAWS', (2,)), \
             patch.object(m, 'ledger_snapshot', lambda: view), patch.object(m, 'subprocess', SimpleNamespace(run=sender)), \
             patch.object(sys, 'argv', ['run_block2.py', '--credential-file', str(temp/'never-created')]), contextlib.redirect_stdout(out):
            try: m.main(); observed = 'completed'
            except NextLaunch: observed = 'continued'
            except SystemExit as e: observed = 'integrity_stop' if str(e).startswith('INTEGRITY STOP') else 'paused' if str(e).startswith('PAUSE') else str(e)
        line = next((json.loads(l) for l in out.getvalue().splitlines() if l.startswith('{')), {})
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
            expected_launches = [f'{site}-draw2', f'{NEXT[site]}-draw2'] if (mode == 'fresh' and expected == 'continued') else \
                                [f'{NEXT[site]}-draw2'] if expected == 'continued' else [f'{site}-draw2'] if mode == 'fresh' else []
            assert got['observed'] == expected and got['launches'] == expected_launches, (name, mode, got)
            if expected == 'continued': assert got['reasons'] == [], (name, mode, got)
            results[f'{name}:{mode}'] = got; print(name, mode, got['observed'], got['outcome'], got['reasons'], flush=True)
    baselines = {site: list(m.gate(BLOCK1/f'{site}-draw1', f'bracket-{site}', 1)) for site in m.ORDER}  # the audited block 1 runs, read-only
    assert all(d[0] == 'continue' and d[2] == [] for d in baselines.values()), baselines
    r6.write_json(args.output, {'passed': True, 'cases': len(CASES), 'records': len(results), 'results': results, 'block1_baselines': baselines,
                                'runner_sha256': r6.sha(HERE/'run_block2.py'), 'program_sha256': r6.sha(Path(__file__)), 'transmissions': 0, 'credentials_read': 0,
                                'scope': 'synthetic copies of audited block 1 runs, consistent at every identity; mocked sender and ledger; continuation decisions only'})
    print(json.dumps({'passed': True, 'cases': len(CASES), 'records': len(results)}))


if __name__ == '__main__':
    main()

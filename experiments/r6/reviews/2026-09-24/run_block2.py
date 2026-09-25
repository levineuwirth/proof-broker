#!/usr/bin/env python3
"""R6-014 block 2: the 77 authorized episodes of draws 2-8 (draw by draw, across the eleven sites), run by the operator with the operator's
credential file. Never reads the file: its path is passed to the frozen driver (`cohort_episode.py --mode live`), which mounts it for the
sender alone.

Revision 2 (R6-014 block 2 preparation review, two P1 findings). One continuation gate (`gate`) decides every slot from its own bound
evidence, and it is applied identically after a fresh episode and, on restart, to every existing run before it could be skipped; it is
deterministic over the retained records, so a paused slot stays paused until an explicit reviewed resolution (this runner has no override).
Its decisions:

* **continue** — the slot ended as a returned send, bound and reconciled on the live ledger, sealed with an intact chain, its own
  synthetic-canary publication scan clean, and its outcome one of the ordinary outcomes with consistent records: a proof (certificate
  accepted, consumed, local and whole validated); a diagnosed closer refusal (certificate accepted, refusal recorded, nothing consumed);
  a witness rejected by the independent checker; an invalid model response (a proposal-phase failure with every binding intact);
* **integrity stop** — any raw verifier or consumer acceptance on the negative control (l170): an accepted certificate, a recorded
  refusal after acceptance, or a verdict. Collection stops and the block needs review (frozen analysis rule);
* **pause** — everything else, fail-closed: a release or unknown send, an open reservation, a ledger row that does not match, a transport,
  binding or capture failure, a provider (non-2xx) status, a failed publication scan, contradictory records, missing or unreadable
  evidence, a broken seal or chain, an unsealed (interrupted) run. Operator publication pending is normal and not a failure.

Revision 3 (block 2 runner revision 2 review: one P1, two P2). Raw acceptance is read before any classification, from every verifier,
consumer and kernel receipt and record, the summary and the terminal event, so the negative control stops whatever another record says;
the receipts in the chain must agree with the outcome records, the summary and the terminal payload (which binds the summary and publication
records by digest); the seal must retain every record the gate reads and list every file in the run; and the permit and reconciliation must
be this slot's (task, draw, episode, reservation), held once each and in order by the live ledger, bound by the chain's ledger receipts,
and ending the run's own ledger snapshots.

The block 1 runner (`run_block1.py`) is retained as run; this revision is for block 2 only.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

R6 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(R6))
import cohort_contract as contract
import cohort_ledger as ledger
import events

RUNS = R6/'cohort-live-v9'
ORDER = ('l069', 'l070', 'l071', 'l078', 'l096', 'l166', 'l170', 'l175', 'l178', 'l204', 'l099')
DRAWS = range(2, 9)
NEGATIVE_CONTROL = 'bracket-l170'
CONTINUABLE = ('proof', 'closer_refusal', 'witness_rejected', 'response_invalid')


def ledger_snapshot():
    """The live ledger's rows and state, read without the credential."""
    raw, s = contract.campaign_ledger(True).snapshot()
    return ledger.parse(raw), s


def load(path):
    return json.loads(Path(path).read_bytes())


REQUIRED = ('events.ndjson', 'search-policy.json', 'campaign-permit.json', 'campaign-reconciliation.json', 'credential-summary.json',
            'transport-validation.json', 'stages/proposal-1/output/http.json', 'publication-final.json', 'publication-scan.json',
            'transport-ledger.ndjson', 'ledger-after.ndjson')
OUTCOME_FILES = ('certificate-verdict.json', 'verdict.json', 'reconstruction-refusal.json')  # retained wherever present


def seal_covers(run, problems):
    """Revision 3: the seal's inventory covers every record the gate reads, lists every file in the run, and every retained digest holds."""
    seal = load(run/'seal.json'); retained, ephemeral = seal['retained_sha256'], seal['ephemeral_sha256']
    rows = events.read(run/'events.ndjson')
    needed = [*REQUIRED, *(f for f in OUTCOME_FILES if (run/f).exists())]
    missing = [f for f in needed if f not in retained]
    if missing: problems.append(f'seal does not retain {missing}')
    files = [str(p.relative_to(run)) for p in run.rglob('*') if p.is_file() and p.name != 'seal.json']
    unlisted = [f for f in files if f not in retained and f not in ephemeral]
    if unlisted: problems.append(f'seal does not list {unlisted[:3]}')
    if not (seal['event_count'] == len(rows) and seal['last_event_hash'] == rows[-1]['event_hash']
            and all((run/k).is_file() and contract.r6.sha(run/k) == v for k, v in retained.items())): problems.append('seal digests or chain do not hold')
    return rows


def gate(run, task_id, draw):
    """(decision, outcome, reasons) for one slot, from its own records and the live ledger. Decision: continue, pause or integrity_stop.
    Revision 3: raw acceptance before classification; receipts, files, summary and terminal in agreement; seal coverage; slot identity."""
    reasons = []
    if not run.is_dir(): return 'pause', None, ['no run directory']
    if not (run/'seal.json').exists(): return 'pause', None, ['unsealed: the episode was interrupted']
    try:
        rows = seal_covers(run, reasons)
        sp = load(run/'search-policy.json'); permit = load(run/'campaign-permit.json'); reconciliation = load(run/'campaign-reconciliation.json')
        summary = load(run/'credential-summary.json'); validation = load(run/'transport-validation.json')
        http = load(run/'stages/proposal-1/output/http.json')
        publication = load(run/'publication-final.json'); scan = load(run/'publication-scan.json')
        own_before = ledger.parse((run/'transport-ledger.ndjson').read_bytes()); own_after = ledger.parse((run/'ledger-after.ndjson').read_bytes())
        cert = load(run/'certificate-verdict.json') if (run/'certificate-verdict.json').exists() else None
        verdict = load(run/'verdict.json') if (run/'verdict.json').exists() else None
        refusal = load(run/'reconstruction-refusal.json') if (run/'reconstruction-refusal.json').exists() else None
    except (OSError, ValueError, KeyError, IndexError, ledger.Failure) as error:
        return 'pause', None, reasons+[f'evidence missing or unreadable: {type(error).__name__}: {error}'[:300]]
    supervisor = {}
    for r in rows:
        if r['source'] == 'supervisor': supervisor.setdefault((r['stage'], r['event']), []).append(r['payload'])
    one = lambda stage, event: (supervisor.get((stage, event)) or [None])[0] if len(supervisor.get((stage, event), [])) <= 1 else 'duplicate'
    child = [r for r in rows if r['source'] == 'child_report']
    terminal = rows[-1]; terminal_payload = terminal['payload'] if terminal['source'] == 'supervisor' else {}
    receipt = one('certificate-check', 'independent_certificate_verdict'); refused_receipt = one('reconstruct', 'reconstruction_refused')
    kernels = supervisor.get(('validation-local', 'kernel_verdict'), [])+supervisor.get(('validation-whole', 'kernel_verdict'), [])
    reconstruct_reached = any(r['stage'] == 'reconstruct' for r in rows) or bool(child)
    # 1. raw acceptance on the negative control, before any classification: any verifier, consumer or kernel acceptance stops
    raw_acceptance = [name for name, hit in (
        ('verifier receipt', isinstance(receipt, dict) and receipt.get('accepted') is True), ('certificate record', (cert or {}).get('accepted') is True),
        ('consumer reached', reconstruct_reached), ('refusal record', refusal is not None), ('kernel receipts', bool(kernels)),
        ('proof receipt', bool(supervisor.get(('episode', 'proof_validated')))), ('verdict record', verdict is not None),
        ('summary proof_accepted', summary.get('proof_accepted') is True), ('terminal proof_accepted', terminal_payload.get('proof_accepted') is True),
        ('terminal finished', terminal['event'] == 'episode_finished')) if hit]
    if task_id == NEGATIVE_CONTROL and raw_acceptance:
        return 'integrity_stop', 'negative_control_acceptance', reasons+[f'acceptance on the negative control: {raw_acceptance}']
    # 2. the slot's identity: the run, its permit and reconciliation, their ledger rows and receipts, the run's own ledger snapshots
    if not (rows[0].get('run_id') == run.name and rows[0].get('task_id') == task_id): reasons.append('event chain is not this run')
    if not (sp.get('task_id') == task_id and sp.get('draw') == draw and sp.get('mode') == 'live'): reasons.append('run is not this slot')
    ident = lambda r: (r.get('task_id'), r.get('draw'), r.get('episode_id'))
    if not (permit.get('kind') == 'reservation' and ident(permit) == (task_id, draw, run.name)
            and ident(reconciliation) == (task_id, draw, run.name) and reconciliation.get('reservation_id') == permit.get('reservation_id')):
        reasons.append('permit or reconciliation is not this slot\'s')
    if not (own_before and own_before[-1] == permit and own_after and own_after[-1] == reconciliation and own_after[:len(own_before)] == own_before):
        reasons.append('the run\'s own ledger snapshots do not end at its permit and reconciliation')
    reserved = one('campaign-ledger', 'request_reserved'); reconciled = one('campaign-ledger', 'reservation_reconciled')
    if not (isinstance(reserved, dict) and reserved.get('reservation_id') == permit.get('reservation_id') and reserved.get('ledger_row_hash') == permit.get('row_hash')
            and isinstance(reconciled, dict) and reconciled.get('reservation_id') == reconciliation.get('reservation_id')
            and reconciled.get('row_hash') == reconciliation.get('row_hash') and reconciled.get('kind') == reconciliation.get('kind')):
        reasons.append('ledger receipts in the chain do not bind the permit and reconciliation')
    if not (reconciliation.get('kind') == 'send_grant' and reconciliation.get('send_outcome') == 'returned'):
        reasons.append(f"slot ended as {reconciliation.get('kind')}/{reconciliation.get('send_outcome')}, not a returned send")
    try:
        ledger_rows, s = ledger_snapshot()
        at = [i for i, r in enumerate(ledger_rows) if r == permit]; end = [i for i, r in enumerate(ledger_rows) if r == reconciliation]
        slot = s['slots'].get(f'{task_id}/{draw}') or {}
        if not (len(at) == 1 and len(end) == 1 and at[0] < end[0]): reasons.append('the live ledger does not hold this permit and its reconciliation')
        if not slot.get('consumed') or s['open_reservations']: reasons.append('ledger slot not consumed, or a reservation is open')
    except (ledger.Failure, OSError, ValueError, KeyError) as error:
        reasons.append(f'ledger unreadable: {error}')
    # 3. publication (the run's own synthetic-canary scan; the operator scan is pending, not failed), provider and transport
    if not (scan.get('accepted') is True and scan.get('disclosures') == [] and publication.get('report_clean') is True): reasons.append('publication scan failed')
    status = http.get('http_status'); category = summary.get('failure_category')
    bindings = (validation.get('outbound_envelope', {}).get('accepted') is True and validation.get('local_send_consistency', {}).get('accepted') is True
                and validation.get('response_request_binding', {}).get('accepted') is True)
    if status != 200 or summary.get('credential_use_accepted') is not True: reasons.append(f'provider status {status}')
    if not bindings: reasons.append('transport binding failure')
    if validation.get('failure_category') is not None and validation.get('failure_phase') != 'proposal':
        reasons.append(f"transport failure {validation.get('failure_category')} ({validation.get('failure_phase')})")
    if not (summary.get('evidence_complete') is True and summary.get('ledger_reconciled') is True): reasons.append('evidence incomplete or ledger not reconciled')
    # 4. the terminal receipt binds the summary and publication records and agrees with them
    shared = ('proof_accepted', 'credential_use_accepted', 'evidence_complete', 'ledger_reconciled')
    if not (terminal['source'] == 'supervisor' and terminal['event'] in ('episode_finished', 'episode_rejected')
            and terminal_payload.get('summary_sha256') == contract.r6.sha(run/'credential-summary.json')
            and terminal_payload.get('publication_final_sha256') == contract.r6.sha(run/'publication-final.json')
            and terminal_payload.get('publication_scan_sha256') == contract.r6.sha(run/'publication-scan.json')
            and all(terminal_payload.get(k) == summary.get(k) for k in shared)): reasons.append('terminal receipt does not agree with the summary and publication records')
    # 5. the outcome: receipts, records and summary in agreement for exactly one ordinary outcome
    if receipt == 'duplicate' or refused_receipt == 'duplicate' or (receipt is None) != (cert is None) or (receipt is not None and receipt != cert):
        reasons.append('verifier receipt and certificate record disagree')
    finished = [r['payload']['data'] for r in child if r['event'] == 'reconstruction_finished']
    proof_receipt = supervisor.get(('episode', 'proof_validated'), [])
    if category is None and summary.get('proof_accepted') is True:
        outcome = 'proof'
        if not (cert and cert.get('accepted') is True and verdict and verdict.get('local_obligation_closed') is True and verdict.get('whole_declaration_validated') is True
                and len(finished) == 1 and finished[0].get('certificate_consumed') is True and refusal is None and refused_receipt is None
                and len(kernels) == 2 and kernels == [verdict['final_validation']['local'], verdict['final_validation']['whole']] and all(k.get('accepted') is True for k in kernels)
                and len(proof_receipt) == 1 and proof_receipt[0].get('proof_accepted') is True and proof_receipt[0].get('verdict_sha256') == contract.r6.sha(run/'verdict.json')
                and terminal['event'] == 'episode_finished'):
            reasons.append('proof receipts and records do not agree')
    elif category == 'reconstruction_refused':
        outcome = 'closer_refusal'
        if not (cert and cert.get('accepted') is True and refusal and refusal.get('diagnosis') and refused_receipt == refusal and verdict is None
                and not finished and not kernels and not proof_receipt and any(r['event'] == 'closer_selected' for r in child)
                and summary.get('proof_accepted') is False and terminal['event'] == 'episode_rejected'):
            reasons.append('refusal receipts and records do not agree')
    elif category == 'certificate_verification':
        outcome = 'witness_rejected'
        if not (cert is not None and cert.get('accepted') is False and verdict is None and refusal is None and not reconstruct_reached and not kernels
                and not proof_receipt and summary.get('proof_accepted') is False and terminal['event'] == 'episode_rejected'):
            reasons.append('rejection receipts and records do not agree')
    elif category is not None and validation.get('failure_category') == category and validation.get('failure_phase') == 'proposal' and bindings and status == 200:
        outcome = 'response_invalid'
        if not (cert is None and receipt is None and verdict is None and refusal is None and not reconstruct_reached and not kernels and not proof_receipt
                and summary.get('proof_accepted') is False and terminal['event'] == 'episode_rejected'):
            reasons.append('invalid-response receipts and records do not agree')
    else:
        outcome = None; reasons.append(f'an outcome this runner has not reviewed: {category}')
    return ('continue' if not reasons and outcome in CONTINUABLE else 'pause'), outcome, reasons


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--credential-file', type=Path, required=True)
    args = parser.parse_args()
    RUNS.mkdir(exist_ok=True)
    for draw, site in [(d, s) for d in DRAWS for s in ORDER]:
        task_id, run = f'bracket-{site}', RUNS/f'{site}-draw{draw}'
        fresh = not run.exists()
        if fresh:
            _, s = ledger_snapshot()
            if s['open_reservations']: raise SystemExit(f'PAUSE: an open reservation exists before {run.name}: {s["open_reservations"]}')
            result = subprocess.run([sys.executable, str(R6/'cohort_episode.py'), '--mode', 'live', '--task', task_id, '--draw', str(draw),
                                     '--run-dir', str(run), '--credential-file', str(args.credential_file)], cwd=R6)
        decision, outcome, reasons = gate(run, task_id, draw)
        _, s = ledger_snapshot()
        print(json.dumps({'run': run.name, 'fresh': fresh, **({'exit': result.returncode} if fresh else {}), 'decision': decision, 'outcome': outcome,
                          'reasons': reasons, 'consumed': s['transmissions_consumed'], 'committed_micro_usd': s['committed_micro_usd']}), flush=True)
        if decision == 'integrity_stop': raise SystemExit(f'INTEGRITY STOP at {run.name}: {reasons}; collection stops, the block needs review')
        if decision != 'continue': raise SystemExit(f'PAUSE at {run.name}: {reasons}; stop and review (a restart re-applies this decision)')
    print(json.dumps({'block_2': 'complete', 'runs': len(ORDER)*len(DRAWS), 'next': 'the operator disclosure scan over all 88 runs, then the frozen evaluation'}), flush=True)


if __name__ == '__main__':
    main()

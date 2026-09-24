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


def seal_intact(run):
    seal = load(run/'seal.json'); rows = events.read(run/'events.ndjson')
    return (seal['event_count'] == len(rows) and seal['last_event_hash'] == rows[-1]['event_hash']
            and all((run/k).is_file() and contract.r6.sha(run/k) == v for k, v in seal['retained_sha256'].items())), rows


def gate(run, task_id, draw):
    """(decision, outcome, reasons) for one slot, from its own records and the live ledger. Decision: continue, pause or integrity_stop."""
    reasons = []
    if not run.is_dir(): return 'pause', None, ['no run directory']
    if not (run/'seal.json').exists(): return 'pause', None, ['unsealed: the episode was interrupted']
    try:
        intact, rows = seal_intact(run)
        if not intact: reasons.append('seal or chain not intact')
        terminal = rows[-1]
        if not (terminal['source'] == 'supervisor' and terminal['event'] in ('episode_finished', 'episode_rejected')): reasons.append('no terminal event')
        sp = load(run/'search-policy.json')
        if not (sp.get('task_id') == task_id and sp.get('draw') == draw and sp.get('mode') == 'live'): reasons.append('run is not this slot')
        reconciliation = load(run/'campaign-reconciliation.json')
        summary = load(run/'credential-summary.json')
        validation = load(run/'transport-validation.json')
        http = load(run/'stages/proposal-1/output/http.json')
        publication = load(run/'publication-final.json'); scan = load(run/'publication-scan.json')
    except (OSError, ValueError, KeyError, IndexError) as error:
        return 'pause', None, reasons+[f'evidence missing or unreadable: {type(error).__name__}: {error}'[:300]]
    # the ledger: a returned send, reconciled exactly as recorded, nothing open
    if not (reconciliation.get('kind') == 'send_grant' and reconciliation.get('send_outcome') == 'returned'):
        reasons.append(f"slot ended as {reconciliation.get('kind')}/{reconciliation.get('send_outcome')}, not a returned send")
    try:
        ledger_rows, s = ledger_snapshot()
        hits = [r for r in ledger_rows if r['kind'] in ledger.TERMINAL and r.get('reservation_id') == reconciliation.get('reservation_id')]
        slot = s['slots'].get(f'{task_id}/{draw}') or {}
        if not (len(hits) == 1 and hits[0] == reconciliation): reasons.append('ledger terminal row does not match the run')
        if not slot.get('consumed') or s['open_reservations']: reasons.append('ledger slot not consumed, or a reservation is open')
    except (ledger.Failure, OSError, ValueError, KeyError) as error:
        reasons.append(f'ledger unreadable: {error}')
    # publication: the run's own synthetic-canary scan must be clean (the operator scan comes later and is pending, not failed)
    if not (scan.get('accepted') is True and scan.get('disclosures') == [] and publication.get('report_clean') is True):
        reasons.append('publication scan failed')
    # transport and provider
    status = http.get('http_status'); category = summary.get('failure_category')
    bindings = (validation.get('outbound_envelope', {}).get('accepted') is True and validation.get('local_send_consistency', {}).get('accepted') is True
                and validation.get('response_request_binding', {}).get('accepted') is True)
    if status != 200 or summary.get('credential_use_accepted') is not True: reasons.append(f'provider status {status}')
    if not bindings: reasons.append('transport binding failure')
    if validation.get('failure_category') is not None and validation.get('failure_phase') != 'proposal':
        reasons.append(f"transport failure {validation.get('failure_category')} ({validation.get('failure_phase')})")
    if not (summary.get('evidence_complete') is True and summary.get('ledger_reconciled') is True): reasons.append('evidence incomplete or ledger not reconciled')
    # the outcome and its consistency
    cert = load(run/'certificate-verdict.json') if (run/'certificate-verdict.json').exists() else None
    verdict = load(run/'verdict.json') if (run/'verdict.json').exists() else None
    refusal = load(run/'reconstruction-refusal.json') if (run/'reconstruction-refusal.json').exists() else None
    accepted = (cert or {}).get('accepted') is True
    if task_id == NEGATIVE_CONTROL and (accepted or verdict is not None or refusal is not None):
        return 'integrity_stop', 'negative_control_acceptance', reasons+['a verifier or consumer acceptance on the negative control']
    if category is None and summary.get('proof_accepted') is True:
        outcome = 'proof'
        if not (accepted and verdict and verdict.get('local_obligation_closed') is True and verdict.get('whole_declaration_validated') is True
                and refusal is None and terminal['event'] == 'episode_finished'):
            reasons.append('contradictory records for a proof')
    elif category == 'reconstruction_refused':
        outcome = 'closer_refusal'
        if not (accepted and refusal and refusal.get('diagnosis') and verdict is None and summary.get('proof_accepted') is False): reasons.append('contradictory records for a refusal')
    elif category == 'certificate_verification':
        outcome = 'witness_rejected'
        if not (cert is not None and cert.get('accepted') is False and verdict is None and refusal is None): reasons.append('contradictory records for a rejected witness')
    elif category is not None and validation.get('failure_category') == category and validation.get('failure_phase') == 'proposal' and bindings and status == 200:
        outcome = 'response_invalid'
        if accepted or verdict is not None or refusal is not None: reasons.append('contradictory records for an invalid response')
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

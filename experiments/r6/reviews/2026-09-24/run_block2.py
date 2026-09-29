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

Revision 4 (block 2 runner revision 3 review: two P2 receipt-agreement gaps). Every supervisor receipt in the chain that mirrors a retained
record is required once and compared with it (`receipts_agree`): transport validation, the HTTPS observation digests, the credential-use
receipt, the reservation and its reconciled ledger digest, pricing admission, the live payload, the prepared problem, the episode's policy,
the transport authorization's slot and nonce, every stage's process record, and the assembly receipt; the terminal receipt must have the
frozen live shape (publication pending, not accepted) and be finished exactly when a proof is accepted with complete evidence. The seal must
retain each record these receipts mirror.

Revision 5 (block 2 runner revision 4 review: stage receipts were compared only for surviving process records). The whole event chain —
supervisor receipts and child reports, in order — must equal the frozen sequence for its outcome, taken from the auditor frozen under
`live-evaluation-v2` (its digest checked against the lock before use); the stages whose finish receipts that sequence names must be exactly
the run's stage directories and process records; and each stage's finish receipt and process record must match one to one before their
payloads are compared.

Revision 6 (R6-014 amendment 2, after block 2 paused at l204 draw 6 on a pre-send connection failure). A verified pre-send release — the
sender's connection-phase failure before its grant (one of `CONNECT_PHASE`), one connection attempt, no verified TLS, no grant, zero sends,
no status, the handled exception, the ledger's release with established termination, the slot's k-th release on the ledger, nothing open,
no record past the send, the frozen live release sequence — is decided `retry`: after `RETRY_DELAY_SECONDS`, the runner reserves the slot
again as `<site>-draw<d>-attempt<k+1>`, within the frozen pre-send limit (the ledger's `maximum_presend_attempts`); at the limit the slot is
exhausted and collection pauses. On restart every existing attempt is gated in order. A sent slot must show its prior releases as its
`released` count. Everything else is revision 5's.

Revision 7 (review `reviews/2026-09-29/R6-014-AMENDMENT-2-REVIEW.md`). P1: a release is retried only on the sender's complete pre-grant
state (`pre_grant_state`, the amendment 2 auditor's revision 2 predicate): every field `cohort_https.execute` initializes, present with its
initial value and type, the milestones before `handoff` reached in order, no outbound body or provider response; a missing or malformed
field pauses. P2: `preflight` inventories and gates the whole existing population before any sender is invoked — canonical run directory
names only, the slots with runs a prefix of the schedule, each slot's attempts 1..n within the limit, every attempt gated in order (each but
the last a retry, and only the last slot awaiting one), and the ledger's block 2 slots exactly these, nothing open, each with n reservations,
its releases and its consumption; collection then resumes at the next missing attempt, and a run directory that appears after the preflight
pauses.

The block 1 runner (`run_block1.py`) is retained as run; this revision is for block 2 only.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import time

R6 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(R6))
import importlib.util
import cohort_contract as contract
import cohort_ledger as ledger
import events

# Revision 5: the frozen receipt sequences, from the auditor under live-evaluation-v2 (checked against the lock before use), live mode.
AUDITOR = 'experiments/r6/reviews/2026-09-24/cohort_v9_audit_amended.py'
if contract.r6.sha(R6.parents[1]/AUDITOR) != json.loads((R6/'policies/live-evaluation-v2.sha256.json').read_bytes())['reviewed'][AUDITOR]:
    raise SystemExit('the auditor is not the one live-evaluation-v2 froze')
_spec = importlib.util.spec_from_file_location('block2_frozen_sequences', R6.parents[1]/AUDITOR); _audit = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_audit); _audit.configure('live')
SEQUENCE = {'proof': _audit.sequence('proof'), 'closer_refusal': _audit.sequence('reconstruction_refused'),
            'witness_rejected': _audit.sequence('witness_rejected'), 'response_invalid': _audit.sequence('response_invalid'),
            'released': _audit.sequence('release')}  # revision 6: the frozen live release sequence (unchanged by amendment 2)


def attempt_of(run):
    """Revision 6: `<site>-draw<d>` is attempt 1; `<site>-draw<d>-attempt<k>` is attempt k."""
    return int(run.name.rsplit('-attempt', 1)[1]) if '-attempt' in run.name else 1

RUNS = R6/'cohort-live-v9'
ORDER = ('l069', 'l070', 'l071', 'l078', 'l096', 'l166', 'l170', 'l175', 'l178', 'l204', 'l099')
DRAWS = range(2, 9)
NEGATIVE_CONTROL = 'bracket-l170'
CONTINUABLE = ('proof', 'closer_refusal', 'witness_rejected', 'response_invalid')
CONNECT_PHASE = ('tls_certificate_verification', 'tls_protocol_failure', 'transport_timeout', 'transport_connection_failure')  # cohort_https.handoff, before the grant
RETRY_DELAY_SECONDS = 60  # revision 6: a released slot is retried after this pause, riding out a brief network interruption
PRE_GRANT = {  # revision 7: the sender's record as `cohort_https.execute` initializes it (the amendment 2 auditor's, revision 2)
    'header_sends_started': 0, 'header_sends_returned': 0, 'body_sends_started': 0, 'body_sends_returned': 0, 'tls': None, 'tls_verified_at_ns': None,
    'header_send_at_ns': None, 'outbound_body_sha256': None, 'response_sha256': None, 'response_bytes': None, 'http_status': None, 'response_headers': {},
    'retries': 0, 'redirects_followed': 0, 'pricing_failure_code': None, 'ledger_failure_code': None, 'grant_committed': False, 'grant_write_failed': False,
    'grant_id': None, 'grant_created_at_ns': None, 'grant_durable_at_ns': None, 'send_outcome': 'not_started'}
REACHED = ('permit_verified_at_ns', 'pricing_admitted_at_ns', 'credential_read_at_ns', 'connection_started_at_ns')  # before `handoff`, in this order
NAME = re.compile(r'(l\d{3})-draw([1-9]\d*)(?:-attempt([2-9]|[1-9]\d+))?')  # revision 7: the only run directory names


def pre_grant_state(http, stage):
    """Revision 7: every `PRE_GRANT` field present with its initial value and type (missing or malformed fails), one connection attempt, the
    milestones before `handoff` reached in order, a verification code exactly for a certificate failure, no outbound body or response file."""
    same = lambda v, w: type(v) is type(w) and v == w
    reached = [http.get(k) for k in REACHED]; category = http.get('failure_category')
    return (all(k in http and same(http[k], v) for k, v in PRE_GRANT.items()) and same(http.get('connection_attempts'), 1)
            and all(type(t) is int for t in reached) and reached == sorted(reached) and type(http.get('elapsed_ns')) is int and http['elapsed_ns'] >= 0
            and category in CONNECT_PHASE and 'tls_verify_code' in http
            and (type(http['tls_verify_code']) is int if category == 'tls_certificate_verification' else http['tls_verify_code'] is None)
            and not (stage/'output/outbound-body.json').exists() and not (stage/'output/provider-response.json').exists())


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
# Revision 4: the records the chain's receipts mirror, which the gate now compares, retained too (validated-response.json where assembled)
RECEIPT_FILES = ('credential-receipt.json', 'reservation.json', 'host-pricing-admission.json', 'live-payload.json', 'prepared.json', 'input-ir.json',
                 'payload-audit.json', 'stages/proposal-1/output/server.json', 'stages/proposal-1/output/pricing-check.json')
TERMINAL_KEYS = ('accepted', 'proof_accepted', 'credential_use_accepted', 'publication_accepted', 'publication_pending', 'ledger_reconciled',
                 'evidence_complete', 'summary_sha256', 'publication_scan_sha256', 'publication_final_sha256')


def seal_covers(run, problems):
    """Revision 3: the seal's inventory covers every record the gate reads, lists every file in the run, and every retained digest holds."""
    seal = load(run/'seal.json'); retained, ephemeral = seal['retained_sha256'], seal['ephemeral_sha256']
    rows = events.read(run/'events.ndjson')
    needed = [*REQUIRED, *RECEIPT_FILES, *(f for f in OUTCOME_FILES if (run/f).exists()), *(['validated-response.json'] if (run/'validated-response.json').exists() else []),
              *(str(p.relative_to(run)) for p in sorted((run/'stages').glob('*/*.process.json')))]
    missing = [f for f in needed if f not in retained]
    if missing: problems.append(f'seal does not retain {missing}')
    files = [str(p.relative_to(run)) for p in run.rglob('*') if p.is_file() and p.name != 'seal.json']
    unlisted = [f for f in files if f not in retained and f not in ephemeral]
    if unlisted: problems.append(f'seal does not list {unlisted[:3]}')
    if not (seal['event_count'] == len(rows) and seal['last_event_hash'] == rows[-1]['event_hash']
            and all((run/k).is_file() and contract.r6.sha(run/k) == v for k, v in retained.items())): problems.append('seal digests or chain do not hold')
    return rows


def receipts_agree(run, one, supervisor, permit, http, cert):
    """Revision 4. Each receipt present exactly once and equal to the record (or the record's digest) it mirrors; a missing, duplicate or
    disagreeing receipt is reported. The assembly receipt is required exactly where a certificate record exists."""
    sha = contract.r6.sha; out = lambda *path: run.joinpath(*path); problems = []
    expected = {
        ('proposal', 'transport_validated'): load(out('transport-validation.json')),
        ('proposal', 'https_observed'): {'http_sha256': sha(out('stages/proposal-1/output/http.json')), 'server_sha256': sha(out('stages/proposal-1/output/server.json')),
                                         'pricing_check_sha256': sha(out('stages/proposal-1/output/pricing-check.json'))},
        ('credential-receipt', 'credential_use_checked'): load(out('credential-receipt.json')),
        ('campaign-ledger', 'request_reserved'): load(out('reservation.json')),
        ('pricing-admission', 'pricing_admitted'): {'admission_sha256': sha(out('host-pricing-admission.json'))},
        ('live-payload', 'payload_validated'): load(out('live-payload.json')),
        ('payload', 'prepared_problem'): {'prepared_sha256': sha(out('prepared.json')), 'input_ir_sha256': sha(out('input-ir.json')),
                                          'payload_audit_sha256': sha(out('payload-audit.json'))}}
    for key, value in expected.items():
        got = one(*key)
        if got != value: problems.append(f'{key[1]} receipt {"missing or duplicated" if got in (None, "duplicate") else "disagrees with its record"}')
    started = one('episode', 'episode_started'); reconciled = one('campaign-ledger', 'reservation_reconciled'); authorized = one('proposal', 'live_transport_authorized')
    if not (isinstance(started, dict) and started.get('policy_sha256') == sha(out('search-policy.json'))): problems.append('episode_started does not bind the search policy')
    if not (isinstance(reconciled, dict) and reconciled.get('ledger_sha256') == sha(out('ledger-after.ndjson'))): problems.append('reservation_reconciled does not bind the ledger snapshot')
    if not (isinstance(authorized, dict) and authorized.get('reservation_id') == permit.get('reservation_id') and authorized.get('slot') == {'task_id': permit.get('task_id'), 'draw': permit.get('draw')}
            and authorized.get('commitment_nonce') == http.get('commitment_nonce')): problems.append('live_transport_authorized is not this slot\'s')
    processes = {p.parent.name: p for p in run.glob('stages/*/*.process.json')}
    finished = {stage for (stage, event) in supervisor if event == 'stage_finished'}
    for stage in sorted(set(processes) | finished):  # revision 5: one to one, then equal
        if stage not in processes or one(stage, 'stage_finished') in (None, 'duplicate') or one(stage, 'stage_finished') != load(processes[stage]):
            problems.append(f'{stage} stage receipt and process record do not match one to one')
    assembled = one('assembly', 'certificate_assembled')
    if cert is not None:
        if not (isinstance(assembled, dict) and out('validated-response.json').is_file() and assembled.get('response_sha256') == sha(out('validated-response.json'))
                and 'sha256:'+str(assembled.get('certificate_sha256')) == cert.get('certificate_hash')): problems.append('certificate_assembled does not bind the response and certificate')
    elif assembled is not None: problems.append('an assembly receipt without a certificate record')
    return problems


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
    released = reconciliation.get('kind') == 'release'; attempt = attempt_of(run); limit = None  # revision 6
    if not released and not (reconciliation.get('kind') == 'send_grant' and reconciliation.get('send_outcome') == 'returned'):
        reasons.append(f"slot ended as {reconciliation.get('kind')}/{reconciliation.get('send_outcome')}, not a returned send")
    try:
        ledger_rows, s = ledger_snapshot()
        at = [i for i, r in enumerate(ledger_rows) if r == permit]; end = [i for i, r in enumerate(ledger_rows) if r == reconciliation]
        slot = s['slots'].get(f'{task_id}/{draw}') or {}; limit = s['maximum_presend_attempts']
        if not (len(at) == 1 and len(end) == 1 and at[0] < end[0]): reasons.append('the live ledger does not hold this permit and its reconciliation')
        elif released:  # revision 6: this is the slot's k-th release on the ledger, and nothing is open
            prior = [r for r in ledger_rows[:end[0]+1] if r['kind'] == 'release' and r.get('task_id') == task_id and r.get('draw') == draw]
            if len(prior) != attempt or s['open_reservations']: reasons.append(f'the ledger does not hold this release as attempt {attempt}, or a reservation is open')
        elif not slot.get('consumed') or s['open_reservations'] or slot.get('released') != attempt-1:
            reasons.append('ledger slot not consumed after its releases, or a reservation is open')
    except (ledger.Failure, OSError, ValueError, KeyError) as error:
        reasons.append(f'ledger unreadable: {error}')
    # 3. publication (the run's own synthetic-canary scan; the operator scan is pending, not failed), provider and transport
    if not (scan.get('accepted') is True and scan.get('disclosures') == [] and publication.get('report_clean') is True): reasons.append('publication scan failed')
    status = http.get('http_status'); category = summary.get('failure_category')
    bindings = (validation.get('outbound_envelope', {}).get('accepted') is True and validation.get('local_send_consistency', {}).get('accepted') is True
                and validation.get('response_request_binding', {}).get('accepted') is True)
    if released:  # revision 6: the sender's connection-phase failure before its grant, nothing sent (the amendment 2 auditor's `live_release`)
        process = load(run/'stages/proposal-1/proposal-1.process.json'); stderr = (run/'stages/proposal-1/proposal-1.stderr').read_text()
        if not (pre_grant_state(http, run/'stages/proposal-1') and category == validation.get('failure_category') == http.get('failure_category')
                and summary.get('failure_phase') == validation.get('failure_phase') == 'https_transport' and validation.get('send_outcome') == 'not_started'
                and process.get('exit_code') == 0 and stderr == '' and summary.get('credential_use_accepted') is False
                and reconciliation.get('reason') == 'pre_send_failure_with_established_termination' and reconciliation.get('termination_established') is True
                and reconciliation.get('launched') is True and reconciliation.get('send_outcome') is None):
            reasons.append('not a pre-send release: the connection-phase failure, zero sends or the release reconciliation does not hold')
    else:
        if status != 200 or summary.get('credential_use_accepted') is not True: reasons.append(f'provider status {status}')
        if not bindings: reasons.append('transport binding failure')
        if validation.get('failure_category') is not None and validation.get('failure_phase') != 'proposal':
            reasons.append(f"transport failure {validation.get('failure_category')} ({validation.get('failure_phase')})")
    if not (summary.get('evidence_complete') is True and summary.get('ledger_reconciled') is True): reasons.append('evidence incomplete or ledger not reconciled')
    # 4. the terminal receipt: the frozen live shape (`cohort_episode.finalize`, live: publication pending, not accepted), binding the summary and
    #    publication records by digest and agreeing with the summary; finished exactly when a proof is accepted with complete evidence
    shared = ('proof_accepted', 'credential_use_accepted', 'evidence_complete', 'ledger_reconciled')
    finished_expected = summary.get('proof_accepted') is True and category is None and summary.get('evidence_complete') is True and summary.get('ledger_reconciled') is True
    if not (terminal['source'] == 'supervisor' and terminal['event'] == ('episode_finished' if finished_expected else 'episode_rejected')
            and sorted(terminal_payload) == sorted(TERMINAL_KEYS) and terminal_payload.get('accepted') is False
            and terminal_payload.get('publication_pending') is True and terminal_payload.get('publication_accepted') is None
            and terminal_payload.get('summary_sha256') == contract.r6.sha(run/'credential-summary.json')
            and terminal_payload.get('publication_final_sha256') == contract.r6.sha(run/'publication-final.json')
            and terminal_payload.get('publication_scan_sha256') == contract.r6.sha(run/'publication-scan.json')
            and all(terminal_payload.get(k) is summary.get(k) for k in shared)): reasons.append('terminal receipt does not agree with the summary and publication records')
    # 4a. revision 4: every receipt in the chain that mirrors a retained record, unique and equal to it
    reasons.extend(receipts_agree(run, one, supervisor, permit, http, cert))
    # 5. the outcome: receipts, records and summary in agreement for exactly one ordinary outcome
    if receipt == 'duplicate' or refused_receipt == 'duplicate' or (receipt is None) != (cert is None) or (receipt is not None and receipt != cert):
        reasons.append('verifier receipt and certificate record disagree')
    finished = [r['payload']['data'] for r in child if r['event'] == 'reconstruction_finished']
    proof_receipt = supervisor.get(('episode', 'proof_validated'), [])
    if released:  # revision 6: a release reaches no certificate, consumer, kernel or proof record
        outcome = 'released'
        if not (cert is None and receipt is None and verdict is None and refusal is None and not reconstruct_reached and not kernels and not proof_receipt
                and summary.get('proof_accepted') is False and not (run/'response.json').exists()): reasons.append('release records are not empty past the send')
    elif category is None and summary.get('proof_accepted') is True:
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
    # 6. revision 5: the whole chain is the frozen sequence for its outcome, and its stages are exactly the run's stage records
    if outcome in SEQUENCE:
        expected = SEQUENCE[outcome]
        if [(r['source'], r['stage'], r['event']) for r in rows] != expected: reasons.append(f'the receipt sequence is not the frozen sequence for {outcome}')
        stages = sorted(st for (_, st, event) in expected if event == 'stage_finished')
        directories = sorted(p.name for p in (run/'stages').iterdir() if p.is_dir()) if (run/'stages').is_dir() else []
        processes = sorted(p.parent.name for p in run.glob('stages/*/*.process.json'))
        if not (stages == directories == processes): reasons.append(f'stage records {processes} and directories {directories} are not the sequence\'s stages {stages}')
    if outcome == 'released':  # revision 6: retry within the frozen pre-send limit; at the limit the slot is exhausted and collection pauses
        if not reasons and limit is not None and attempt >= limit: reasons.append(f'pre-send attempts exhausted ({attempt} of {limit})')
        return ('retry' if not reasons else 'pause'), outcome, reasons
    return ('continue' if not reasons and outcome in CONTINUABLE else 'pause'), outcome, reasons


def run_name(site, draw, attempt): return f'{site}-draw{draw}' if attempt == 1 else f'{site}-draw{draw}-attempt{attempt}'


def report(run, fresh, result, decision, outcome, reasons):
    _, s = ledger_snapshot()
    print(json.dumps({'run': run.name, 'fresh': fresh, **({'exit': result.returncode} if fresh else {}), 'decision': decision, 'outcome': outcome,
                      'reasons': reasons, 'consumed': s['transmissions_consumed'], 'committed_micro_usd': s['committed_micro_usd']}), flush=True)
    if decision == 'integrity_stop': raise SystemExit(f'INTEGRITY STOP at {run.name}: {reasons}; collection stops, the block needs review')
    if decision not in ('continue', 'retry'): raise SystemExit(f'PAUSE at {run.name}: {reasons}; stop and review (a restart re-applies this decision)')


def preflight(schedule):
    """Revision 7 (review P2): the whole existing population, before any sender is invoked. Every entry is a run directory with a canonical
    name (block 1's draw-1 runs, or a block 2 slot's attempt); the slots with runs are a prefix of the schedule; each slot's attempts are
    1..n, n within the pre-send limit; every attempt is gated in order, each but the last deciding `retry` and only the last slot awaiting
    one; the ledger holds a slot for exactly these block 2 slots, nothing open, each with n reservations, its releases and its consumption.
    Returns where collection resumes: (schedule index, attempt)."""
    def pause(why): raise SystemExit(f'PAUSE before any launch: {why}; stop and review')
    attempts = {}
    for entry in sorted(RUNS.iterdir()):
        parsed = NAME.fullmatch(entry.name); site, draw, k = (parsed.group(1), int(parsed.group(2)), int(parsed.group(3) or 1)) if parsed else (None, None, None)
        if not (parsed and entry.is_dir() and site in ORDER and (draw in DRAWS or (draw == 1 and k == 1)) and not entry.is_symlink()):
            pause(f'{entry.name} is not a canonical run directory of this schedule')
        if draw in DRAWS: attempts.setdefault((draw, site), []).append(k)
    existing = [slot for slot in schedule if slot in attempts]
    if existing != schedule[:len(existing)]: pause(f'the slots with runs are not a prefix of the schedule: {[run_name(s, d, 1) for d, s in existing]}')
    _, s = ledger_snapshot(); limit = s['maximum_presend_attempts']
    held = {key for key in s['slots'] if int(key.rsplit('/', 1)[1]) in DRAWS}
    if held != {f'bracket-{site}/{draw}' for draw, site in existing} or s['open_reservations']:
        pause(f'the ledger holds block 2 slots {sorted(held)} (open {s["open_reservations"]}), the runs {[run_name(s_, d, 1) for d, s_ in existing]}')
    resume = (len(existing), 1)
    for i, (draw, site) in enumerate(existing):
        ks = sorted(attempts[(draw, site)])
        if ks != list(range(1, len(ks)+1)) or len(ks) > limit: pause(f'{run_name(site, draw, 1)} attempts {ks} are not 1..n within the limit {limit}')
        decisions = []
        for k in ks:
            run = RUNS/run_name(site, draw, k); decision, outcome, reasons = gate(run, f'bracket-{site}', draw)
            report(run, False, None, decision, outcome, reasons); decisions.append(decision)
            if k < len(ks) and decision != 'retry': pause(f'an attempt follows {run.name}, which was not released')
        slot = s['slots'][f'bracket-{site}/{draw}']
        if not (slot.get('reservations') == len(ks) and slot.get('released') == decisions.count('retry') and slot.get('consumed') is (decisions[-1] == 'continue')):
            pause(f'the ledger slot {slot} disagrees with attempts {ks} decided {decisions}')
        if decisions[-1] == 'retry':
            if i != len(existing)-1: pause(f'{run_name(site, draw, ks[-1])} awaits a retry, but later slots have runs')
            resume = (i, len(ks)+1)
    print(json.dumps({'preflight': {'existing_block2_slots': len(existing), 'resume': run_name(*reversed(schedule[resume[0]]), resume[1]) if resume[0] < len(schedule) else None}}), flush=True)
    return resume


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--credential-file', type=Path, required=True)
    args = parser.parse_args()
    RUNS.mkdir(exist_ok=True)
    schedule = [(d, s) for d in DRAWS for s in ORDER]
    start, attempt = preflight(schedule)  # revision 7: nothing is launched until every existing run is inventoried and gated
    for index in range(start, len(schedule)):
        draw, site = schedule[index]; task_id = f'bracket-{site}'
        if index > start: attempt = 1
        while True:  # revision 6: a verified pre-send release is retried as the slot's next attempt directory
            run = RUNS/run_name(site, draw, attempt)
            if run.exists(): raise SystemExit(f'PAUSE: {run.name} appeared after the preflight; stop and review')
            _, s = ledger_snapshot()
            if s['open_reservations']: raise SystemExit(f'PAUSE: an open reservation exists before {run.name}: {s["open_reservations"]}')
            if attempt > 1: time.sleep(RETRY_DELAY_SECONDS)
            result = subprocess.run([sys.executable, str(R6/'cohort_episode.py'), '--mode', 'live', '--task', task_id, '--draw', str(draw),
                                     '--run-dir', str(run), '--credential-file', str(args.credential_file)], cwd=R6)
            decision, outcome, reasons = gate(run, task_id, draw)
            report(run, True, result, decision, outcome, reasons)
            if decision == 'retry': attempt += 1; continue
            break
    print(json.dumps({'block_2': 'complete', 'runs': len(ORDER)*len(DRAWS), 'next': 'the operator disclosure scan over all 88 runs, then the frozen evaluation'}), flush=True)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""R6-009 driver: one (task, draw) episode under the scientific contract and the campaign ledger.

`--mode rehearsal` runs the complete episode against a canned TLS receiver on
loopback with a synthetic canary, fully isolated, through the same grant path
the live stage uses. `--mode live` shares the network namespace for the one
proposal stage, trusts the pinned public bundle, mounts the operator's
credential file and consumes one transmission from the campaign ledger. Both
modes reserve from the same ledger for the same policy. Whatever fails, the
run is scanned, terminated with an event and sealed.

Revision 4 (R6-012) runs a verified census site under contract v2. Setup and preparation are `site_task`'s (the frozen
stages, the byte-span instrumentation); the request is policy C's; every stage runs through the site stage or the site sender
stage, each the frozen function with the supervisor line changed; final validation is the frozen one with the site stage.
A site the SDK refuses to prepare, or policy C refuses to pose, is recorded before any reservation as `interface_refused` or
`policy_refused`; the fifteen-site denominator is the reviewed one. Rehearsal responses are canned: the exact certificate
from the representability classification where one exists, and for the negative control a well-formed non-certificate.
"""
import argparse
import json
from pathlib import Path
import shutil
import tempfile
import time

import admission
import site_network as network
import cohort_budget as budget
import cohort_contract as contract
import cohort_ledger as ledger
import credential
import credential_episode as publication_driver
import episode
import events
import live_tls_fixture
import priced_payload_v2 as wire
import provider_episode as consumer
import provider_payload
import pricing_gate_v4 as gate
import publication
import run as r6
import site_request
import site_stage
import site_task

MODES = ('rehearsal', 'live')
TERMINAL_KEYS = ('accepted', 'proof_accepted', 'credential_use_accepted', 'publication_accepted', 'publication_pending',
                 'ledger_reconciled', 'evidence_complete', 'summary_sha256', 'publication_scan_sha256', 'publication_final_sha256')


def setup(run, task, packages):
    contract.verify_sources(); site_task.verify_lock()
    runtime_path, runtime = contract.materialize_runtime()
    tools = site_task.setup(run, task, packages)
    tools.update(python=Path(runtime['python']), runtime=runtime, runtime_path=runtime_path)
    binaries = r6.read_json(run/'provenance/binaries.json')
    binaries[runtime['python']] = runtime['python_sha256']
    r6.write_json(run/'provenance/binaries.json', binaries)
    r6.write_json(run/'provenance/python-runtime.json', runtime)
    r6.write_json(run/'provenance/roles.json', {'python': runtime['python'], 'runtime_path': str(runtime_path),
        'actor_source': str(r6.ROOT/'cohort_https.py'), 'network_stage': str(r6.ROOT/'campaign_network.py'),
        'ledger_module': str(r6.ROOT/'cohort_ledger.py'), 'ledger_directory': str(contract.LEDGERS), 'contract': str(contract.CONTRACT),
        'assembler': str(tools['driver']), 'verifier': str(tools['verifier']), 'checker': str(tools['checker']),
        'runtime_pin': 'cohort-runtime-v1', 'downstream_setup': 'site_task.setup: frozen proposal_episode.setup on the D1 control, site expectation substituted',
        'site_supervisor': str(r6.ROOT/'site_supervise.py'), 'site_stage': str(r6.ROOT/'site_stage.py'), 'site_network': str(r6.ROOT/'site_network.py'),
        'site_lock': str(site_task.LOCK)})
    chain = [('cohort-harness', contract, [contract.RUNTIME, contract.CONTRACT, contract.PREVIOUS_CONTRACT, r6.ROOT/contract.REQUEST_SCHEMA_PATH]),
             ('site-harness', site_task, [site_task.MEMBERSHIP_DECISION, site_task.ADDENDUM])]
    module = contract.previous
    while module is not None:
        name = module.__name__.replace('_contract', '').replace('_', '-')
        extra = [module.RUNTIME] if getattr(module, 'RUNTIME', None) and Path(module.RUNTIME).exists() else []
        chain.append((name+'-harness', module, extra))
        module = getattr(module, 'previous', None)
    for section, module, extra in chain:
        for source in [r6.ROOT/name for name in module.FILES]+[getattr(module, 'CONFIG', None), module.LOCK]+extra:
            if source is None: continue
            target = run/'provenance'/section/source.relative_to(r6.ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
    return tools


def prepare(run, task, tools):
    prepared, _ = site_task.prepare(run, task, tools)
    request, evidence = budget.request(task, prepared)
    r6.write_json(run/'policy-c-evidence.json', evidence)
    (run/'live-request.json').write_bytes(request)
    args = budget.arguments(request)
    r6.write_json(run/'live-arguments.json', args)
    r6.write_json(run/'live-messages.json', args['input'])
    record = {'request_sha256': gate.sha(request), 'policy_sha256': contract.policy_sha256(), 'contract_sha256': contract.contract_sha256(),
              'prompt_sha256': r6.sha(contract.PROMPT), 'arguments_sha256': r6.sha(run/'live-arguments.json'),
              'messages_sha256': r6.sha(run/'live-messages.json'), 'prepared_sha256': r6.sha(run/'prepared.json'),
              'policy_c_evidence_sha256': r6.sha(run/'policy-c-evidence.json'), 'payload_audit_sha256': r6.sha(run/'payload-audit.json'),
              'inner_binding': 'request contract_sha256 is the scientific contract; no policy digest is model-visible'}
    r6.write_json(run/'live-payload.json', record)
    events.append(run, 'live-payload', 'payload_validated', record)
    return request


def canned(task, request):
    """A rehearsal response for a site: the exact certificate from the classification (`contract.REPRESENTABILITY`) where one exists; for the negative
    control, whose rows have no certificate, a well-formed witness that is not one. Evaluator-only; never a live input."""
    record = r6.read_json(contract.REPRESENTABILITY/task.id/'representability.json')
    coefficients = record.get('certificate') or [{'hypothesis': 'neg_goal', 'coefficient': '1'}]
    witness = {'request_sha256': gate.sha(request), 'witness': {'coefficients': coefficients}}
    text = (events.canonical(witness)+b'\n').decode()
    response = {'id': 'r6_canned_response', 'object': 'response', 'model': contract.MODEL, 'service_tier': 'default', 'status': 'completed',
                'error': None, 'incomplete_details': None,
                'output': [{'type': 'message', 'id': 'r6_message', 'status': 'completed', 'role': 'assistant',
                            'content': [{'type': 'output_text', 'text': text, 'annotations': []}]}],
                'usage': {'input_tokens': 11, 'output_tokens': 7, 'total_tokens': 18,
                          'input_tokens_details': {'cached_tokens': 2}, 'output_tokens_details': {'reasoning_tokens': 3}}}
    return {'status': 200, 'body': (events.canonical(response)+b'\n').decode()}


def failure(category, phase, message):
    return wire.Failure(category, phase, message)


RECONSTRUCTED = ['reification_started', 'reification_finished', 'dispatch_started', 'dispatch_received', 'certificate_verification_started',
                 'certificate_verification_finished', 'reconstruction_started']
NAT_SHAPE_REFUSAL = 'proof_broker_term: non-False ℕ goal must have shape'


def reconstruction_observed(run):
    return [(r['event'], r['payload']['data']) for r in events.read(run/'events.ndjson') if r['source'] == 'child_report' and r['stage'] == 'reconstruct']


def consumption_receipt(run, packet):
    """The closer's own success receipt (revision 6): exactly one closer selected and one `reconstruction_finished` after it, both naming this
    packet's certificate and the same closer, with consumption stated. A kernel success without it is not a demonstrated consumption."""
    observed = reconstruction_observed(run); names = [e for e, _ in observed]
    selected = [d for e, d in observed if e == 'closer_selected']; finished = [d for e, d in observed if e == 'reconstruction_finished']
    if not (names[:len(RECONSTRUCTED)] == RECONSTRUCTED and len(selected) == 1 and len(finished) == 1
            and names.index('closer_selected') < names.index('reconstruction_finished') == len(names)-1
            and selected[0]['certificate'] == finished[0]['certificate'] == packet['certificate'] and selected[0]['closer'] == finished[0]['closer']
            and finished[0]['certificate_consumed'] is True):
        raise wire.Failure('consumption_unobserved', 'reconstruction', 'no closer-specific consumption receipt for this certificate')
    return finished[0]


def reconstruction_refusal(run, packet):
    """The pinned ℕ closer's goal-shape refusal, from bound evidence only: the reified IR reached dispatch unchanged (the guard passed), the
    bridge verified this certificate, the ℕ closer was selected for a comparison whose carrier is not ℕ, the stage exited 1 on its own (no
    exhaustion, violation, monitor or observation failure), no consumption receipt, and the one error is that closer's message. Anything
    else is not this refusal: None."""
    observed = reconstruction_observed(run); names = [e for e, _ in observed]; data = dict(observed)
    record = run/'stages/reconstruct'; process = r6.read_json(record/'reconstruct.process.json')
    log = (record/'reconstruct.stdout').read_text()+(record/'reconstruct.stderr').read_text()
    errors = [line for line in log.splitlines() if ': error: ' in line]
    selected = data.get('closer_selected') or {}
    if not (names == RECONSTRUCTED+['closer_selected'] and data['dispatch_started']['ir'] == packet['input_ir']
            and data['certificate_verification_finished'].get('ok') is True and data['certificate_verification_finished'].get('envelope_ok') is True
            and data['reconstruction_started']['certificate'] == selected.get('certificate') == packet['certificate']
            and process['exit_code'] == 1 and process['resource_exhausted'] is None and process['resource_violations'] == []
            and process['monitor_error'] is None and process['observation_error'] is None and process['workload_empty_after_cleanup'] is True
            and selected.get('closer') == 'term_mode_nat' and selected.get('comparison_type') not in (None, 'ℕ', 'Nat')
            and len(errors) == 1 and NAT_SHAPE_REFUSAL in errors[0]):
        return None
    return {'diagnosis': 'nat_closer_int_goal' if selected['comparison_type'] in ('ℤ', 'Int') else 'nat_closer_non_nat_goal',
            'closer': selected['closer'], 'comparison_type': selected['comparison_type'], 'goal': selected['goal'],
            'certificate_sha256': events.digest(packet['certificate']), 'error_line': errors[0][:500],
            'process_sha256': r6.sha(record/'reconstruct.process.json'), 'stdout_sha256': r6.sha(record/'reconstruct.stdout'),
            'stderr_sha256': r6.sha(record/'reconstruct.stderr'), 'scope': 'pinned tactic behavior at e627efe; not a witness failure'}


def relative(path):
    return str(path.relative_to(r6.ROOT)) if path.is_relative_to(r6.ROOT) else str(path)


def safe_sha(path):
    try: return r6.sha(path) if Path(path).is_file() else None
    except OSError: return None


NoneType = type(None)
SCHEMAS = {
    'process': {'exit_code': int, 'workload_empty_after_cleanup': bool, 'monitor_error': (str, NoneType), 'observation_error': (str, NoneType),
                'accounting_scope': str},
    'http': {'connection_attempts': int, 'header_sends_started': int, 'header_sends_returned': int, 'body_sends_started': int,
             'body_sends_returned': int, 'failure_category': (str, NoneType), 'http_status': (int, NoneType), 'grant_committed': bool,
             'send_outcome': str, 'mode': str, 'request_sha256': str, 'credential_commitment_sha256': (str, NoneType), 'commitment_nonce': str,
             'reservation_id': (str, NoneType), 'tls_verified_at_ns': (int, NoneType), 'header_send_at_ns': (int, NoneType)},
    'server': {'requests': list, 'server_names': list}}


def read_record(path, schema=None):
    """A record that is missing, truncated, malformed, unreadable, not an object, or missing required fields is evidence, not an exception."""
    path = Path(path)
    if not path.exists(): return None, None
    try: value = r6.read_json(path)
    except (ValueError, OSError, UnicodeError) as error:
        return None, {'path': path.name, 'error': type(error).__name__, 'sha256': safe_sha(path)}
    if not isinstance(value, dict):
        return None, {'path': path.name, 'error': 'not_an_object', 'sha256': safe_sha(path)}
    if schema is not None:
        bad = {k: ('missing' if k not in value else type(value[k]).__name__) for k, t in SCHEMAS[schema].items()
               if k not in value or not isinstance(value[k], t) or (isinstance(value[k], bool) and t is int)}
        if bad: return None, {'path': path.name, 'error': 'schema', 'fields': bad, 'sha256': safe_sha(path)}
    return value, None


def reconcile(run, permit, live, lifecycle):
    """After the sender terminated, or failed to: the authoritative slot decides; every record read failure is retained.
    The disposition is owned the moment the terminal row commits; evidence copies that fail afterwards are recorded, never
    mistaken for an open reservation."""
    stage = run/'stages/proposal-1'; book = contract.campaign_ledger(live); slot = book.grant_slot(permit)
    process, process_failure = read_record(stage/'proposal-1.process.json', 'process')
    http, http_failure = read_record(stage/'output/http.json', 'http')
    launched = (stage/'command.json').exists()  # written by the stage before any process is spawned
    evidence = {'process_sha256': safe_sha(stage/'proposal-1.process.json'), 'http_sha256': safe_sha(stage/'output/http.json'),
                'grant_file_sha256': safe_sha(slot/ledger.GRANT_FILE), 'launched': launched,
                'process_exit_code': None if process is None else process.get('exit_code'),
                'record_read_failures': [f for f in (process_failure, http_failure) if f is not None]}
    try:
        row, raw = book.reconcile(permit, process, http, evidence, launched)
    except Exception as caught:
        row = book.find_terminal(permit['reservation_id'])  # the append may have committed before the exception
        if row is None: raise
        lifecycle['reconciliation'] = row; lifecycle['reconcile_recovered'] = type(caught).__name__  # known before any further read
        try: raw = book.snapshot()[0]
        except Exception as second: raw = None; lifecycle['snapshot_failure'] = type(second).__name__
    lifecycle['reconciliation'] = row
    failures = [] if raw is not None else [{'artifact': 'ledger-after', 'error': lifecycle.get('snapshot_failure', 'unavailable')}]
    def attempt(label, fn):
        try: fn()
        except Exception as caught: failures.append({'artifact': label, 'error': type(caught).__name__})
    def copy_slot():
        retained = stage/'grant'; retained.mkdir(parents=True, exist_ok=True); missed = []
        for item in sorted(slot.iterdir()):
            if item.is_file():
                try: shutil.copyfile(item, retained/item.name)
                except OSError: (retained/(item.name+'.unreadable')).write_bytes(b''); missed.append(item.name)
        if missed: raise OSError(5, 'slot files not copied: '+', '.join(missed))
    attempt('grant-copy', copy_slot)
    if raw is not None: attempt('ledger-after', lambda: (run/'ledger-after.ndjson').write_bytes(raw))
    attempt('campaign-reconciliation', lambda: r6.write_json(run/'campaign-reconciliation.json', row))
    lifecycle['evidence_write_failures'] = failures
    attempt('reservation_reconciled-event', lambda: events.append(run, 'campaign-ledger', 'reservation_reconciled', {'kind': row['kind'],
        'reservation_id': row['reservation_id'], 'row_hash': row['row_hash'], 'send_outcome': row.get('send_outcome'),
        'termination_established': row['termination_established'], 'record_read_failures': len(evidence['record_read_failures']),
        'evidence_write_failures': [f['artifact'] for f in failures if f['artifact'] != 'reservation_reconciled-event'],
        'ledger_sha256': safe_sha(run/'ledger-after.ndjson'), 'recovered': lifecycle.get('reconcile_recovered')}))
    return row


def accounting_for(run, c, live, http, server, lifecycle):
    """Total over any evidence: observed facts stay observed, unobserved ones are null, and the allowance disposition comes from
    the authoritative reconciliation. `allowance_consumed` is the one allowance field: 1, 0, or null when unknown."""
    reconciliation = lifecycle.get('reconciliation'); permit = lifecycle.get('permit')
    usage, status, estimate = provider_payload.usage({}), 'unreported', None
    raw = run/'stages/proposal-1/output/provider-response.json'
    if raw.exists():
        try: usage = provider_payload.usage(json.loads(raw.read_bytes())); status = usage['status']
        except (ValueError, AttributeError, TypeError, OSError, KeyError): status = 'invalid'
    try:
        if usage['input_tokens'] is not None and usage['output_tokens'] is not None:
            estimate = gate.cost_micro(usage['input_tokens'], usage['output_tokens'], c['pricing']['nano_usd_per_token'])
    except (TypeError, KeyError, ValueError): estimate = None
    observed = isinstance(http, dict)
    get = (lambda key: http.get(key)) if observed else (lambda key: None)
    state = lifecycle.get('reservation_state', 'reserved' if permit else 'not_reserved')
    if state == 'reserved' and permit is None: state = 'unknown'  # a reserved state without its permit is not a known reservation
    reserved = permit is not None or state == 'unknown'
    grant_committed = (reconciliation['kind'] == 'send_grant') if reconciliation else (get('grant_committed') if observed else None)
    send_outcome = (reconciliation.get('send_outcome') if reconciliation and reconciliation['kind'] == 'send_grant'
                    else ('not_started' if reconciliation and reconciliation['kind'] == 'release' else get('send_outcome')))
    consumed = 1 if reconciliation and reconciliation['kind'] in ('send_grant', 'unknown') else (0 if reconciliation else None)
    reconciled = reconciliation is not None or (permit is None and state == 'not_reserved')
    reconciliation_evidence = not lifecycle.get('evidence_write_failures')
    return {'attempts_reserved': 1 if permit else (None if state == 'unknown' else 0),
            'reservation_state': state,
            'reservation': lifecycle.get('reservation'), 'reservation_id': permit['reservation_id'] if permit else None,
            'transport_record_observed': observed,
            'connection_attempts': get('connection_attempts'), 'headers_started': get('header_sends_started'),
            'transmissions_observed': get('body_sends_started'), 'transmissions_returned': get('body_sends_returned'),
            'grant_committed': grant_committed, 'send_outcome': send_outcome,
            'ledger_outcome': reconciliation['kind'] if reconciliation else None,
            'ledger_reconciled': reconciled,
            'reconciliation_evidence_complete': reconciliation_evidence,
            # whole-episode predicate: the reservation is known, the ledger disposition is known, every reconciliation artifact was written
            'evidence_complete': state != 'unknown' and reconciled and reconciliation_evidence,
            'allowance_consumed': consumed, 'endpoint_receipts': len(server['requests']) if isinstance(server, dict) and isinstance(server.get('requests'), list) else None,
            'usage': usage, 'usage_status': status, 'priced_usage_ceiling_micro_usd': estimate, 'live': live,
            'live_usage_ceiling_usd': None if not live else (None if estimate is None else estimate/1e6),
            'scope': ('one authorized provider transmission; the ceiling prices reported usage and is not a bill; allowance_consumed is the '
                      'authoritative disposition (null when unknown), transmissions_observed the sender\'s own count or null when unobserved'
                      if live else 'rehearsal against a local canned receiver; no live transmission, no cost')}


def recover_reservation(run, live, lifecycle, caught):
    """An uncertain reserve(): the ledger, not the exception, says whether the row committed. The state is unknown before any
    fallible diagnostic, the recovered permit is retained before any receipt, and receipts are written later under the
    reconciliation guard so that a failed receipt can never decide whether reconciliation runs."""
    lifecycle['reservation_state'] = 'unknown'; lifecycle['uncertain'] = type(caught).__name__
    try:
        book = contract.campaign_ledger(live); row = book.find_open(lifecycle['attempt_id'])
    except Exception as second:
        lifecycle['reservation_error'] = type(second).__name__
        return None, None, None
    if row is None:
        lifecycle['reservation_state'] = 'not_reserved'; return None, None, None
    lifecycle['permit'] = row; lifecycle['reservation_state'] = 'reserved'; lifecycle['reservation_recovered'] = type(caught).__name__
    try: raw = book.snapshot()[0]
    except Exception: raw = None
    return row, raw, row['pricing_admission']


def refused_before_reservation(run, c, live, nonce, lifecycle, state, refused):
    pricing = isinstance(refused, gate.Failure)
    code = refused.code if isinstance(refused, (gate.Failure, ledger.Failure)) else type(refused).__name__
    if lifecycle.get('uncertain'):
        events.append(run, 'campaign-ledger', 'reservation_uncertain', {'attempt_id': lifecycle['attempt_id'], 'error': lifecycle['uncertain'],
                      'resolved_state': state, 'ledger_error': lifecycle.get('reservation_error')})
    denied = {'accepted': False, 'failure_code': code, 'evaluated_at_unix': time.time(), 'reservation_state': state,
              'stage': 'pricing_admission' if pricing else 'cohort_ledger'}
    r6.write_json(run/'host-pricing-admission.json', denied)
    events.append(run, 'pricing-admission' if pricing else 'campaign-ledger', 'pricing_rejected' if pricing else 'reservation_refused', denied)
    receipt = publication_driver.receipt(run, {'requests': []}, credential.derive(nonce), 'rehearsal') if not live else live_receipt(run, None)
    accounting = accounting_for(run, c, live, None, None, lifecycle)
    r6.write_json(run/'accounting.json', accounting)
    category = ('contract_admission' if pricing and code.startswith(('contract_', 'policy_')) else 'pricing_admission') if pricing else ('reservation_state_unknown' if state == 'unknown' else 'cohort_ledger')
    return None, failure(category, 'pricing_admission' if pricing else 'cohort_ledger',
                         ('Pricing admission: ' if pricing else 'Campaign ledger: ')+code), receipt, accounting


def invoke(run, tools, mode, nonce, credential_file, lifecycle, task_id, draw):
    c = contract.config(); runtime = tools['runtime']; limits = c['limits']
    live = mode == 'live'
    request = (run/'live-request.json').read_bytes()
    shutil.copytree(contract.sources(c), run/'pricing-sources')
    lifecycle['attempt_id'] = credential.nonce()  # transaction identity, chosen before any ledger effect
    events.append(run, 'campaign-ledger', 'reservation_attempted', {'attempt_id': lifecycle['attempt_id']})
    try:
        row, raw, admitted = budget.reserve(run.name, task_id, draw, r6.read_json(run/'live-arguments.json'), request, run/'pricing-sources', live,
                                            lifecycle['attempt_id'])
    except (gate.Failure, ledger.Failure) as refused:
        if not isinstance(refused, gate.Failure) and refused.code not in ('cohort_ledger_not_activated', 'cohort_reservation_open', 'cohort_slot_consumed',
                'cohort_slot_not_scheduled', 'cohort_presend_attempts_exhausted', 'cohort_money_exhausted', 'cohort_missing_episode_identity', 'cohort_revision_not_current'):
            row, raw, admitted = recover_reservation(run, live, lifecycle, refused)  # anything else may have committed
            if row is None:
                return refused_before_reservation(run, c, live, nonce, lifecycle, lifecycle.get('reservation_state', 'not_reserved'), refused)
        else:
            return refused_before_reservation(run, c, live, nonce, lifecycle, 'not_reserved', refused)
    except Exception as uncertain:  # the append may have committed: resolve by attempt identity, never by the exception
        row, raw, admitted = recover_reservation(run, live, lifecycle, uncertain)
        if row is None:
            return refused_before_reservation(run, c, live, nonce, lifecycle, lifecycle.get('reservation_state', 'not_reserved'), uncertain)
    # From here the reservation is owned: whatever happens below, reconciliation is attempted before this function returns.
    lifecycle['permit'] = row; lifecycle['reservation_state'] = 'reserved'
    stage_error = None; canary = None
    try:
        if lifecycle.get('reservation_recovered'):  # an uncertain ledger return is a reason to stop, not to send
            events.append(run, 'campaign-ledger', 'reservation_uncertain', {'attempt_id': lifecycle['attempt_id'], 'error': lifecycle['reservation_recovered'], 'resolved_state': 'reserved'})
            events.append(run, 'campaign-ledger', 'reservation_recovered', {'attempt_id': lifecycle['attempt_id'], 'reservation_id': row['reservation_id']})
            raise episode.StageFailure('proposal-1', 'harness_failure', 'reservation recovered after an uncertain ledger return; sender not launched')
        r6.write_json(run/'host-pricing-admission.json', admitted)
        events.append(run, 'pricing-admission', 'pricing_admitted', {'admission_sha256': r6.sha(run/'host-pricing-admission.json')})
        r6.write_json(run/'campaign-permit.json', row)
        (run/'transport-ledger.ndjson').write_bytes(raw)
        reservation = {**row['reservation'], 'reservation_id': row['reservation_id'], 'request_sha256': row['request_sha256'],
                       'arguments_sha256': row['arguments_sha256'], 'policy_sha256': row['policy_sha256'],
                       'pricing_admission_sha256': r6.sha(run/'host-pricing-admission.json'), 'ledger_row_hash': row['row_hash'],
                       'ledger_sha256': r6.sha(run/'transport-ledger.ndjson')}
        lifecycle['reservation'] = {k: reservation[k] for k in reservation}
        r6.write_json(run/'reservation.json', reservation)
        events.append(run, 'campaign-ledger', 'request_reserved', reservation)
        shutil.copytree(run/'pricing-sources', run/'transport-pricing-sources')
        shutil.copyfile(run/'live-arguments.json', run/'transport-arguments.json')
        (run/'transport-request.json').write_bytes(request)
        shutil.copyfile(contract.CONFIG, run/'transport-policy.json')  # byte-identical: the actor digests it
        commitment_nonce = credential.nonce()
        book = contract.campaign_ledger(live); slot = book.grant_slot(row)
        shutil.copyfile(contract.CONTRACT, run/'transport-contract.json'); shutil.copyfile(contract.PROMPT, run/'transport-instruction.txt')
        common = [(tools['runtime_path'], runtime['stdlib']), (r6.ROOT/'cohort_https.py', '/adapter.py'),
                  (r6.ROOT/'live_https.py', '/live_https.py'), (r6.ROOT/'pricing_gate_v2.py', '/pricing_gate_v2.py'),
                  (r6.ROOT/'pricing_gate_v4.py', '/pricing_gate_v4.py'), (r6.ROOT/'campaign_ledger.py', '/campaign_ledger.py'),
                  (r6.ROOT/'cohort_ledger.py', '/cohort_ledger.py'),
                  (run/'transport-policy.json', '/policy.json'), (run/'transport-contract.json', '/contract.json'),
                  (run/'transport-instruction.txt', '/instruction.txt'), (run/'transport-arguments.json', '/arguments.json'),
                  (run/'transport-request.json', '/request.json'), (run/'transport-pricing-sources', '/pricing-sources'),
                  (run/'campaign-permit.json', '/permit.json'), (book.path, '/ledger.ndjson')]  # the authoritative file, read-only
        argv = ['-I', '-S', '-B', '/adapter.py', '--mode', mode, '--policy', '/policy.json', '--contract', '/contract.json', '--instruction', '/instruction.txt',
                '--arguments', '/arguments.json', '--credential-file', '/credential', '--ca', '/ca.pem', '--out', '/out', '--request', '/request.json',
                '--sources', '/pricing-sources', '--permit', '/permit.json', '--ledger', '/ledger.ndjson', '--episode', run.name,
                '--task', task_id, '--draw', str(draw), '--grant', '/grant', '--commitment-nonce', commitment_nonce]
        budgets = dict(extra_binaries=[Path(p) for p in runtime['extension_binaries']], wall=limits['request_wall_seconds'],
                       cpu=limits['request_cpu_seconds'], memory=limits['request_memory_bytes'],
                       output_limit=limits['request_output_bytes'])
        if live:
            ca_path, described = contract.bundle()
            if described['sha256'] != c['tls']['public_ca_bundle']['sha256']: raise ValueError('campaign_ca_bundle_binding')
            events.append(run, 'proposal', 'live_transport_authorized', {
                'approved_by': c['authorization']['approved_by'], 'approved_utc': c['authorization']['approved_utc'],
                'ca_bundle_sha256': described['sha256'], 'network_namespace': 'shared_with_host',
                'reservation_id': row['reservation_id'], 'slot': {'task_id': task_id, 'draw': draw}, 'commitment_nonce': commitment_nonce,
                'credential_source': 'operator file; value never copied'})
            network.stage(run, 'proposal-1', tools['python'], argv,
                          [*common, (Path(credential_file), '/credential'), (ca_path, '/ca.pem')], slot, shared_network=True, **budgets)
        else:
            r6.write_json(run/'canned-provider.json', canned(site_task.get(r6.read_json(run/'search-policy.json')['task_id']), request))
            argv += ['--fixture', '/fixture.json', '--server-cert', '/server.pem', '--server-key', '/server.key']
            with credential.delivery(nonce) as (canary, secret), live_tls_fixture.materialize(run, 'valid') as (ca, cert, key):
                credential_path = Path(credential_file) if credential_file is not None else secret  # a test may supply a malformed file
                network.stage(run, 'proposal-1', tools['python'], argv,
                              [*common, (run/'canned-provider.json', '/fixture.json'), (credential_path, '/credential'),
                               (ca, '/ca.pem'), (cert, '/server.pem'), (key, '/server.key')], slot, shared_network=False, **budgets)
    except episode.StageFailure as caught:
        stage_error = caught
    except Exception as caught:  # whatever stopped the launch, the reservation is reconciled before anything else
        stage_error = episode.StageFailure('proposal-1', 'harness_failure', type(caught).__name__+': '+str(caught)[:500])
    try:
        reconcile(run, row, live, lifecycle)
    except Exception as caught:
        if lifecycle.get('reconciliation') is None:  # nothing committed: the reservation stays open and the record says so
            lifecycle['reconcile_error'] = type(caught).__name__+': '+str(caught)[:500]
            try: events.append(run, 'campaign-ledger', 'reconciliation_failed', {'reservation_id': row['reservation_id'], 'error': type(caught).__name__})
            except Exception: pass
        else:  # the disposition committed; whatever failed afterwards is an evidence failure, never an open reservation
            lifecycle.setdefault('evidence_write_failures', []).append({'artifact': 'reconciliation-evidence', 'error': type(caught).__name__})
    out = run/'stages/proposal-1/output'
    http, http_failure = read_record(out/'http.json', 'http')
    server, _ = read_record(out/'server.json', 'server')
    if lifecycle['reconcile_error'] is not None:
        accounting = accounting_for(run, c, live, http, server, lifecycle); r6.write_json(run/'accounting.json', accounting)
        receipt = live_receipt(run, http) if live else publication_driver.receipt(run, server or {'requests': []}, canary or credential.derive(nonce), mode)
        return None, failure('reconciliation_failure', 'cohort_ledger', 'Reservation left open: '+lifecycle['reconcile_error']), receipt, accounting
    if lifecycle.get('evidence_write_failures') and stage_error is None and (http is None or http.get('failure_category')):
        stage_error = episode.StageFailure('proposal-1', 'evidence_incomplete', 'reconciliation evidence incomplete: '
                                           +', '.join(f['artifact'] for f in lifecycle['evidence_write_failures']))
    if http is None:
        accounting = accounting_for(run, c, live, None, None, lifecycle); r6.write_json(run/'accounting.json', accounting)
        receipt = live_receipt(run, None) if live else publication_driver.receipt(run, {'requests': []}, canary or credential.derive(nonce), mode)
        category = 'transport_record_unreadable' if http_failure else (stage_error.category if stage_error else 'https_transport')
        detail = ('unusable transport record: '+http_failure['error']+str(http_failure.get('fields', ''))) if http_failure else (str(stage_error) if stage_error else 'proposal stage left no transport record')
        return None, failure(category, 'https_transport', detail), receipt, accounting
    if server is None: server = {'requests': []}
    events.append(run, 'proposal', 'https_observed', {'http_sha256': r6.sha(out/'http.json'),
        'server_sha256': safe_sha(out/'server.json'), 'pricing_check_sha256': safe_sha(out/'pricing-check.json')})
    proposed, text, metadata, validation, error = budget.interpret(out, request, live)
    r6.write_json(run/'transport-validation.json', validation); r6.write_json(run/'provider-metadata.json', metadata)
    if text is not None: (run/'response.json').write_bytes(text)
    events.append(run, 'proposal', 'transport_validated', validation)
    if live:
        receipt = live_receipt(run, http)
    else:
        receipt = publication_driver.receipt(run, server, canary or credential.derive(nonce), mode)
        if error is None and not receipt['exact_receipt']:
            error = failure('credential_receipt_failure', 'credential_receipt', 'Endpoint did not receive the expected credential')
    if error is None and stage_error is not None:
        error = failure(stage_error.category, 'https_transport', str(stage_error))
    accounting = accounting_for(run, c, live, http, server, lifecycle)
    r6.write_json(run/'accounting.json', accounting)
    return proposed, error, receipt, accounting


def live_receipt(run, http):
    """What a real provider lets us observe: use of the credential, not exact receipt of it."""
    status = None if http is None else http['http_status']
    value = {'schema_version': 'r6-campaign-credential-use-1', 'channel': 'operator_credential_file',
             'http_status': status, 'credential_use_accepted': status is not None and 200 <= status < 300,
             'exact_receipt': None, 'credential_commitment_sha256': None if http is None else http.get('credential_commitment_sha256'),
             'commitment_nonce': None if http is None else http.get('commitment_nonce'),
             'evidence_scope': 'a 2xx provider status is evidence that the request was authenticated and processed; it is not a '
                               'digest-matched receipt of a particular credential, and 4xx/5xx statuses other than 401 are not receipts either'}
    r6.write_json(run/'credential-receipt.json', value)
    events.append(run, 'credential-receipt', 'credential_use_checked', value)
    return value


def consume(run, task, tools, response, proposer, route):
    """provider_episode.consume with attribution passed through instead of hardcoded."""
    r6.write_json(run/'validated-response.json', response)
    assembled = site_stage.stage(run, 'assembly', tools['driver'],
        ['assemble', '/prepared.json', '/response.json', 'sha256:'+r6.sha(consumer.contract.CONFIG), '/out/evidence.json'],
        [(run/'prepared.json', '/prepared.json'), (run/'validated-response.json', '/response.json')])
    shutil.copyfile(assembled/'evidence.json', run/'evidence.json')
    packet = r6.read_json(run/'evidence.json')
    events.append(run, 'assembly', 'certificate_assembled', {'certificate_sha256': events.digest(packet['certificate']),
        'witness_proposer': proposer, 'certificate_assembler': 'sdk_proposal_assembler_v1',
        'consumer_route': consumer.contract.NAME, 'response_sha256': r6.sha(run/'validated-response.json')})
    try:
        verified = site_stage.stage(run, 'certificate-check', tools['verifier'], ['/evidence.json', '/out/verdict.json'],
                                 [(run/'evidence.json', '/evidence.json')])
    except episode.StageFailure as error:
        if error.category != 'stage_rejected': raise
        verified = run/'stages/certificate-check/output'
    report = r6.read_json(verified/'verdict.json')
    r6.write_json(run/'certificate-verdict.json', report)
    events.append(run, 'certificate-check', 'independent_certificate_verdict', report)
    events.append(run, 'proposal', 'recovery_finished', {'route': route, 'consumer_route': consumer.contract.NAME,
        'ok': report['accepted'], 'witness': response['witness'], 'reason': report.get('reason'), 'proposer': proposer})
    if report['accepted'] is not True:
        raise consumer.wire.Failure('certificate_verification', 'certificate-check', 'Farkas witness was not verified', report)
    inputs = site_task.compile_input(run, 'input', 'ProposalCapture', site_task.capture_source(task), task)
    compiler = tools['compiler']
    mounts = [*tools['mounts'], (inputs, '/input')]
    built = site_stage.stage(run, 'capture-build', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', '/out/ProposalCapture.olean', '/input/ProposalCapture.lean'],
        mounts, compiler=compiler, env={'LEAN_PATH': tools['lean_path']+':/out'}, extra_binaries=tools['extras'])
    try:
        reconstructed = site_stage.stage(run, 'reconstruct', compiler/'bin/lean',
            [*tools['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
            [*mounts, (built, '/capture'), (run/'evidence.json', '/evidence.json')], compiler=compiler,
            extra_binaries=tools['extras'], capture_events=True,
            env={'LEAN_PATH': tools['lean_path']+':/capture', 'R6_PROPOSAL_PACKET': '/evidence.json',
                 'PROOF_BROKER_EPISODE_TRACE': '1', 'R6_CAPTURE_OUTPUT': '/out/context.json'})
    except episode.StageFailure as error:
        refusal = reconstruction_refusal(run, packet) if error.category == 'stage_rejected' else None
        if refusal is None: raise
        r6.write_json(run/'reconstruction-refusal.json', refusal)
        events.append(run, 'reconstruct', 'reconstruction_refused', refusal)
        raise wire.Failure('reconstruction_refused', 'reconstruction', f"pinned {refusal['closer']} closer refused the goal ({refusal['diagnosis']})")
    receipt = consumption_receipt(run, packet)
    consumer.require(r6.read_json(reconstructed/'context.json') == r6.read_json(task.path/'context/local-context.json'),
                     'reconstruction changed frozen context')
    events.append(run, 'reconstruct', 'context_validated', {'captured_context_sha256': r6.sha(reconstructed/'context.json'),
        'frozen_context_sha256': r6.sha(task.path/'context/local-context.json')})
    exported = site_stage.stage(run, 'export', tools['exporter'], ['Frozen', '--', task.whole, task.local, *r6.EXPORT_TARGETS],
        [*tools['mounts'], (reconstructed, '/objects'), (built, '/capture')], compiler=compiler,
        extra_binaries=tools['extras'], env={'LEAN_PATH': tools['lean_path']+':/capture:/objects'})
    solution = exported.parent/'export.stdout'
    r6.pack(solution, run/'solution.ndjson.gz')
    with tempfile.TemporaryDirectory(prefix='r6-campaign-challenge-') as temp:
        challenge = Path(temp)/'challenge.ndjson'
        r6.unpack(task.path/'challenge.ndjson.gz', challenge)
        consumer.require(r6.sha(challenge) == tools['expected']['challenge_sha256'], 'challenge changed')
        reports, delta = network.final_validation(run, challenge, solution, tools['checker'], tools['expected'], task)
    return packet, report, reports, delta, r6.sha(solution), receipt


def finalize(run, canary, nonce, summary, live):
    """Scan, terminal event, seal — on every path. In live mode the synthetic scan is structural, not an admission gate."""
    report = publication.scan([run], canary, nonce)
    r6.write_json(run/'publication-scan.json', report)
    final = publication.final_record(run/'publication-scan.json', canary, nonce)
    r6.write_json(run/'publication-final.json', final)
    publication_ok = None if live else bool(report['accepted'] and final['report_clean'])
    evidence_ok = bool(summary['ledger_reconciled']) and bool(summary['evidence_complete'])
    accepted = bool(summary['proof_accepted'] and summary['credential_use_accepted'] and publication_ok and evidence_ok)
    payload = {'accepted': accepted, 'proof_accepted': bool(summary['proof_accepted']),
        'credential_use_accepted': bool(summary['credential_use_accepted']), 'publication_accepted': publication_ok,
        'publication_pending': live, 'ledger_reconciled': bool(summary['ledger_reconciled']), 'evidence_complete': evidence_ok,
        'summary_sha256': r6.sha(run/'credential-summary.json'), 'publication_scan_sha256': r6.sha(run/'publication-scan.json'),
        'publication_final_sha256': r6.sha(run/'publication-final.json')}
    publication_driver.require(publication.safe_record(payload, TERMINAL_KEYS), 'terminal receipt carries an unrestricted value')
    completed = summary['proof_accepted'] and summary['failure_category'] is None and (publication_ok is not False) and evidence_ok
    events.append(run, 'episode', 'episode_finished' if completed else 'episode_rejected', payload)
    network.seal(run, accepted)
    return accepted, report, final


def execute(run, task, draw, mode, packages, credential_file):
    if mode not in MODES: raise ValueError('Unknown mode')
    if task.id not in site_task.primary(): raise ValueError('Task outside the reviewed census population')
    tools = setup(run, task, packages)
    c = contract.config(); nonce = credential.nonce(); live = mode == 'live'
    if live:
        contract.live_permitted(c)
        if credential_file is None: raise ValueError('live mode requires --credential-file')
    shutil.copytree(contract.sources(c), run/'pricing-origin')
    r6.write_json(run/'credential-canary.json', credential.record(nonce))
    policy = {'name': contract.NAME, 'mode': mode, 'task_id': task.id, 'draw': draw, 'config_sha256': contract.policy_sha256(),
              'contract_sha256': contract.contract_sha256(), 'campaign_id': c['campaign']['id'], 'revision': c['revision'],
              'source_lock_sha256': r6.sha(contract.LOCK), 'manifest_sha256': r6.sha(task.path/'manifest.json'),
              'ledger_path': relative(contract.campaign_ledger(live).path), 'ledger_slots': relative(contract.campaign_ledger(live).slots),
              'ledger_scope': 'live authorization ledger' if live else 'rehearsal ledger; never funds a transmission'}
    r6.write_json(run/'search-policy.json', policy)
    events.append(run, 'episode', 'episode_started', {'policy_sha256': r6.sha(run/'search-policy.json'),
        'challenge_sha256': tools['expected']['challenge_sha256'], 'nonce': nonce, 'mode': mode}, task_id=task.id)
    proposer = c['attribution']['witness_proposer'] if live else c['attribution']['rehearsal_witness_proposer']
    verdict = None; error = None; receipt = None; accounting = None; request = None
    lifecycle = {'permit': None, 'reservation': None, 'reconciliation': None, 'reconcile_error': None, 'attempt_id': None,
                 'reservation_state': 'not_reserved', 'evidence_write_failures': []}
    try:
        try: request = prepare(run, task, tools)
        except site_request.Refusal as refusal:  # policy C will not pose this problem: recorded, never reserved
            events.append(run, 'request-admission', 'request_refused', {'code': refusal.code, 'detail': str(refusal)[:500]})
            raise wire.Failure('policy_refused', 'request_admission', 'Policy C: '+refusal.code)
        except episode.StageFailure as caught:
            stderr = run/'stages'/caught.stage/(caught.stage+'.stderr')
            if caught.stage == 'pipeline-prepare' and stderr.exists() and stderr.read_text().startswith('Failure('):  # the SDK's own refusal
                events.append(run, 'request-admission', 'interface_refused', {'stage': caught.stage, 'stderr_sha256': r6.sha(stderr)})
                raise wire.Failure('interface_refused', 'preparation', 'SDK refused to prepare: '+stderr.read_text()[:200])
            raise
        events.append(run, 'proposal', 'recovery_started', {'route': contract.NAME, 'proposer': proposer})
        response, error, receipt, accounting = invoke(run, tools, mode, nonce, credential_file, lifecycle, task.id, draw)
        if error is None:
            try:
                packet, report, reports, delta, solution_hash, receipt_ = consume(run, task, tools, response, proposer, contract.NAME)
                verdict = {'schema_version': 'r6-cohort-proof-1', 'task_id': task.id, 'search_policy': contract.NAME,
                    'mode': mode, 'manifest_sha256': r6.sha(task.path/'manifest.json'),
                    'challenge_sha256': tools['expected']['challenge_sha256'], 'request_sha256': gate.sha(request),
                    'solution_sha256': solution_hash, 'final_validation': reports, 'axiom_delta': delta,
                    'certificate_validation': report, 'witness_proposer': proposer,
                    'certificate_assembler': 'sdk_proposal_assembler_v1', 'consumer_route': consumer.contract.NAME,
                    'certificate_verified': True, 'closer': receipt_['closer'], 'certificate_consumed': receipt_['certificate_consumed'],
                    'derivation_replayed': receipt_['derivation_replayed'], 'residual_closer': receipt_['residual_closer'],
                    'proof_replayed': True, 'trust_tier': 1, 'local_obligation_closed': True,
                    'whole_declaration_validated': True}
                r6.write_json(run/'verdict.json', verdict)
                events.append(run, 'episode', 'proof_validated', {'verdict_sha256': r6.sha(run/'verdict.json'),
                    'proof_accepted': True, 'solution_sha256': solution_hash})
            except provider_payload.Failure as caught:
                error = failure(caught.category, 'certificate_verification', str(caught))
    except episode.StageFailure as caught:
        error = failure(caught.category, 'stage', f'{caught.stage}: {caught}')
        events.append(run, caught.stage, 'stage_failure_recorded', {'category': caught.category, 'stage': caught.stage})
    except (wire.Failure, provider_payload.Failure) as caught:
        error = caught if isinstance(caught, wire.Failure) else failure(caught.category, 'proposal', str(caught))
    except Exception as caught:  # last resort: the episode contract is a sealed record on every path
        error = failure('harness_failure', 'harness', type(caught).__name__+': '+str(caught)[:500])
        events.append(run, 'episode', 'harness_failure_recorded', {'error': type(caught).__name__})
    if receipt is None:
        receipt = live_receipt(run, None) if live else publication_driver.receipt(run, {'requests': []}, credential.derive(nonce), mode)
    if accounting is None:  # the lifecycle record, never a constant: a reservation made before the failure is reported as such
        out = run/'stages/proposal-1/output'
        try:
            accounting = accounting_for(run, c, live, read_record(out/'http.json', 'http')[0], read_record(out/'server.json', 'server')[0], lifecycle)
        except Exception as caught:  # accounting must not throw while an earlier failure is being recorded
            accounting = {'accounting_error': type(caught).__name__, 'attempts_reserved': 1 if lifecycle.get('permit') else None,
                          'reservation_state': lifecycle.get('reservation_state'), 'ledger_outcome': (lifecycle.get('reconciliation') or {}).get('kind'),
                          'ledger_reconciled': lifecycle.get('reconciliation') is not None, 'allowance_consumed': None,
                          'reconciliation_evidence_complete': False, 'evidence_complete': False, 'scope': 'accounting failed; lifecycle facts only'}
        r6.write_json(run/'accounting.json', accounting)
    reconciled = accounting['ledger_reconciled']
    use_ok = receipt.get('credential_use_accepted') if live else receipt.get('exact_receipt')
    summary = {'schema_version': 'r6-cohort-summary-1', 'task_id': task.id, 'draw': draw, 'campaign_id': c['campaign']['id'],
               'revision': c['revision'], 'contract_sha256': contract.contract_sha256(), 'mode': mode,
               'search_policy': contract.NAME, 'proof_accepted': verdict is not None, 'credential_use_accepted': bool(use_ok),
               'ledger_reconciled': reconciled, 'reservation_state': accounting.get('reservation_state'),
               'reconciliation_evidence_complete': accounting.get('reconciliation_evidence_complete'),
               'evidence_complete': accounting.get('evidence_complete'), 'failure_category': error.category if error else None,
               'failure_phase': error.phase if error else None, 'error': str(error) if error else None,
               'accounting': accounting, 'scope': c['scope']}
    r6.write_json(run/'credential-summary.json', summary)
    accepted, scan, final = finalize(run, credential.derive(nonce), nonce, summary, live)
    return {'accepted': accepted, 'mode': mode, 'proof_accepted': verdict is not None,
            'failure_category': summary['failure_category'], 'credential_use_accepted': bool(use_ok),
            'publication_accepted': None if live else bool(scan['accepted'] and final['report_clean']),
            'publication_pending': live, 'ledger_reconciled': reconciled, 'evidence_complete': accounting.get('evidence_complete'),
            'accounting': accounting}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=MODES, required=True)
    parser.add_argument('--task', choices=site_task.primary(), required=True)
    parser.add_argument('--draw', type=int, required=True)
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--credential-file', type=Path)
    args = parser.parse_args()
    run = args.run_dir.resolve(); run.mkdir(parents=True, exist_ok=False)
    result = execute(run, site_task.get(args.task), args.draw, args.mode, r6.ROOT.parents[1]/'lean-bridge/.lake/packages',
                     None if args.credential_file is None else args.credential_file.resolve())
    print(json.dumps(result, indent=1, default=str))


if __name__ == '__main__':
    main()

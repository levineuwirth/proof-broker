#!/usr/bin/env python3
"""R6-008 driver: the pilot's episode with every stage failure finalized.

`--mode rehearsal` runs the complete episode against a canned TLS receiver on
loopback with a synthetic canary, fully isolated, through the same grant path
the live stage uses. `--mode live` shares the network namespace for the one
proposal stage, trusts the pinned public bundle, mounts the operator's
credential file and consumes one transmission from the campaign ledger. Both
modes reserve from the same ledger for the same policy. Whatever fails, the
run is scanned, terminated with an event and sealed.
"""
import argparse
import json
from pathlib import Path
import shutil
import tempfile
import time

import admission
import campaign_budget as budget
import campaign_contract as contract
import campaign_ledger as ledger
import campaign_network as network
import credential
import credential_episode as publication_driver
import episode
import events
import live_tls_fixture
import priced_payload_v2 as wire
import provider_episode as consumer
import provider_payload
import pricing_gate_v2 as gate
import publication
import run as r6

MODES = ('rehearsal', 'live')
TERMINAL_KEYS = ('accepted', 'proof_accepted', 'credential_use_accepted', 'publication_accepted', 'publication_pending',
                 'ledger_reconciled', 'evidence_complete', 'summary_sha256', 'publication_scan_sha256', 'publication_final_sha256')


def setup(run, task, packages):
    contract.verify_sources()
    runtime_path, runtime = contract.materialize_runtime()
    tools = consumer.downstream.setup(run, task, packages)
    tools.update(python=Path(runtime['python']), runtime=runtime, runtime_path=runtime_path)
    binaries = r6.read_json(run/'provenance/binaries.json')
    binaries[runtime['python']] = runtime['python_sha256']
    r6.write_json(run/'provenance/binaries.json', binaries)
    r6.write_json(run/'provenance/python-runtime.json', runtime)
    r6.write_json(run/'provenance/roles.json', {'python': runtime['python'], 'runtime_path': str(runtime_path),
        'actor_source': str(r6.ROOT/'campaign_https.py'), 'network_stage': str(r6.ROOT/'campaign_network.py'),
        'ledger_module': str(r6.ROOT/'campaign_ledger.py'), 'ledger_directory': str(contract.LEDGERS),
        'assembler': str(tools['driver']), 'verifier': str(tools['verifier']), 'checker': str(tools['checker']),
        'runtime_pin': 'campaign-runtime-v1', 'downstream_setup': 'frozen proposal_episode.setup'})
    chain = [('campaign-harness', contract, [contract.RUNTIME])]
    module = contract.previous
    while module is not None:
        name = module.__name__.replace('_contract', '').replace('_', '-')
        extra = [module.RUNTIME] if getattr(module, 'RUNTIME', None) and Path(module.RUNTIME).exists() else []
        chain.append((name+'-harness', module, extra))
        module = getattr(module, 'previous', None)
    for section, module, extra in chain:
        for source in [r6.ROOT/name for name in module.FILES]+[module.CONFIG, module.LOCK]+extra:
            target = run/'provenance'/section/source.relative_to(r6.ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
    return tools


def prepare(run, task, tools):
    prepared = consumer.prepare(run, task, tools)
    request = budget.request(task, prepared)
    (run/'live-request.json').write_bytes(request)
    args = budget.arguments(request)
    r6.write_json(run/'live-arguments.json', args)
    r6.write_json(run/'live-messages.json', args['input'])
    record = {'request_sha256': gate.sha(request), 'policy_sha256': contract.policy_sha256(),
              'prompt_sha256': r6.sha(contract.PROMPT), 'arguments_sha256': r6.sha(run/'live-arguments.json'),
              'messages_sha256': r6.sha(run/'live-messages.json'), 'prepared_sha256': r6.sha(run/'prepared.json'),
              'preparation_request_sha256': r6.sha(run/'request.json'),
              'inner_binding': 'request policy_sha256 is this campaign policy; the preparation component request is retained separately'}
    r6.write_json(run/'live-payload.json', record)
    events.append(run, 'live-payload', 'payload_validated', record)
    return request


def canned(task, request):
    fixture = consumer.canned_provider(task, request, 'valid')
    obj = json.loads(fixture['body'])
    obj['model'] = contract.MODEL
    obj['service_tier'] = 'default'
    fixture['body'] = (events.canonical(obj)+b'\n').decode()
    return fixture


def failure(category, phase, message):
    return wire.Failure(category, phase, message)


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
    stage = run/'stages/proposal-1'; book = contract.campaign_ledger(live); slot = book.slot(permit['reservation_id'])
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
              'stage': 'pricing_admission' if pricing else 'campaign_ledger'}
    r6.write_json(run/'host-pricing-admission.json', denied)
    events.append(run, 'pricing-admission' if pricing else 'campaign-ledger', 'pricing_rejected' if pricing else 'reservation_refused', denied)
    receipt = publication_driver.receipt(run, {'requests': []}, credential.derive(nonce), 'rehearsal') if not live else live_receipt(run, None)
    accounting = accounting_for(run, c, live, None, None, lifecycle)
    r6.write_json(run/'accounting.json', accounting)
    category = 'pricing_admission' if pricing else ('reservation_state_unknown' if state == 'unknown' else 'campaign_ledger')
    return None, failure(category, 'pricing_admission' if pricing else 'campaign_ledger',
                         ('Pricing admission: ' if pricing else 'Campaign ledger: ')+code), receipt, accounting


def invoke(run, tools, mode, nonce, credential_file, lifecycle):
    c = contract.config(); runtime = tools['runtime']; limits = c['limits']
    live = mode == 'live'
    request = (run/'live-request.json').read_bytes()
    shutil.copytree(contract.SOURCES, run/'pricing-sources')
    lifecycle['attempt_id'] = credential.nonce()  # transaction identity, chosen before any ledger effect
    events.append(run, 'campaign-ledger', 'reservation_attempted', {'attempt_id': lifecycle['attempt_id']})
    try:
        row, raw, admitted = budget.reserve(run.name, r6.read_json(run/'live-arguments.json'), request, run/'pricing-sources', live,
                                            lifecycle['attempt_id'])
    except (gate.Failure, ledger.Failure) as refused:
        if not isinstance(refused, gate.Failure) and refused.code not in ('campaign_ledger_not_activated', 'campaign_reservation_open',
                'campaign_transmissions_exhausted', 'campaign_presend_attempts_exhausted', 'campaign_money_exhausted', 'campaign_missing_episode_identity'):
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
        book = contract.campaign_ledger(live); slot = book.slot(row['reservation_id'])
        common = [(tools['runtime_path'], runtime['stdlib']), (r6.ROOT/'campaign_https.py', '/adapter.py'),
                  (r6.ROOT/'live_https.py', '/live_https.py'), (r6.ROOT/'pricing_gate_v2.py', '/pricing_gate_v2.py'),
                  (r6.ROOT/'campaign_ledger.py', '/campaign_ledger.py'),
                  (run/'transport-policy.json', '/policy.json'), (run/'transport-arguments.json', '/arguments.json'),
                  (run/'transport-request.json', '/request.json'), (run/'transport-pricing-sources', '/pricing-sources'),
                  (run/'campaign-permit.json', '/permit.json'), (book.path, '/ledger.ndjson')]  # the authoritative file, read-only
        argv = ['-I', '-S', '-B', '/adapter.py', '--mode', mode, '--policy', '/policy.json', '--arguments', '/arguments.json',
                '--credential-file', '/credential', '--ca', '/ca.pem', '--out', '/out', '--request', '/request.json',
                '--sources', '/pricing-sources', '--permit', '/permit.json', '--ledger', '/ledger.ndjson', '--episode', run.name,
                '--grant', '/grant', '--commitment-nonce', commitment_nonce]
        budgets = dict(extra_binaries=[Path(p) for p in runtime['extension_binaries']], wall=limits['request_wall_seconds'],
                       cpu=limits['request_cpu_seconds'], memory=limits['request_memory_bytes'],
                       output_limit=limits['request_output_bytes'])
        if live:
            ca_path, described = contract.bundle()
            if described['sha256'] != c['tls']['public_ca_bundle']['sha256']: raise ValueError('campaign_ca_bundle_binding')
            events.append(run, 'proposal', 'live_transport_authorized', {
                'approved_by': c['authorization']['approved_by'], 'approved_utc': c['authorization']['approved_utc'],
                'ca_bundle_sha256': described['sha256'], 'network_namespace': 'shared_with_host',
                'reservation_id': row['reservation_id'], 'commitment_nonce': commitment_nonce,
                'credential_source': 'operator file; value never copied'})
            network.stage(run, 'proposal-1', tools['python'], argv,
                          [*common, (Path(credential_file), '/credential'), (ca_path, '/ca.pem')], slot, shared_network=True, **budgets)
        else:
            r6.write_json(run/'canned-provider.json', canned(r6.get_task(r6.read_json(run/'search-policy.json')['task_id']), request))
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
        return None, failure('reconciliation_failure', 'campaign_ledger', 'Reservation left open: '+lifecycle['reconcile_error']), receipt, accounting
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
    assembled = episode.stage(run, 'assembly', tools['driver'],
        ['assemble', '/prepared.json', '/response.json', 'sha256:'+r6.sha(consumer.contract.CONFIG), '/out/evidence.json'],
        [(run/'prepared.json', '/prepared.json'), (run/'validated-response.json', '/response.json')])
    shutil.copyfile(assembled/'evidence.json', run/'evidence.json')
    packet = r6.read_json(run/'evidence.json')
    events.append(run, 'assembly', 'certificate_assembled', {'certificate_sha256': events.digest(packet['certificate']),
        'witness_proposer': proposer, 'certificate_assembler': 'sdk_proposal_assembler_v1',
        'consumer_route': consumer.contract.NAME, 'response_sha256': r6.sha(run/'validated-response.json')})
    try:
        verified = episode.stage(run, 'certificate-check', tools['verifier'], ['/evidence.json', '/out/verdict.json'],
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
    inputs = consumer.downstream.compile_input(run, 'input', 'ProposalCapture', consumer.overlay.capture_source(task), task)
    compiler = tools['compiler']
    mounts = [*tools['mounts'], (inputs, '/input')]
    built = episode.stage(run, 'capture-build', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', '/out/ProposalCapture.olean', '/input/ProposalCapture.lean'],
        mounts, compiler=compiler, env={'LEAN_PATH': tools['lean_path']+':/out'}, extra_binaries=tools['extras'])
    reconstructed = episode.stage(run, 'reconstruct', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
        [*mounts, (built, '/capture'), (run/'evidence.json', '/evidence.json')], compiler=compiler,
        extra_binaries=tools['extras'], capture_events=True,
        env={'LEAN_PATH': tools['lean_path']+':/capture', 'R6_PROPOSAL_PACKET': '/evidence.json',
             'PROOF_BROKER_EPISODE_TRACE': '1', 'R6_CAPTURE_OUTPUT': '/out/context.json'})
    consumer.require(r6.read_json(reconstructed/'context.json') == r6.read_json(task.path/'context/local-context.json'),
                     'reconstruction changed frozen context')
    events.append(run, 'reconstruct', 'context_validated', {'captured_context_sha256': r6.sha(reconstructed/'context.json'),
        'frozen_context_sha256': r6.sha(task.path/'context/local-context.json')})
    exported = episode.stage(run, 'export', tools['exporter'], ['Frozen', '--', task.whole, task.local, *r6.EXPORT_TARGETS],
        [*tools['mounts'], (reconstructed, '/objects'), (built, '/capture')], compiler=compiler,
        extra_binaries=tools['extras'], env={'LEAN_PATH': tools['lean_path']+':/capture:/objects'})
    solution = exported.parent/'export.stdout'
    r6.pack(solution, run/'solution.ndjson.gz')
    with tempfile.TemporaryDirectory(prefix='r6-campaign-challenge-') as temp:
        challenge = Path(temp)/'challenge.ndjson'
        r6.unpack(task.path/'challenge.ndjson.gz', challenge)
        consumer.require(r6.sha(challenge) == tools['expected']['challenge_sha256'], 'challenge changed')
        reports, delta = episode.final_validation(run, challenge, solution, tools['checker'], tools['expected'], task)
    return packet, report, reports, delta, r6.sha(solution)


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
    publication_driver.seal(run, accepted)
    return accepted, report, final


def execute(run, task, mode, packages, credential_file):
    if mode not in MODES: raise ValueError('Unknown mode')
    if task.id not in admission.verify()['controls']: raise ValueError('Task outside frozen controls')
    tools = setup(run, task, packages)
    c = contract.config(); nonce = credential.nonce(); live = mode == 'live'
    if live:
        contract.live_permitted(c)
        if credential_file is None: raise ValueError('live mode requires --credential-file')
    shutil.copytree(contract.SOURCES, run/'pricing-origin')
    r6.write_json(run/'credential-canary.json', credential.record(nonce))
    policy = {'name': contract.NAME, 'mode': mode, 'task_id': task.id, 'config_sha256': contract.policy_sha256(),
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
        request = prepare(run, task, tools)
        events.append(run, 'proposal', 'recovery_started', {'route': contract.NAME, 'proposer': proposer})
        response, error, receipt, accounting = invoke(run, tools, mode, nonce, credential_file, lifecycle)
        if error is None:
            try:
                packet, report, reports, delta, solution_hash = consume(run, task, tools, response, proposer, contract.NAME)
                verdict = {'schema_version': 'r6-campaign-proof-1', 'task_id': task.id, 'search_policy': contract.NAME,
                    'mode': mode, 'manifest_sha256': r6.sha(task.path/'manifest.json'),
                    'challenge_sha256': tools['expected']['challenge_sha256'], 'request_sha256': gate.sha(request),
                    'solution_sha256': solution_hash, 'final_validation': reports, 'axiom_delta': delta,
                    'certificate_validation': report, 'witness_proposer': proposer,
                    'certificate_assembler': 'sdk_proposal_assembler_v1', 'consumer_route': consumer.contract.NAME,
                    'certificate_verified': True, 'certificate_consumed': True, 'derivation_replayed': False,
                    'residual_closer': 'omega', 'proof_replayed': True, 'trust_tier': 1, 'local_obligation_closed': True,
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
    summary = {'schema_version': 'r6-campaign-summary-2', 'task_id': task.id, 'mode': mode,
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
    parser.add_argument('--task', choices=('verinf-d1-70',), default='verinf-d1-70')
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--credential-file', type=Path)
    args = parser.parse_args()
    run = args.run_dir.resolve(); run.mkdir(parents=True, exist_ok=False)
    result = execute(run, r6.get_task(args.task), args.mode, r6.ROOT.parents[1]/'lean-bridge/.lake/packages',
                     None if args.credential_file is None else args.credential_file.resolve())
    print(json.dumps(result, indent=1, default=str))


if __name__ == '__main__':
    main()

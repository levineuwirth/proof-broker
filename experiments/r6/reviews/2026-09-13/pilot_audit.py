#!/usr/bin/env python3
"""R6-007 historical auditor over the six pilot runs. Non-locked; read-only.

Every relationship is reconstructed from bytes retained inside the run tree:
each run binds its own policy, lock and sources from `provenance/`; requests
and admissions are regenerated from the retained policy; proofs go through the
shared R6-002 checker plus task, context and witness equality; transport and
accounting are recomputed from the actor's records. The audited tree may be a
copy: nothing is compared against a fixed original location except the frozen
task directory (bound by manifest digest) and the frozen modules imported here
(bound to the copies the live run retained).

Named cases are asserted as a fixed population, not counted. No provider
request, credential read, Lean build or verifier execution happens here.
"""
import argparse
import copy
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import credential
import envelope_proof_audit
import episode
import events
import payload
import pilot_budget as budget
import pilot_contract as contract
import priced_payload_v2 as v2
import pricing_gate_v2 as gate
import provider_payload
import run as r6

RUNS = ('rehearsal-1', 'rehearsal-2', 'rehearsal-3', 'rehearsal-4', 'live-1', 'live-2')
PILOT_FILES = ('pilot_contract.py', 'pilot_https.py', 'pilot_network.py', 'pilot_budget.py', 'pilot_episode.py', 'test_pilot.py')
TASK = 'verinf-d1-70'
SIGNED_POLICY = '833035eb0d34b103aed7aad5f32cb519963b48d34040d2afb14e0739e36fa0ea'
LIVE_LOCK = 'bf5d637bc5639fcc7619d5819c1d4f4c01ecda641e822f18a3df8151c151e0d9'
CANNED_D1_EXPORT = 'cd6081daac2fc64d718d28202d1742ff1e653e9862031fb19a5efeb7cd7d1812'   # R6-003 canned path
LIVE_EXPORT = '862f16b9d9efc5de246fc8aa8aa2278bfff5590fbc70dd6b8d42ab993ab25c27'
MODULES = {'credential': ('credential-harness', credential), 'envelope_proof_audit': ('envelope-harness', envelope_proof_audit),
           'episode': ('harness', episode), 'events': ('harness', events), 'payload': ('harness', payload),
           'pilot_budget': ('pilot-harness', budget), 'pilot_contract': ('pilot-harness', contract),
           'priced_payload_v2': ('priced-v2-harness', v2), 'pricing_gate_v2': ('priced-v2-harness', gate),
           'provider_payload': ('provider-harness', provider_payload), 'run': ('harness', r6)}

PREFIX = [('supervisor', 'episode', 'episode_started')] + [(s, st, e) for st in ('preparation-build', 'preparation', 'pipeline-prepare')
          for s, e in (('supervisor', 'stage_started'), ('supervisor', 'stage_finished'))] + [
          ('supervisor', 'payload', 'payload_validated'), ('supervisor', 'live-payload', 'payload_validated'),
          ('supervisor', 'proposal', 'recovery_started')]
ADMITTED = [('supervisor', 'pricing-admission', 'pricing_admitted'), ('supervisor', 'proposal', 'request_reserved')]
OBSERVED = [('supervisor', 'proposal', 'https_observed'), ('supervisor', 'proposal', 'transport_validated'),
            ('supervisor', 'credential-receipt', 'credential_receipt_checked')]
CHILDREN = [('child_report', 'reconstruct', e) for e in ('reification_started', 'reification_finished', 'dispatch_started',
            'dispatch_received', 'certificate_verification_started', 'certificate_verification_finished',
            'reconstruction_started', 'residual_started', 'residual_finished', 'reconstruction_finished')]
PROOF = [('supervisor', 'assembly', 'stage_started'), ('supervisor', 'assembly', 'stage_finished'),
         ('supervisor', 'assembly', 'certificate_assembled'), ('supervisor', 'certificate-check', 'stage_started'),
         ('supervisor', 'certificate-check', 'stage_finished'), ('supervisor', 'certificate-check', 'independent_certificate_verdict'),
         ('supervisor', 'proposal', 'recovery_finished'), ('supervisor', 'capture-build', 'stage_started'),
         ('supervisor', 'capture-build', 'stage_finished'), ('supervisor', 'reconstruct', 'stage_started'), *CHILDREN,
         ('supervisor', 'reconstruct', 'stage_finished'), ('supervisor', 'reconstruct', 'context_validated'),
         ('supervisor', 'export', 'stage_started'), ('supervisor', 'export', 'stage_finished'),
         ('supervisor', 'validation-local', 'stage_started'), ('supervisor', 'validation-local', 'stage_finished'),
         ('supervisor', 'validation-local', 'kernel_verdict'), ('supervisor', 'validation-whole', 'stage_started'),
         ('supervisor', 'validation-whole', 'stage_finished'), ('supervisor', 'validation-whole', 'kernel_verdict'),
         ('supervisor', 'episode', 'proof_validated'), ('supervisor', 'episode', 'episode_finished')]
REHEARSAL_STAGE = [('supervisor', 'proposal-1', 'stage_started'), ('supervisor', 'proposal-1', 'stage_finished')]
# pilot_network.stage appends its own start/finish receipts beside the frozen supervisor's: one process, two receipts each.
LIVE_STAGE = [('supervisor', 'proposal', 'live_transport_authorized'), ('supervisor', 'proposal-1', 'stage_started'),
              ('supervisor', 'proposal-1', 'stage_started'), ('supervisor', 'proposal-1', 'stage_finished'),
              ('supervisor', 'proposal-1', 'stage_finished')]
REJECTED = [('supervisor', 'episode', 'episode_rejected')]
SEQUENCES = {
    'rehearsal-1': PREFIX+[('supervisor', 'pricing-admission', 'pricing_rejected'),
                           ('supervisor', 'credential-receipt', 'credential_receipt_checked')]+REJECTED,
    'rehearsal-2': PREFIX+ADMITTED+REHEARSAL_STAGE+OBSERVED+REJECTED,
    'rehearsal-3': PREFIX+ADMITTED+REHEARSAL_STAGE+OBSERVED+REJECTED,
    'rehearsal-4': PREFIX+ADMITTED+REHEARSAL_STAGE+OBSERVED+PROOF,
    'live-1': PREFIX+ADMITTED+LIVE_STAGE,
    'live-2': PREFIX+ADMITTED+LIVE_STAGE+OBSERVED+PROOF}
EXPECT = {'rehearsal-1': ('host', 'pricing_capture_stale'), 'rehearsal-2': ('actor', 'pricing_admission', 'pricing_reservation_binding'),
          'rehearsal-3': ('actor', 'tls_protocol_failure', None), 'rehearsal-4': ('proof', CANNED_D1_EXPORT),
          'live-1': ('unsealed', 'credential_format'), 'live-2': ('proof', LIVE_EXPORT)}
LIVE_ATTRIBUTION = {'recovery_started': ('live_model_response', 'responses_live_pilot_v1'),
                    'recovery_finished': ('canned_provider_response', 'openai_responses_http_fixture_v1'),
                    'certificate_assembled': ('canned_provider_response', None)}


class Rejection(AssertionError):
    def __init__(self, case, detail=''):
        super().__init__(case+(': '+detail if detail else '')); self.case = case


class Audit:
    def __init__(self):
        self.cases = {}

    def require(self, ok, case, detail=''):
        if case in self.cases: raise Rejection(case, 'duplicate case name')
        self.cases[case] = bool(ok)
        if not ok: raise Rejection(case, detail)


def sha(data): return hashlib.sha256(data).hexdigest()
def load(path): return json.loads(Path(path).read_bytes())
def canonical(value): return events.canonical(value)


def expected_cases():
    """The fixed population: every case name the audit must record."""
    names = ['population:exactly_six_runs', 'population:no_stray_entries', 'modules:bound_to_live_retained_copies',
             'task:manifest_bound', 'campaign:one_transmission_under_signed_authorization',
             'campaign:reservations_recorded', 'live-1:inventory_bound', 'operator_scan:consistent']
    for run in RUNS:
        kind = EXPECT[run][0]
        names += [f'{run}:versions:policy_lock_sources_bound', f'{run}:versions:runtime_bound',
                  f'{run}:chain:valid', f'{run}:chain:expected_sequence', f'{run}:request:regenerated',
                  f'{run}:request:arguments_regenerated', f'{run}:pricing:host_admission_rederived']
        if kind == 'unsealed':
            names += [f'{run}:unsealed:no_terminal_event', f'{run}:unsealed:no_connection',
                      f'{run}:unsealed:stderr_names_credential_format', f'{run}:ledger:consistent',
                      f'{run}:pricing:actor_admission_rederived', f'{run}:live:duplicate_receipts_audited']
            continue
        names += [f'{run}:seal:retained_hashes', f'{run}:seal:chain_bound', f'{run}:seal:outcome_recorded',
                  f'{run}:credential_receipt:recorded']
        if kind == 'host': continue
        names += [f'{run}:ledger:consistent', f'{run}:pricing:actor_admission_rederived', f'{run}:transport:record_consistent',
                  f'{run}:transport:local_send_equals_serialized', f'{run}:transport:endpoint_and_ca_bound',
                  f'{run}:interpretation:reproduced', f'{run}:accounting:recomputed']
        if run.startswith('live'): names += [f'{run}:live:tls_verified_before_send', f'{run}:live:duplicate_receipts_audited']
        if kind == 'actor':
            names += [f'{run}:transport:failure_recorded']
        else:
            names += [f'{run}:transport:remote_receipt', f'{run}:proof:response_bound', f'{run}:proof:witness_contradiction',
                      f'{run}:proof:certificate_bound', f'{run}:proof:attribution_audited', f'{run}:proof:shared_checker',
                      f'{run}:proof:export_expected', f'{run}:provider:reported_fields']
    return tuple(names)


CASES = expected_cases()


def provenance(run):
    sp = load(run/'search-policy.json')
    ph = run/'provenance/pilot-harness'
    policy_path = ph/'policies/responses-live-pilot-v1.json'
    lock_path = ph/'policies/pilot-harness-v1.sha256.json'
    return sp, policy_path, lock_path, load(policy_path), load(lock_path)


def versions(a, run, name):
    sp, policy_path, lock_path, policy, lock = provenance(run)
    sources = {f: sha((run/'provenance/pilot-harness'/f).read_bytes()) for f in PILOT_FILES}
    transport_copy = (not (run/'transport-policy.json').exists()) or load(run/'transport-policy.json') == policy
    a.require(sp['config_sha256'] == sha(policy_path.read_bytes()) and sp['source_lock_sha256'] == sha(lock_path.read_bytes())
              and sorted(lock) == sorted(PILOT_FILES) and all(lock[f] == sources[f] for f in PILOT_FILES)
              and sp['task_id'] == TASK and sp['name'] == 'responses_live_pilot_v1'
              and (name.startswith('live')) == (sp['config_sha256'] == SIGNED_POLICY and policy['live_enabled'] is True)
              and (sp['source_lock_sha256'] == LIVE_LOCK) == (name in ('rehearsal-4', 'live-1', 'live-2'))
              and policy_path.read_bytes() == canonical(policy)+b'\n' and transport_copy,
              f'{name}:versions:policy_lock_sources_bound')
    runtime = load(run/'runtime.json') if (run/'runtime.json').exists() else None
    pinned = load(run/'provenance/pilot-harness/policies/pilot-runtime-v1.json')
    a.require(policy['runtime_lock_sha256'] == sha(canonical(pinned)+b'\n') or policy['runtime_lock_sha256'] == sha((run/'provenance/pilot-harness/policies/pilot-runtime-v1.json').read_bytes()),
              f'{name}:versions:runtime_bound', 'policy runtime lock is not the retained runtime record')
    return sp, policy


def chain(a, run, name):
    try: rows = events.read(run/'events.ndjson')
    except ValueError as error: a.require(False, f'{name}:chain:valid', str(error))
    a.require(all(r['task_id'] == TASK and r['run_id'] == rows[0]['run_id'] for r in rows), f'{name}:chain:valid')
    observed = [(r['source'], r['stage'], r['event']) for r in rows]
    a.require(observed == SEQUENCES[name], f'{name}:chain:expected_sequence',
              f'{len(observed)} events; first divergence at '+str(next((i for i, (x, y) in enumerate(zip(observed, SEQUENCES[name])) if x != y), min(len(observed), len(SEQUENCES[name])))))
    return rows


def duplicate_receipts(a, run, rows, name):
    """Two receipts per boundary for one process: pilot_network's beside the supervisor's. Both must equal the process record."""
    started = [r['payload'] for r in rows if r['stage'] == 'proposal-1' and r['event'] == 'stage_started']
    finished = [r['payload'] for r in rows if r['stage'] == 'proposal-1' and r['event'] == 'stage_finished']
    process = load(run/'stages/proposal-1/proposal-1.process.json')
    a.require(len(started) == 2 and len(finished) == 2 and finished[0] == finished[1] == process
              and started[0]['command_file'] == started[1]['command_file'] == 'stages/proposal-1/command.json'
              and started[0].get('network_namespace') == 'shared_with_host',
              f'{name}:live:duplicate_receipts_audited', 'proposal-1 receipts are not one agreeing pair per boundary bound to the process record')


def seal(a, run, name, rows, kind):
    s = load(run/'seal.json')
    mismatched = [k for k, v in s['retained_sha256'].items() if not (run/k).is_file() or sha((run/k).read_bytes()) != v]
    a.require(not mismatched and len(s['retained_sha256']) > 0, f'{name}:seal:retained_hashes', f'{len(mismatched)} retained entries differ')
    a.require(s['event_count'] == len(rows) and s['last_event_hash'] == rows[-1]['event_hash'], f'{name}:seal:chain_bound')
    a.require(s['accepted'] is (kind == 'proof') and rows[-1]['event'] == ('episode_finished' if kind == 'proof' else 'episode_rejected'),
              f'{name}:seal:outcome_recorded')
    return s


def request(a, run, name, sp, policy, task):
    prepared = load(run/'prepared.json')
    try:
        value = payload.strict_json(v2.request(task, prepared))
    except Exception as error:  # the frozen builder refused the retained preparation
        a.require(False, f'{name}:request:regenerated', type(error).__name__+': '+str(error))
    value['schema_version'] = 'r6-farkas-request-7'; value['policy_sha256'] = sp['config_sha256']
    regenerated = canonical(value)+b'\n'
    retained = (run/'live-request.json').read_bytes()
    a.require(regenerated == retained and (run/'request.sha256').read_text().split() == [sha((run/'request.json').read_bytes()), 'request.json'],
              f'{name}:request:regenerated')
    prompt = (run/'prompt.txt').read_text()
    opts = copy.deepcopy(policy['request'])
    opts['input'] = [{'role': 'system', 'content': prompt},
                     {'role': 'user', 'content': v2.previous.PREFIX+sha(retained)+v2.previous.SEPARATOR+retained.decode()}]
    a.require(sha(prompt.encode()) == policy['prompt_sha256'] == value['binding']['prompt_sha256'] and load(run/'live-arguments.json') == opts,
              f'{name}:request:arguments_regenerated')
    return retained, opts


def host_admission(a, run, name, policy, request_bytes, arguments, kind):
    record = load(run/'host-pricing-admission.json')
    try:
        derived = gate.admission(policy, run/'pricing-sources', arguments, request_bytes, record['evaluated_at_unix'])
        derived_code = None
    except gate.Failure as failure:
        derived, derived_code = None, failure.code
    if kind == 'host':
        a.require(record['accepted'] is False and derived is None and derived_code == record['failure_code'] == EXPECT[name][1],
                  f'{name}:pricing:host_admission_rederived', f'derived {derived_code}, recorded {record.get("failure_code")}')
    else:
        a.require(record['accepted'] is True and derived == record, f'{name}:pricing:host_admission_rederived')


def ledger(a, run, name, sp, request_bytes, policy):
    rows = [json.loads(l) for l in (run/'reservation-ledger.ndjson').read_bytes().splitlines()]
    permit = load(run/'pricing-permit.json'); reservation = load(run/'reservation.json')
    bindings = {'request_sha256': sha(request_bytes), 'arguments_sha256': sha((run/'live-arguments.json').read_bytes()),
                'policy_sha256': sp['config_sha256'], 'pricing_admission_sha256': sha((run/'host-pricing-admission.json').read_bytes())}
    a.require(len(rows) == 1 and rows[0] == permit and permit['episode_id'] == name and permit['sequence'] == 0
              and permit['request_sha256'] == bindings['request_sha256'] and permit['policy_sha256'] == sp['config_sha256']
              and reservation == {**permit['reservation'], **bindings}
              and reservation['reserved_micro_usd'] <= policy['limits']['total_micro_usd']
              and permit['reservation'].get('attempt', 1) == 1 and permit['pricing_admission'] == load(run/'host-pricing-admission.json')
              and (run/'transport-ledger.ndjson').read_bytes() == (run/'reservation-ledger.ndjson').read_bytes() == canonical(permit)+b'\n',
              f'{name}:ledger:consistent')
    return reservation


def actor_admission(a, run, name, kind):
    out = run/'stages/proposal-1/output'; record = load(out/'pricing-check.json')
    if kind == 'actor' and EXPECT[name][1] == 'pricing_admission':
        try:
            gate.transport_admission(load(run/'transport-policy.json'), run/'transport-pricing-sources', load(run/'transport-arguments.json'),
                                     (run/'transport-request.json').read_bytes(), load(run/'pricing-permit.json'),
                                     (run/'transport-ledger.ndjson').read_bytes(), name, record['evaluated_at_unix'])
        except gate.Failure as failure: code = failure.code
        else: code = None
        a.require(record['accepted'] is False and record['failure_code'] == code == EXPECT[name][2], f'{name}:pricing:actor_admission_rederived')
        return record
    derived = gate.transport_admission(load(run/'transport-policy.json'), run/'transport-pricing-sources', load(run/'transport-arguments.json'),
                                       (run/'transport-request.json').read_bytes(), load(run/'pricing-permit.json'),
                                       (run/'transport-ledger.ndjson').read_bytes(), name, record['evaluated_at_unix'])
    a.require(derived == {k: v for k, v in record.items() if k not in ('admitted_at_ns', 'evaluated_at_unix')}
              and derived['current']['body_sha256'] == sha((out/'serialized-body.json').read_bytes()),
              f'{name}:pricing:actor_admission_rederived')
    return record


def transport(a, run, name, policy, request_bytes, kind, live):
    out = run/'stages/proposal-1/output'; http = load(out/'http.json'); server = load(out/'server.json')
    body = (out/'serialized-body.json').read_bytes()
    a.require(http['mode'] == ('live' if live else 'rehearsal') and http['request_sha256'] == sha(body) and http['request_bytes'] == len(body)
              and http['retries'] == 0 and http['redirects_followed'] == 0
              and http['transport_scope'] == ('provider_request' if live else 'isolated_loopback_https_fixture')
              and http['maximum_response_bytes'] == policy['limits']['maximum_response_bytes']
              and (http['fixture_tcp_port'] is None) == (live or http['failure_category'] in ('pricing_admission', 'authorization'))
              and http['authorization_present_in_policy'] is (True if live else None),
              f'{name}:transport:record_consistent')
    sent = (out/'outbound-body.json').read_bytes() if (out/'outbound-body.json').exists() else None
    if http['body_sends_started']:
        a.require(sent == body and http['outbound_body_sha256'] == sha(body), f'{name}:transport:local_send_equals_serialized',
                  'the locally captured outbound bytes differ from the admitted serialized body')
    else:
        a.require(sent is None and http['outbound_body_sha256'] is None, f'{name}:transport:local_send_equals_serialized', 'no send, yet a capture exists')
    a.require(http['endpoint'] == policy['endpoint'] and http['ca_bundle_sha256'] == (policy['tls']['public_ca_bundle']['sha256'] if live else http['ca_bundle_sha256'])
              and (not live or http['ca_bundle_sha256'] == policy['tls']['public_ca_bundle']['sha256']),
              f'{name}:transport:endpoint_and_ca_bound')
    if kind == 'actor':
        a.require(http['failure_category'] == EXPECT[name][1] and http['http_status'] is None and http['body_sends_returned'] == 0,
                  f'{name}:transport:failure_recorded')
        return http, server
    if live:
        # Remote receipt is unobservable. What is recorded: HTTP 200 and a completed provider object. Not exact-credential receipt.
        a.require(http['http_status'] == 200 and http['body_sends_returned'] == 1 and http['response_bytes'] == len((out/'provider-response.json').read_bytes())
                  and http['response_sha256'] == sha((out/'provider-response.json').read_bytes()) and server['requests'] == [],
                  f'{name}:transport:remote_receipt', 'provider status/response binding')
        a.require(http['tls'] and http['tls']['verified'] is True and http['tls']['version'] in ('TLSv1.2', 'TLSv1.3')
                  and http['tls']['server_hostname'] == policy['endpoint']['host'] and http['tls_verified_at_ns'] is not None
                  and http['header_send_at_ns'] is not None and http['tls_verified_at_ns'] < http['header_send_at_ns']
                  and http['connection_started_at_ns'] <= http['tls_verified_at_ns'],
                  f'{name}:live:tls_verified_before_send')
    else:
        nonce = load(run/'credential-canary.json')['nonce']; header = credential.header(credential.derive(nonce))
        a.require(http['http_status'] == 200 and len(server['requests']) == 1 and server['requests'][0]['body_sha256'] == sha(body)
                  and server['requests'][0]['authorization_sha256'] == sha(header.encode())
                  and (out/'received-body.json').read_bytes() == body and server['server_names'] == [policy['endpoint']['host']],
                  f'{name}:transport:remote_receipt', 'fixture receiver did not record the exact canary and body')
    return http, server


def interpretation(a, run, name, request_bytes, live):
    out = run/'stages/proposal-1/output'
    proposed, text, metadata, validation, error = budget.interpret(out, request_bytes, live)
    retained_validation = load(run/'transport-validation.json'); retained_metadata = load(run/'provider-metadata.json')
    same_text = (text is None and not (run/'response.json').exists()) or (text is not None and (run/'response.json').read_bytes() == text)
    a.require(validation == retained_validation and metadata == retained_metadata and same_text, f'{name}:interpretation:reproduced')
    return proposed, error


def accounting(a, run, name, policy, http, server, reservation, live):
    acct = load(run/'accounting.json'); out = run/'stages/proposal-1/output'
    usage = provider_payload.usage({}); status = 'unreported'
    if (out/'provider-response.json').exists():
        usage = provider_payload.usage(load(out/'provider-response.json')); status = usage['status']
    rates = policy['pricing']['nano_usd_per_token']
    estimate = None if usage['input_tokens'] is None or usage['output_tokens'] is None else gate.cost_micro(usage['input_tokens'], usage['output_tokens'], rates)
    expected = {'attempts_reserved': 1, 'reservation': reservation, 'connection_attempts': http['connection_attempts'],
                'headers_started': http['header_sends_started'], 'bodies_started': http['body_sends_started'],
                'bodies_returned': http['body_sends_returned'], 'endpoint_receipts': len(server['requests']),
                'usage': usage, 'usage_status': status, 'priced_usage_ceiling_micro_usd': estimate,
                'live_model_calls': 1 if live and http['body_sends_returned'] else 0,
                'live_model_cost_usd': None if not live else (None if estimate is None else estimate/1e6), 'scope': acct['scope']}
    a.require(acct == expected and (estimate is None or estimate <= reservation['reserved_micro_usd']), f'{name}:accounting:recomputed')
    return {'transmissions_started': http['body_sends_started'], 'transmissions_returned': http['body_sends_returned'],
            'priced_usage_ceiling_micro_usd': estimate, 'usage_status': status}


def receipt_record(a, run, name, http, live):
    r = load(run/'credential-receipt.json')
    if live:
        a.require(r['channel'] == 'operator_credential_file' and r['http_status'] == http['http_status']
                  and r['exact_receipt'] is (http['http_status'] is not None and http['http_status'] != 401),
                  f'{name}:credential_receipt:recorded')
        return {'recorded_exact_receipt': r['exact_receipt'], 'audited_meaning': 'non-401 provider status; not exact-credential receipt'}
    a.require(r['channel'] == 'private_read_only_file', f'{name}:credential_receipt:recorded')
    return {'recorded_exact_receipt': r['exact_receipt'], 'audited_meaning': 'digest-matched canary receipt at the loopback fixture'}


def farkas(problem, witness):
    rows = {row['name']: row for row in problem['rows']}; terms, constant = {}, 0
    for entry in witness['coefficients']:
        row, m = rows[entry['hypothesis']], int(entry['coefficient'])
        if row['relation'] != 'eq' and m < 0: return None, None
        constant += m*int(row['constant'])
        for term in row['terms']: terms[term['variable']] = terms.get(term['variable'], 0)+m*int(term['coefficient'])
    return {v: c for v, c in terms.items() if c}, constant


def proof(a, run, name, rows, task, request_bytes, live):
    response = load(run/'response.json'); validated = load(run/'validated-response.json')
    out = run/'stages/proposal-1/output'
    raw = load(out/'provider-response.json')
    text = [c['text'] for item in raw['output'] if item.get('type') == 'message' for c in item['content'] if c.get('type') == 'output_text']
    a.require(response == validated and json.loads(''.join(text)) == response and response['request_sha256'] == sha(request_bytes),
              f'{name}:proof:response_bound')
    residual, constant = farkas(json.loads(request_bytes)['problem'], response['witness'])
    a.require(residual == {} and constant is not None and constant > 0, f'{name}:proof:witness_contradiction')
    evidence = load(run/'evidence.json'); cert = load(run/'certificate-verdict.json')
    assembled = next(r['payload'] for r in rows if r['event'] == 'certificate_assembled')
    verdict = load(run/'verdict.json')
    a.require(evidence['certificate']['payload']['witness_data'] == response['witness'] and cert['accepted'] is True
              and cert['reason']['kind'] == 'verified_farkas' and cert['certificate_hash'] == 'sha256:'+assembled['certificate_sha256']
              and assembled['response_sha256'] == sha((run/'validated-response.json').read_bytes())
              and cert == next(r['payload'] for r in rows if r['event'] == 'independent_certificate_verdict')
              and verdict['certificate_validation'] == cert and verdict['request_sha256'] == sha(request_bytes)
              and load(run/'stages/assembly/output/evidence.json') == evidence,
              f'{name}:proof:certificate_bound')
    # Literal attribution values, with the interpretation of the reused consumer recorded rather than hidden.
    named = {r['event']: (r['payload'].get('proposer', r['payload'].get('witness_proposer')), r['payload'].get('route')) for r in rows
             if r['event'] in ('recovery_started', 'recovery_finished', 'certificate_assembled')}
    expected = LIVE_ATTRIBUTION if live else {'recovery_started': ('canned_provider_response', 'responses_live_pilot_v1'),
                                              'recovery_finished': ('canned_provider_response', 'openai_responses_http_fixture_v1'),
                                              'certificate_assembled': ('canned_provider_response', None)}
    a.require(named == expected and verdict['witness_proposer'] == ('live_model_response' if live else 'canned_provider_response')
              and assembled['certificate_assembler'] == verdict['certificate_assembler'] == 'sdk_proposal_assembler_v1',
              f'{name}:proof:attribution_audited', f'observed {named}')
    def receipt(stage, event):
        hits = [r['payload'] for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event]
        if len(hits) != 1: raise ValueError(f'{stage}/{event}: {len(hits)} receipts')
        return hits[0]
    read = lambda n: load(run/n)
    try:
        if not (read('stages/reconstruct/output/context.json') == read('stages/preparation/output/context.json')
                == load(task.path/'context/local-context.json')): raise ValueError('reconstruction context differs from the frozen context')
        _, expected = r6.frozen_task(task); challenge = json.loads(request_bytes)['binding']['challenge_sha256']
        if (verdict['task_id'] != task.id or verdict['manifest_sha256'] != sha((task.path/'manifest.json').read_bytes())
                or not (verdict['challenge_sha256'] == expected['challenge_sha256'] == challenge)):
            raise ValueError('target identity differs (task, manifest or challenge)')
        envelope_proof_audit.audit(task, evidence, verdict, rows, lambda n: run/n, read, receipt)
    except (ValueError, AssertionError, KeyError, OSError, gzip.BadGzipFile, EOFError) as error:
        a.require(False, f'{name}:proof:shared_checker', str(error))
    a.require(True, f'{name}:proof:shared_checker')
    proved = next(r['payload'] for r in rows if r['event'] == 'proof_validated')
    a.require(proved['proof_accepted'] is True and proved['solution_sha256'] == verdict['solution_sha256'] == EXPECT[name][1]
              and proved['verdict_sha256'] == sha((run/'verdict.json').read_bytes()) and verdict['local_obligation_closed'] is True,
              f'{name}:proof:export_expected')
    fields = {'model': raw['model'], 'status': raw['status'], 'id': raw['id'], 'service_tier': raw.get('service_tier')}
    a.require(raw['model'] in load(run/'transport-policy.json')['model']['allowed_response_ids'] and raw['status'] == 'completed',
              f'{name}:provider:reported_fields')
    return {'witness': response['witness'], 'residual_terms': residual, 'positive_constant': str(constant), 'output_text_parts': len(text),
            'proof_export_sha256': proved['solution_sha256'], 'provider_reported': fields, 'attribution': named}


def unsealed(a, run, name, rows):
    http = load(run/'stages/proposal-1/output/http.json')
    a.require(rows[-1]['event'] == 'stage_finished' and not any(r['event'] in ('episode_finished', 'episode_rejected') for r in rows)
              and not (run/'seal.json').exists() and not (run/'publication-scan.json').exists(), f'{name}:unsealed:no_terminal_event')
    a.require(http['connection_attempts'] == 0 and http['header_sends_started'] == 0 and http['body_sends_started'] == 0
              and http['failure_category'] is None and http['http_status'] is None, f'{name}:unsealed:no_connection')
    stderr = (run/'stages/proposal-1/proposal-1.stderr').read_text()
    process = load(run/'stages/proposal-1/proposal-1.process.json')
    a.require(stderr.rstrip().endswith('ValueError: credential_format') and 'Bearer' not in stderr and process['exit_code'] == 1
              and load(run/'stages/proposal-1/output/pricing-check.json')['accepted'] is True,
              f'{name}:unsealed:stderr_names_credential_format')
    return http


def live1_inventory(a, run, baseline, retained_only):
    files = sorted(p for p in run.rglob('*') if p.is_file())
    observed = {str(p.relative_to(run)): sha(p.read_bytes()) for p in files}
    expected = {k: v['sha256'] for k, v in baseline['files'].items() if v['git_selected'] or not retained_only}
    if retained_only: observed = {k: v for k, v in observed.items() if k in expected or baseline['files'].get(k, {}).get('git_selected', True)}
    a.require(observed == expected, 'live-1:inventory_bound',
              f'{len(set(observed)^set(expected))} paths differ in presence, {sum(1 for k in observed if k in expected and observed[k]!=expected[k])} in content')
    return {'files_compared': len(expected), 'mode': 'retained_only' if retained_only else 'full_historical'}


def operator_scan(a, root, summary_path, report_path, retained_only=False, report_roots=None):
    if summary_path is None:
        a.require(True, 'operator_scan:consistent'); return {'supplied': False}
    summary = load(summary_path); present = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
    bound = absent = None
    if report_path is not None:
        report = load(report_path)
        # Both report shapes: entries relative to experiments/r6 (single-root scan) or carrying their own absolute root.
        entries = {}
        scan_roots = [Path(r) for r in (report_roots or [ROOT])]  # a report carries root indices, never absolute roots
        for e in report['inventory']:
            if not e['path']: continue
            absolute = (scan_roots[e['root_index']]/e['path']) if 'root_index' in e else (ROOT/e['path'])
            if absolute.is_relative_to(root): entries[str(absolute.relative_to(root))] = e['sha256']
        absent = sorted(set(entries)-present)
        # Every present byte was scanned under its current digest; a retained-only checkout may lack scanned files, never add unscanned ones.
        bound = present <= set(entries) and all(sha((root/k).read_bytes()) == entries[k] for k in present) and (retained_only or not absent)
        clean = (report['accepted'] is True and summary['accepted'] is True and report['disclosures'] == [] and summary['disclosures'] == []
                 and not report['incompletely_scanned'] and not report['unreadable_directories'] and not report['irregular_entries']
                 and summary['files_scanned'] == report['files_scanned'] == len(report['inventory']))
        a.require(sha(report_path.read_bytes()) == summary['full_report_sha256'] and bound and clean, 'operator_scan:consistent',
                  'full report digest, scan acceptance or scanned pilot bytes differ from the audited tree')
    else:
        a.require(summary['accepted'] is True and summary['disclosures'] == [] and summary['incompletely_scanned'] == []
                  and summary['unreadable_directories'] == [] and summary['irregular_entries'] == [] and
                  (summary['files_by_top_level'].get(root.name) == len(present) or (retained_only and summary['files_by_top_level'].get(root.name, 0) >= len(present))),
                  'operator_scan:consistent', 'summary counts do not match the audited tree')
    return {'supplied': True, 'files_scanned': summary['files_scanned'], 'pilot_files_present': len(present), 'scanned_bytes_bound_to_tree': bound,
            'scanned_but_absent': absent, 'scope': 'operator assertion with digest commitment; the secret-dependent search is not repeated here'}


def audit(root, *, live1_baseline, summary=None, report=None, retained_only=False):
    a = Audit(); result = {'runs': {}}
    entries = sorted(p.name for p in root.iterdir())
    a.require(sorted(RUNS) == sorted(n for n in entries if (root/n).is_dir()), 'population:exactly_six_runs', str(entries))
    a.require(all((root/n).is_dir() for n in entries), 'population:no_stray_entries')
    live2 = root/'live-2'
    unbound = [m for m, (folder, module) in MODULES.items()
               if not (live2/'provenance'/folder/(m+'.py')).is_file() or sha(Path(module.__file__).read_bytes()) != sha((live2/'provenance'/folder/(m+'.py')).read_bytes())]
    a.require(not unbound, 'modules:bound_to_live_retained_copies', 'imported modules differ from the live run\'s retained copies: '+', '.join(unbound))
    task = r6.get_task(TASK)
    a.require(all(load(root/n/'search-policy.json')['manifest_sha256'] == sha((task.path/'manifest.json').read_bytes()) for n in RUNS), 'task:manifest_bound')
    transmissions, reservations = {}, {}
    for name in RUNS:
        run = root/name; kind = EXPECT[name][0]; live = name.startswith('live')
        sp, policy = versions(a, run, name)
        rows = chain(a, run, name)
        request_bytes, arguments = request(a, run, name, sp, policy, task)
        host_admission(a, run, name, policy, request_bytes, arguments, kind)
        item = {'kind': kind, 'policy_sha256': sp['config_sha256'], 'source_lock_sha256': sp['source_lock_sha256']}
        if kind == 'unsealed':
            http = unsealed(a, run, name, rows)
            reservations[name] = ledger(a, run, name, sp, request_bytes, policy)['reserved_micro_usd']
            actor_admission(a, run, name, kind); duplicate_receipts(a, run, rows, name)
            transmissions[name] = http['body_sends_started']
            result['runs'][name] = item; continue
        seal(a, run, name, rows, kind)
        if kind == 'host':
            item['receipt'] = receipt_record(a, run, name, {'http_status': None}, live)
            result['runs'][name] = item; continue
        reservation = ledger(a, run, name, sp, request_bytes, policy)
        actor_admission(a, run, name, kind)
        http, server = transport(a, run, name, policy, request_bytes, kind, live)
        if live: duplicate_receipts(a, run, rows, name)
        interpretation(a, run, name, request_bytes, live)
        item['accounting'] = accounting(a, run, name, policy, http, server, reservation, live)
        item['receipt'] = receipt_record(a, run, name, http, live)
        if live: reservations[name] = reservation['reserved_micro_usd']; transmissions[name] = http['body_sends_started']
        if kind == 'proof': item['proof'] = proof(a, run, name, rows, task, request_bytes, live)
        result['runs'][name] = item
    signed = load(live2/'provenance/pilot-harness/policies/responses-live-pilot-v1.json')
    ceiling = signed['limits']['total_micro_usd']; attempts = signed['authorization']['maximum_attempts']
    a.require(sum(transmissions.values()) <= attempts and sum(transmissions.values()) == 1, 'campaign:one_transmission_under_signed_authorization',
              f'transmissions {transmissions}')
    a.require(reservations == {'live-1': 102400, 'live-2': 102400}, 'campaign:reservations_recorded')
    result['campaign'] = {'signed_policy_sha256': SIGNED_POLICY, 'maximum_attempts': attempts, 'ceiling_micro_usd': ceiling,
        'transmissions_started': transmissions, 'reservations_micro_usd': reservations,
        'reserved_total_micro_usd': sum(reservations.values()), 'reserved_total_exceeds_ceiling': sum(reservations.values()) > ceiling,
        'guard_scope': 'per-run-directory ledger; the ceiling bounded each directory, not the authorization (documented defect)'}
    result['live-1_inventory'] = live1_inventory(a, root/'live-1', live1_baseline, retained_only)
    result['operator_scan'] = operator_scan(a, root, summary, report, retained_only)
    missing = sorted(set(CASES)-set(a.cases)); extra = sorted(set(a.cases)-set(CASES))
    if missing or extra: raise Rejection('cases:population', f'missing {missing} extra {extra}')
    result.update(accepted=all(a.cases.values()), cases=a.cases, case_count=len(CASES),
                  module_sha256={m: sha(Path(mod.__file__).read_bytes()) for m, (_, mod) in MODULES.items()},
                  task_manifest_sha256=sha((task.path/'manifest.json').read_bytes()), retained_only=retained_only,
                  live_model_calls=0, credentials_read=0, program_sha256=sha(Path(__file__).read_bytes()),
                  scope='historical audit over retained bytes; no native execution, verifier run or inference')
    return result


def write_inventory(run, output):
    files = sorted(p for p in run.rglob('*') if p.is_file())
    ignored = set(subprocess.run(['git', 'check-ignore', '--stdin'], input='\n'.join(str(p) for p in files), capture_output=True,
                                 text=True, cwd=str(run)).stdout.splitlines())
    record = {'schema_version': 'r6-007-live1-inventory-1', 'run': run.name,
              'files': {str(p.relative_to(run)): {'sha256': sha(p.read_bytes()), 'bytes': p.stat().st_size, 'git_selected': str(p) not in ignored} for p in files}}
    record['file_count'] = len(record['files']); record['git_selected_count'] = sum(v['git_selected'] for v in record['files'].values())
    record['inventory_sha256'] = sha(canonical({k: v['sha256'] for k, v in record['files'].items()}))
    output.write_bytes(json.dumps(record, sort_keys=True, indent=1).encode()+b'\n')
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs', type=Path, required=True)
    parser.add_argument('--live1-inventory', type=Path, help='retained live-1 inventory to compare against')
    parser.add_argument('--write-live1-inventory', type=Path, help='write the live-1 inventory and exit')
    parser.add_argument('--operator-scan-summary', type=Path)
    parser.add_argument('--operator-scan-report', type=Path, help='full report; binds scanned pilot bytes to the audited tree')
    parser.add_argument('--retained-only', action='store_true', help='compare only Git-selected live-1 files')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.write_live1_inventory:
        record = write_inventory(args.runs.resolve()/'live-1', args.write_live1_inventory)
        print(json.dumps({k: record[k] for k in ('file_count', 'git_selected_count', 'inventory_sha256')}, indent=1)); return
    if args.live1_inventory is None: parser.error('--live1-inventory is required for an audit')
    if args.output and args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    try:
        result = audit(args.runs.resolve(), live1_baseline=load(args.live1_inventory), summary=args.operator_scan_summary,
                       report=args.operator_scan_report, retained_only=args.retained_only)
    except Rejection as rejection:
        print(json.dumps({'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}, indent=1)); sys.exit(1)
    if args.output: r6.write_json(args.output, result)
    print(json.dumps({'accepted': result['accepted'], 'case_count': result['case_count'], 'campaign': result['campaign']['transmissions_started'],
                      'reserved_total_exceeds_ceiling': result['campaign']['reserved_total_exceeds_ceiling']}, indent=1))
    sys.exit(0 if result['accepted'] else 1)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""R6-009 focused controls: the scientific contract, the campaign identity and the task-by-draw ledger. Canned; nothing connects.

The actor runs as a plain subprocess against the loopback TLS fixture with a synthetic canary, so the contract validation of the
envelope, the slot-bound permit and the identical model-input bytes across policy revisions are read from real records. The
R6-008 persistence fault sweep is carried forward against the cohort driver and ledger.
"""
import argparse
import copy
import json
import os
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import types

import campaign_ledger as base_ledger
import cohort_budget as budget
import cohort_contract as contract
import cohort_episode as driver
import cohort_https as actor
import cohort_ledger as ledger
import credential
import episode
import events
import live_tls_fixture
import pricing_gate_v2 as v2
import pricing_gate_v3 as gate
import run as r6
from test_proposals import Suite, rejected, require
from unittest.mock import patch

CASES = '''policy_frozen_disabled contract_frozen_canonical_and_bound request_carries_contract_not_policy envelope_identical_across_revisions
slot_identity_absent_from_model_bytes policy_conflicts_with_contract_rejected host_admission_recomputes_envelope actor_validates_envelope_against_contract
actor_permit_bound_to_slot actor_live_rejects_unsigned_policy campaign_identity_survives_revision unregistered_revision_refused
revision_registration_rules distinct_campaigns_share_contract slot_rules activation_bound_to_policy_and_mode
actor_grant_before_first_header_byte actor_commitment_recorded actor_credential_format_classified persistence_fault_sweep
counters_separate ca_bundle_pinned endpoint_allowlist_exact'''.split()
PREPARED = r6.ROOT/'runs/provider-checkpoint-v1/d1_valid/prepared.json'
TERMINATED = {'exit_code': 1, 'workload_empty_after_cleanup': True, 'monitor_error': None, 'observation_error': None, 'accounting_scope': 'sandbox_process_tree'}
SENT = {'body_sends_started': 1, 'header_sends_started': 1, 'send_outcome': 'returned'}
UNSENT = {'body_sends_started': 0, 'header_sends_started': 0}
D1, C8 = 'verinf-d1-70', 'c1-c8-2p18'


def refused(fn, code):
    try: fn()
    except ledger.Failure as error:
        require(error.code == code, f'wrong code {error.code}, wanted {code}')
        return {'rejected': True, 'code': error.code}
    raise AssertionError('accepted: '+code)


def gate_refused(fn, code):
    try: fn()
    except gate.Failure as error:
        require(error.code == code, f'wrong code {error.code}, wanted {code}')
        return {'rejected': True, 'code': error.code}
    raise AssertionError('accepted: '+code)


def signed_record(c, **overrides):
    record = {'approved_by': 'author', 'approved_utc': '2026-09-14T00:00:00Z', 'model_id': contract.MODEL, 'schedule': dict(c['campaign']['schedule']),
              'maximum_micro_usd': c['limits']['total_micro_usd'], 'maximum_presend_attempts': contract.MAXIMUM_PRESEND_ATTEMPTS, 'scope': 'canned'}
    record.update(overrides); return record


def signed(c, **overrides):
    record = signed_record(c, **{k: v for k, v in overrides.items() if k in ('approved_by', 'approved_utc', 'scope', 'model_id', 'schedule', 'maximum_micro_usd', 'maximum_presend_attempts')})
    policy = {**copy.deepcopy(c), 'live_enabled': True, 'authorization': record}
    policy['campaign'] = {**policy['campaign'], 'schedule': record['schedule']}; policy['limits'] = {**policy['limits'], 'total_micro_usd': record['maximum_micro_usd']}
    return policy


def revised(c, **changes):
    """A policy revision: same campaign and contract, different pricing digests or authorization metadata."""
    policy = copy.deepcopy(c); policy['revision'] = c['revision']+1; policy['previous_policy_sha256'] = v2.sha(v2.canonical(c)+b'\n')
    policy['pricing_admission'] = {**policy['pricing_admission'], 'sources': {r: {**s, 'raw_sha256': 'f'*64} for r, s in policy['pricing_admission']['sources'].items()}}
    for k, val in changes.items(): policy[k] = val
    return policy


def temp_book(directory, policy, live=False):
    book = ledger.Ledger(directory, policy['campaign']['id']); book.activate(policy, live); return book


def bind(): return {'request_sha256': 'b'*64, 'arguments_sha256': 'c'*64, 'contract_sha256': contract.contract_sha256()}
def reservation_shape(): return {'reserved_micro_usd': 102400, 'message_utf8_bytes': 5000}
def reserve(book, policy, task, draw, episode='run'): return book.reserve(episode, policy, task, draw, reservation_shape(), bind(), {'accepted': True})[0]
def with_grant(book, permit):
    ledger.commit_grant(book.grant_slot(permit), ledger.grant_record(permit, 1)); return book.grant_slot(permit)

from pathlib import Path


def units(output):
    suite = Suite(output, CASES)
    c = contract.config(); contract_value = contract.contract(); task = r6.get_task(D1); prepared = r6.read_json(PREPARED)

    def frozen_disabled():
        require(c['live_enabled'] is False and c['authorization'] is None and c['live_model_calls_authorized'] == 0 and c['revision'] >= 1)
        require(not contract.campaign_ledger(True).path.exists(), 'live ledger exists before signing')
        require(contract.campaign_ledger(False).snapshot()[1]['purpose'] == 'rehearsal')
        rejected(lambda: contract.live_permitted(c), 'cohort_live_disabled')
        return {'live_enabled': False, 'campaign_id': c['campaign']['id'], 'revision': c['revision'], 'schedule': c['campaign']['schedule']}
    suite.case('policy_frozen_disabled', frozen_disabled)

    def contract_frozen():
        require(contract.CONTRACT.read_bytes() == v2.canonical(contract_value)+b'\n' and gate.check_contract(contract_value) == contract.contract_sha256())
        require(contract_value['instruction']['sha256'] == r6.sha(contract.PROMPT) and contract_value['instruction']['bytes'] == contract.PROMPT.stat().st_size)
        require(contract_value['generation']['options'] == c['request'] and c['contract_sha256'] == contract.contract_sha256())
        require(set(contract_value['generation']['omitted']) & set(contract_value['generation']['options']) == set())
        require(contract_value['request_schema']['sha256'] == r6.sha(r6.ROOT/'schema/cohort-request.schema.json'))
        return {'contract_sha256': contract.contract_sha256(), 'instruction_bytes': contract_value['instruction']['bytes'], 'omitted_options': len(contract_value['generation']['omitted'])}
    suite.case('contract_frozen_canonical_and_bound', contract_frozen)

    def request_binding():
        request = budget.request(task, prepared); value = json.loads(request)
        require('policy_sha256' not in value and value['contract_sha256'] == contract.contract_sha256() and value['schema_version'] == gate.REQUEST_SCHEMA)
        require(set(value['binding']) >= {'task_id', 'manifest_sha256', 'challenge_sha256', 'input_ir_sha256', 'final_ir_sha256', 'prompt_sha256'})
        require(contract.policy_sha256()[:8] not in request.decode() and c['campaign']['id'] not in request.decode())
        return {'request_keys': sorted(value), 'binding_keys': sorted(value['binding'])}
    suite.case('request_carries_contract_not_policy', request_binding)

    sources = r6.ROOT/c['pricing_sources']

    def identical_envelopes():
        request = budget.request(task, prepared); arguments = budget.arguments(request); body = v2.entity_body(arguments)
        other = revised(signed(c, approved_utc='2026-09-15T00:00:00Z'))
        with patch.object(contract, 'config', lambda: other):
            require(budget.request(task, prepared) == request and budget.arguments(request) == arguments and v2.entity_body(budget.arguments(request)) == body)
        a1 = gate.admission(c, contract_value, contract.PROMPT.read_text(), sources, arguments, request, time.time())
        require(a1['contract_sha256'] == contract.contract_sha256() and a1['body_sha256'] == v2.sha(body))
        return {'entity_body_sha256': v2.sha(body), 'identical_under_revised_policy': True}
    suite.case('envelope_identical_across_revisions', identical_envelopes)

    def slot_absent():
        request = budget.request(task, prepared); arguments = budget.arguments(request); text = v2.entity_body(arguments).decode()
        for needle in ('draw', 'reservation', 'campaign', c['campaign']['id'], contract.policy_sha256(), 'slot'):
            require(needle not in text, 'model-visible bytes carry '+needle)
        return {'checked_absent': ['draw', 'reservation', 'campaign id', 'policy digest', 'slot']}
    suite.case('slot_identity_absent_from_model_bytes', slot_absent)

    def policy_conflicts():
        bad = copy.deepcopy(c); bad['request'] = {**bad['request'], 'max_output_tokens': 4097}
        gate_refused(lambda: gate.check_policy(bad, contract_value), 'policy_generation_conflict')
        bad = copy.deepcopy(c); bad['request'] = {**bad['request'], 'temperature': 0}
        gate_refused(lambda: gate.check_policy(bad, contract_value), 'policy_generation_conflict')
        bad = copy.deepcopy(c); bad['limits'] = {**bad['limits'], 'output_tokens': 2048}
        gate_refused(lambda: gate.check_policy(bad, contract_value), 'policy_limit_conflict_output_tokens')
        bad = copy.deepcopy(c); bad['model'] = {**bad['model'], 'requested_id': 'gpt-5.4'}
        gate_refused(lambda: gate.check_policy(bad, contract_value), 'policy_model_conflict')
        bad = copy.deepcopy(c); bad['contract_sha256'] = 'f'*64
        gate_refused(lambda: gate.check_policy(bad, contract_value), 'policy_contract_binding')
        return {'rejections': ['generation option', 'omitted option added', 'scientific limit', 'model', 'contract digest']}
    suite.case('policy_conflicts_with_contract_rejected', policy_conflicts)

    sources = r6.ROOT/c['pricing_sources']
    def host_envelope():
        request = budget.request(task, prepared); arguments = budget.arguments(request); instruction = contract.PROMPT.read_text(); now = time.time()
        crossed = {}
        a = copy.deepcopy(arguments); a['input'][0]['content'] += 'Altered.'; crossed['altered_prompt_text'] = gate_refused(lambda: gate.admission(c, contract_value, instruction, sources, a, request, now), 'contract_envelope_messages')['code']
        a = copy.deepcopy(arguments); a['temperature'] = 0; crossed['omitted_option_present'] = gate_refused(lambda: gate.admission(c, contract_value, instruction, sources, a, request, now), 'contract_envelope_keys')['code']
        a = copy.deepcopy(arguments); a['max_output_tokens'] = 4097; crossed['generation_option'] = gate_refused(lambda: gate.admission(c, contract_value, instruction, sources, a, request, now), 'contract_generation_max_output_tokens')['code']
        a = copy.deepcopy(arguments); a['model'] = 'gpt-5.4'; crossed['model'] = gate_refused(lambda: gate.admission(c, contract_value, instruction, sources, a, request, now), 'contract_generation_model')['code']
        value = json.loads(request); value['contract_sha256'] = 'f'*64; foreign = events.canonical(value)+b'\n'
        crossed['foreign_contract_digest'] = gate_refused(lambda: gate.admission(c, contract_value, instruction, sources, budget.arguments(foreign), foreign, now), 'contract_request_binding')['code']
        crossed['instruction_bytes'] = gate_refused(lambda: gate.admission(c, contract_value, instruction+' ', sources, arguments, request, now), 'contract_instruction_bytes')['code']
        require(gate.admission(c, contract_value, instruction, sources, arguments, request, now)['accepted'] is True)
        return crossed
    suite.case('host_admission_recomputes_envelope', host_envelope)

    def actor_run(directory, *, credential_text=None, mode='rehearsal', policy=None, book=None, permit=None, arguments_mutation=None, task_id=D1, draw=1, actor_task=None, actor_draw=None):
        d = Path(directory); run = d/'run'; run.mkdir(exist_ok=True)
        policy_value = policy or c; policy_path = d/'policy.json'; policy_path.write_bytes(v2.canonical(policy_value)+b'\n')
        request = budget.request(task, prepared); arguments = budget.arguments(request)
        if arguments_mutation: arguments = arguments_mutation(copy.deepcopy(arguments))
        (d/'request.json').write_bytes(request); r6.write_json(d/'arguments.json', arguments)
        if book is None:
            admitted = gate.admission(policy_value, contract_value, contract.PROMPT.read_text(), sources, budget.arguments(request), request, time.time())
            book = temp_book(d/'ledger', policy_value, mode == 'live' and policy_value.get('live_enabled') is True)
            permit, _ = book.reserve('probe', policy_value, task_id, draw, budget.reservation(arguments), {'request_sha256': gate.sha(request), 'arguments_sha256': gate.sha(gate.canonical(budget.arguments(request))), 'contract_sha256': contract.contract_sha256()}, admitted)
        r6.write_json(d/'permit.json', permit)
        out = d/'out'; out.mkdir(exist_ok=True); grant = book.grant_slot(permit)
        nonce = credential.nonce(); canary = credential.derive(nonce)
        cred = d/'credential'; cred.write_text(credential.header(canary)+'\n' if credential_text is None else credential_text)
        base_args = ['--mode', mode, '--policy', str(policy_path), '--contract', str(contract.CONTRACT), '--instruction', str(contract.PROMPT), '--arguments', str(d/'arguments.json'),
                     '--credential-file', str(cred), '--out', str(out), '--sources', str(sources), '--permit', str(d/'permit.json'), '--ledger', str(book.path),
                     '--request', str(d/'request.json'), '--episode', 'probe', '--task', actor_task or task_id, '--draw', str(actor_draw or draw), '--grant', str(grant), '--commitment-nonce', nonce]
        if mode == 'rehearsal':
            fixture = driver.canned(task, request); r6.write_json(d/'fixture.json', fixture)
            with live_tls_fixture.materialize(run, 'valid') as (ca, cert, key):
                proc = subprocess.run([sys.executable, '-I', '-S', '-B', str(r6.ROOT/'cohort_https.py'), *base_args, '--ca', str(ca), '--fixture', str(d/'fixture.json'),
                                       '--server-cert', str(cert), '--server-key', str(key)], capture_output=True, text=True, timeout=120)
        else:
            ca, _ = contract.bundle()
            proc = subprocess.run([sys.executable, '-I', '-S', '-B', str(r6.ROOT/'cohort_https.py'), *base_args, '--ca', str(ca)], capture_output=True, text=True, timeout=120)
        require(proc.returncode == 0, 'actor crashed: '+proc.stderr[-800:])
        return types.SimpleNamespace(http=r6.read_json(out/'http.json'), out=out, grant=grant, canary=canary, nonce=nonce, request=request, book=book, permit=permit)

    def actor_envelope():
        outcomes = {}
        for label, mutation, code in (('altered_prompt_text', lambda a: (a['input'][0].__setitem__('content', a['input'][0]['content']+'Altered.'), a)[1], 'contract_envelope_messages'),
                                      ('omitted_option_present', lambda a: (a.__setitem__('temperature', 0), a)[1], 'contract_envelope_keys'),
                                      ('generation_option', lambda a: (a.__setitem__('max_output_tokens', 4097), a)[1], 'contract_generation_max_output_tokens')):
            with tempfile.TemporaryDirectory() as d:
                r = actor_run(d, arguments_mutation=mutation)
                require(r.http['failure_category'] == 'contract_admission' and r.http['pricing_failure_code'] == code and r.http['connection_attempts'] == 0
                        and r.http['grant_committed'] is False, label+': '+str({k: r.http[k] for k in ('failure_category', 'pricing_failure_code', 'ledger_failure_code')}))
                outcomes[label] = code
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d); require(r.http['http_status'] == 200 and r.http['grant_committed'] is True)
        return {**outcomes, 'unaltered': 'sent'}
    suite.case('actor_validates_envelope_against_contract', actor_envelope)

    def actor_slot():
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d, actor_draw=2)
            require(r.http['failure_category'] == 'cohort_ledger' and r.http['ledger_failure_code'] == 'cohort_permit_binding' and r.http['connection_attempts'] == 0)
        with tempfile.TemporaryDirectory() as d:
            first = actor_run(d); require(first.http['http_status'] == 200)
            first.book.reconcile(first.permit, TERMINATED, first.http, {})
            second = Path(d)/'second'; second.mkdir()
            r = actor_run(second, book=first.book, permit=first.permit)
            require(r.http['ledger_failure_code'] == 'cohort_permit_not_last_row' and r.http['connection_attempts'] == 0)
            require(r.http['slot'] == D1+'/1' and 'slot' in r.http, 'slot identity missing from the receipt')
        return {'draw_mismatch': 'cohort_permit_binding', 'consumed_permit': 'cohort_permit_not_last_row', 'slot_in_receipt': True}
    suite.case('actor_permit_bound_to_slot', actor_slot)

    def live_unsigned():
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d, mode='live', policy=c)
            require(r.http['failure_category'] == 'authorization' and r.http['ledger_failure_code'] == 'cohort_live_disabled' and r.http['connection_attempts'] == 0)
        with tempfile.TemporaryDirectory() as d:
            live_policy = signed(c); rehearsal_book = temp_book(Path(d)/'r', live_policy, False)
            permit = reserve(rehearsal_book, live_policy, D1, 1, 'probe')
            r = actor_run(d, mode='live', policy=live_policy, book=rehearsal_book, permit=permit)
            require(r.http['failure_category'] == 'cohort_ledger' and r.http['ledger_failure_code'] == 'cohort_activation_purpose' and r.http['connection_attempts'] == 0)
        return {'disabled_policy': 'cohort_live_disabled', 'rehearsal_ledger_under_live_policy': 'cohort_activation_purpose', 'connections': 0}
    suite.case('actor_live_rejects_unsigned_policy', live_unsigned)

    def identity_survives():
        with tempfile.TemporaryDirectory() as d:
            live_policy = signed(c, schedule={D1: 3}); book = temp_book(d, live_policy, True)
            p1 = reserve(book, live_policy, D1, 1); with_grant(book, p1); book.reconcile(p1, TERMINATED, SENT, {})
            p2 = reserve(book, live_policy, D1, 2); book.reconcile(p2, TERMINATED, UNSENT, {})  # a pre-send release: slot 2 stays available
            rev2 = revised(live_policy, authorization={**live_policy['authorization'], 'approved_utc': '2026-09-15T00:00:00Z'})
            refused(lambda: book.reserve('run', rev2, D1, 2, reservation_shape(), bind(), {}), 'cohort_revision_not_current')
            book.register_revision(rev2, True)
            _, s = book.snapshot()
            require(s['revision'] == 1 and s['policy_sha256'] == v2.sha(v2.canonical(rev2)+b'\n') and s['slots'][D1+'/1']['consumed'] is True and s['transmissions_consumed'] == 1)
            refused(lambda: book.reserve('run', live_policy, D1, 2, reservation_shape(), bind(), {}), 'cohort_revision_not_current')  # the old revision can no longer reserve
            refused(lambda: book.reserve('run', rev2, D1, 1, reservation_shape(), bind(), {}), 'cohort_slot_consumed')            # consumed before the refresh stays consumed
            p3 = reserve(book, rev2, D1, 2); require(p3['slot_attempt'] == 2 and p3['policy_sha256'] == s['policy_sha256'])
            with_grant(book, p3); book.reconcile(p3, TERMINATED, SENT, {})
            _, s = book.snapshot(); require(s['transmissions_consumed'] == 2 and s['revisions'][0] != s['revisions'][1] and len(s['revisions']) == 2)
        return {'consumed_before_refresh': 'still consumed', 'old_revision': 'cohort_revision_not_current', 'released_slot': 'retried under the new revision, same slot',
                'continuous_accounting': '2 consumed across 2 revisions'}
    suite.case('campaign_identity_survives_revision', identity_survives)

    def unregistered():
        with tempfile.TemporaryDirectory() as d:
            live_policy = signed(c); book = temp_book(d, live_policy, True)
            rev2 = revised(live_policy)
            refused(lambda: book.reserve('run', rev2, D1, 1, reservation_shape(), bind(), {}), 'cohort_revision_not_current')
            refused(lambda: ledger.check_activation(book.snapshot()[1], rev2, True), 'cohort_revision_not_current')
            p = reserve(book, live_policy, D1, 1); raw = book.path.read_bytes()
            refused(lambda: ledger.verify_permit(p, raw, rev2, True, 'run', D1, 1), 'cohort_revision_not_current')
            require(ledger.verify_permit(p, raw, live_policy, True, 'run', D1, 1)['revision'] == 0)
        return {'unregistered_policy_digest': 'refused by host and actor'}
    suite.case('unregistered_revision_refused', unregistered)

    def registration_rules():
        with tempfile.TemporaryDirectory() as d:
            live_policy = signed(c); book = temp_book(d, live_policy, True)
            other = revised(live_policy); other['campaign'] = {**other['campaign'], 'id': 'x'*32}
            refused(lambda: book.register_revision(other, True), 'cohort_revision_identity')
            other = revised(live_policy); other['contract_sha256'] = 'f'*64
            refused(lambda: book.register_revision(other, True), 'cohort_revision_identity')
            shrunk = revised(signed(c, schedule={D1: 2})); shrunk['campaign']['id'] = live_policy['campaign']['id']
            refused(lambda: book.register_revision(shrunk, True), 'cohort_revision_schedule_shrunk')
            refused(lambda: book.register_revision(revised(live_policy), False), 'cohort_revision_identity')  # purpose
            p = reserve(book, live_policy, D1, 1)
            refused(lambda: book.register_revision(revised(live_policy), True), 'cohort_revision_while_open')
            with_grant(book, p); book.reconcile(p, TERMINATED, SENT, {})
            poorer = revised(signed(c, maximum_micro_usd=1)); poorer['campaign']['id'] = live_policy['campaign']['id']
            refused(lambda: book.register_revision(poorer, True), 'cohort_revision_money_below_committed')
            rev2 = revised(live_policy); book.register_revision(rev2, True)
            refused(lambda: book.register_revision(rev2, True), 'cohort_revision_already_registered')
        return {'refused': ['campaign identity', 'contract', 'schedule shrunk', 'purpose', 'while open', 'money below committed', 'duplicate']}
    suite.case('revision_registration_rules', registration_rules)

    def distinct_campaigns():
        with tempfile.TemporaryDirectory() as d:
            a_policy = signed(c); b_policy = signed(c); b_policy['campaign'] = {**b_policy['campaign'], 'id': 'b'*32}
            require(a_policy['contract_sha256'] == b_policy['contract_sha256'])
            a = temp_book(Path(d)/'a', a_policy, True); b = temp_book(Path(d)/'b', b_policy, True)
            pa = reserve(a, a_policy, D1, 1); with_grant(a, pa); a.reconcile(pa, TERMINATED, SENT, {})
            require(b.snapshot()[1]['transmissions_consumed'] == 0 and a.snapshot()[1]['transmissions_consumed'] == 1)
            refused(lambda: ledger.check_activation(a.snapshot()[1], b_policy, True), 'cohort_activation_campaign')
        return {'shared_contract': True, 'independent_ledgers': True}
    suite.case('distinct_campaigns_share_contract', distinct_campaigns)

    def slots():
        with tempfile.TemporaryDirectory() as d:
            live_policy = signed(c, schedule={D1: 2}, maximum_micro_usd=2*102400, maximum_presend_attempts=3); book = temp_book(d, live_policy, True)
            refused(lambda: reserve(book, live_policy, C8, 1), 'cohort_slot_not_scheduled')
            refused(lambda: reserve(book, live_policy, D1, 3), 'cohort_slot_not_scheduled')
            refused(lambda: reserve(book, live_policy, D1, 0), 'cohort_slot_not_scheduled')
            for i in range(3):
                p = reserve(book, live_policy, D1, 1); require(p['slot_attempt'] == i+1); book.reconcile(p, TERMINATED, UNSENT, {})
            refused(lambda: reserve(book, live_policy, D1, 1), 'cohort_presend_attempts_exhausted')
            p = reserve(book, live_policy, D1, 2); book.reconcile(p, None, None, {})  # unknown consumes the draw, no retry
            refused(lambda: reserve(book, live_policy, D1, 2), 'cohort_slot_consumed')
            _, s = book.snapshot(); require(s['transmissions_consumed'] == 1 and s['slots'][D1+'/1']['released'] == 3 and s['committed_micro_usd'] == 102400)
        with tempfile.TemporaryDirectory() as d:
            live_policy = signed(c, schedule={D1: 2}, maximum_micro_usd=102400); book = temp_book(d, live_policy, True)
            p = reserve(book, live_policy, D1, 1); with_grant(book, p); book.reconcile(p, TERMINATED, SENT, {})
            refused(lambda: reserve(book, live_policy, D1, 2), 'cohort_money_exhausted')
        return {'wrong_task': 'cohort_slot_not_scheduled', 'draw_out_of_schedule': 'cohort_slot_not_scheduled', 'same_slot_presend_retries': 3,
                'unknown': 'consumes the draw', 'global_money_cap': 'cohort_money_exhausted'}
    suite.case('slot_rules', slots)

    def bound_activation():
        live_policy = signed(c)
        with tempfile.TemporaryDirectory() as d:
            rehearsal = temp_book(Path(d)/'r', c, False); p = reserve(rehearsal, c, D1, 1); raw = rehearsal.path.read_bytes()
            refused(lambda: ledger.verify_permit(p, raw, live_policy, True, 'run', D1, 1), 'cohort_activation_purpose')
            require(ledger.verify_permit(p, raw, c, False, 'run', D1, 1)['purpose'] == 'rehearsal')
            foreign = signed(c, approved_by='someone else'); other = temp_book(Path(d)/'o', foreign, True); p2 = reserve(other, foreign, D1, 1); raw2 = other.path.read_bytes()
            refused(lambda: ledger.verify_permit(p2, raw2, live_policy, True, 'run', D1, 1), 'cohort_revision_not_current')
        return {'rehearsal_under_live': 'cohort_activation_purpose', 'foreign_authorization': 'cohort_revision_not_current'}
    suite.case('activation_bound_to_policy_and_mode', bound_activation)

    def grant_order():
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d); http = r.http; record = ledger.read_grant(r.grant, r.permit)
            require(http['grant_committed'] is True and http['grant_id'] == record['grant_id'] and http['tls_verified_at_ns'] < record['at_ns'] == http['grant_created_at_ns'] < http['grant_durable_at_ns'] < http['header_send_at_ns'])
            require(http['send_outcome'] == 'returned' and http['http_status'] == 200 and (r.out/'outbound-body.json').read_bytes() == (r.out/'serialized-body.json').read_bytes() == (r.out/'received-body.json').read_bytes())
            require(r.grant.parent.parent.parent.name == 'slots' and r.grant.name == r.permit['reservation_id'], 'grant slot is not the attempt slot under the (task, draw) slot')
        return {'order': 'tls_verified < grant created < grant durable < header_send', 'slot': 'slots/<task>/<draw>/<reservation_id>'}
    suite.case('actor_grant_before_first_header_byte', grant_order)

    def commitment():
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d); expected = actor.commitment(r.nonce, credential.header(r.canary))
            require(r.http['credential_commitment_sha256'] == expected and r.canary not in (r.out/'http.json').read_text())
        return {'commitment': 'sha256(domain:nonce:header)', 'value_absent_from_records': True}
    suite.case('actor_commitment_recorded', commitment)

    def credential_format():
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d, credential_text='sk-no-bearer-prefix\n')
            require(r.http['failure_category'] == 'credential_format' and r.http['connection_attempts'] == 0 and r.http['grant_committed'] is False
                    and 'Bearer' not in (r.out/'http.json').read_text())
        return {'classified': 'credential_format', 'connections': 0}
    suite.case('actor_credential_format_classified', credential_format)

    def production(stage_double=None, copy_failure=False, reconcile_failure=False, patches=None):
        """Production execute/invoke/reconcile/finalize with doubles for setup, preparation and the stage launcher.
        `patches(ctx)` may return extra (target, attribute, replacement) triples for fault injection."""
        with tempfile.TemporaryDirectory() as d:
            d = Path(d); run = d/'run'; run.mkdir()
            book = ledger.Ledger(d/'ledgers'/c['campaign']['id']/'rehearsal', c['campaign']['id']); book.activate(c, False)
            tools = {'expected': r6.frozen_task(task)[1], 'runtime': {'stdlib': '/probe', 'extension_binaries': []}, 'runtime_path': d, 'python': Path(sys.executable)}
            def prepare_double(run, task, tools):
                request = budget.request(task, prepared)
                (run/'live-request.json').write_bytes(request); r6.write_json(run/'live-arguments.json', budget.arguments(request)); return request
            def default_stage(run, name, binary, argv, mounts, grant, **kwargs):
                raise episode.StageFailure('proposal-1', 'stage_rejected', 'synthetic')
            real_copy = shutil.copytree
            def copy(source, destination, *args, **kwargs):
                if copy_failure and Path(destination) == run/'transport-pricing-sources': raise PermissionError('synthetic copy failure after reservation')
                return real_copy(source, destination, *args, **kwargs)
            real_reconcile = book.reconcile
            def failing_reconcile(*args, **kwargs): raise OSError('synthetic reconciliation failure')
            ctx = types.SimpleNamespace(run=run, book=book, d=d)
            extra = patches(ctx) if patches else []
            raised = None
            with patch.object(contract, 'campaign_ledger', lambda live, cfg=None: book), patch.object(driver, 'setup', lambda *a: tools), \
                 patch.object(driver, 'prepare', prepare_double), patch.object(driver.network, 'stage', stage_double or default_stage), \
                 patch.object(shutil, 'copytree', copy), patch.object(book, 'reconcile', failing_reconcile if reconcile_failure else real_reconcile):
                stack = [patch.object(t, a, r) for t, a, r in extra]
                for x in stack: x.start()
                try:
                    try: result = driver.execute(run, task, 1, 'rehearsal', d, None)
                    except Exception as caught: result = None; raised = type(caught).__name__
                finally:
                    for x in reversed(stack): x.stop()
            rows = events.read(run/'events.ndjson') if (run/'events.ndjson').exists() else []
            sealed = (run/'seal.json').exists()
            if sealed:
                seal = r6.read_json(run/'seal.json')
                require(seal['event_count'] == len(rows) and all(r6.sha(run/k) == v for k, v in seal['retained_sha256'].items()), 'not sealed consistently')
            raw, state = book.snapshot(); ledger_rows = ledger.parse(raw)
            return types.SimpleNamespace(run=run, result=result, raised=raised, rows=rows, state=state, book=book, sealed=sealed,
                                         ledger_rows=ledger_rows, events=[r['event'] for r in rows],
                                         retained_grant=(run/'stages/proposal-1/grant/send-grant.json').exists(),
                                         accounting=r6.read_json(run/'accounting.json') if (run/'accounting.json').exists() else None,
                                         summary=r6.read_json(run/'credential-summary.json') if (run/'credential-summary.json').exists() else None,
                                         reconciliation=r6.read_json(run/'campaign-reconciliation.json') if (run/'campaign-reconciliation.json').exists() else None,
                                         slot_files=sorted(p.name for p in book.slots.rglob('*') if p.is_file()) if book.slots.exists() else [])

    def stage_writing(http_bytes, process_value, grant=True):
        def stage(run, name, binary, argv, mounts, slot, **kwargs):
            out = run/'stages/proposal-1/output'; out.mkdir(parents=True); (out.parent/'command.json').write_bytes(b'{}\n')
            if grant:
                permit = r6.read_json(run/'campaign-permit.json'); ledger.commit_grant(slot, ledger.grant_record(permit, time.monotonic_ns()))
            r6.write_json(out.parent/'proposal-1.process.json', process_value); (out/'http.json').write_bytes(http_bytes)
            raise episode.StageFailure('proposal-1', 'resource_exhaustion', 'synthetic interruption')
        return stage

    def ledger_fd_writer(ctx, behaviour):
        """Patch os.write only for the ledger file's inode."""
        inode = ctx.book.path.stat().st_ino; real = os.write; calls = []
        def write(fd, data):
            try: same = os.fstat(fd).st_ino == inode
            except OSError: same = False
            if not same: return real(fd, data)
            calls.append(len(data)); return behaviour(real, fd, data, len(calls))
        return [(os, 'write', write)]

    def json_writer_failure(target_name):
        real = r6.write_json
        def write_json(path, value):
            if Path(path).name == target_name: raise OSError(5, 'synthetic evidence-write failure: '+target_name)
            return real(path, value)
        return lambda ctx: [(r6, 'write_json', write_json)]

    def head_failure_at(rows_at, also_snapshot=False):
        def patches(ctx):
            real = ctx.book._write_head; real_snapshot = ctx.book.snapshot
            def head(rows, last_hash):
                if rows == rows_at: raise OSError(5, 'synthetic head failure at row '+str(rows))
                return real(rows, last_hash)
            def snapshot():
                if also_snapshot: raise OSError(5, 'synthetic snapshot failure after recovery')
                return real_snapshot()
            return [(ctx.book, '_write_head', head), (ctx.book, 'snapshot', snapshot)]
        return patches

    def append_failure(ctx):
        real = ctx.book._append
        def append(rows, row):
            if row['kind'] in ledger.TERMINAL: raise OSError(5, 'synthetic append failure before the terminal row')
            return real(rows, row)
        return [(ctx.book, '_append', append)]

    def event_failure_once(event_name, also=None):
        def patches(ctx):
            real = events.append; fired = []
            def append(run, stage, event, payload, *a, **k):
                if event == event_name and not fired: fired.append(1); raise OSError(5, 'synthetic receipt failure: '+event_name)
                return real(run, stage, event, payload, *a, **k)
            return [(events, 'append', append)]+(also(ctx) if also else [])
        return patches

    def copyfile_failure(ctx):
        real = shutil.copyfile
        def copyfile(src, dst, *a, **k):
            if 'slots' in str(src): raise OSError(5, 'synthetic evidence copy failure')
            return real(src, dst, *a, **k)
        return [(shutil, 'copyfile', copyfile)]

    valid_http = lambda: events.canonical({'connection_attempts': 0, 'header_sends_started': 0, 'header_sends_returned': 0, 'body_sends_started': 0,
        'body_sends_returned': 0, 'failure_category': None, 'http_status': None, 'grant_committed': False, 'send_outcome': 'not_started', 'mode': 'rehearsal',
        'request_sha256': 'a'*64, 'credential_commitment_sha256': None, 'commitment_nonce': 'n', 'reservation_id': None, 'tls_verified_at_ns': None,
        'header_send_at_ns': None})+b'\n'
    interrupted = lambda: stage_writing(b'{', {**TERMINATED, 'exit_code': 137})
    FAULTS = {
        # name: (stage double, patches builder, expectations over authoritative state / lifecycle / accounting / evidence)
        'ledger_short_append': (interrupted(), lambda ctx: ledger_fd_writer(ctx, lambda real, fd, data, n: real(fd, bytes(data[:7]))),
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 1, 'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected'}),
        'ledger_append_failure_after_partial': (interrupted(),
            lambda ctx: ledger_fd_writer(ctx, lambda real, fd, data, n: real(fd, bytes(data[:7])) if n == 1 else (_ for _ in ()).throw(OSError(5, 'synthetic I/O error after a partial append'))),
            {'reservations': 0, 'open': 0, 'consumed': 0, 'terminal': None, 'attempts': 0, 'state': 'not_reserved', 'reconciled': True,
             'allowance': None, 'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'cohort_ledger',
             'events': ['reservation_uncertain']}),
        'reserve_head_failure': (interrupted(), head_failure_at(2),
            {'reservations': 1, 'open': 0, 'consumed': 0, 'terminal': 'release', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 0, 'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'harness_failure',
             'events': ['reservation_uncertain', 'reservation_recovered']}),
        'reservation_receipt_failure': (interrupted(), json_writer_failure('campaign-permit.json'),
            {'reservations': 1, 'open': 0, 'consumed': 0, 'terminal': 'release', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 0, 'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'harness_failure'}),
        'request_reserved_event_failure': (interrupted(), event_failure_once('request_reserved'),
            {'reservations': 1, 'open': 0, 'consumed': 0, 'terminal': 'release', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 0, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'harness_failure'}),
        'stage_interrupted_truncated_http': (interrupted(), None,
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'transport_record_unreadable'}),
        'http_empty_object': (stage_writing(b'{}\n', {**TERMINATED, 'exit_code': 137}), None,
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'transport_record_unreadable', 'read_failure': 'schema'}),
        'http_wrong_types': (stage_writing(valid_http().replace(b'"connection_attempts":0', b'"connection_attempts":"0"'), {**TERMINATED, 'exit_code': 137}), None,
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'transport_record_unreadable', 'read_failure': 'schema'}),
        'process_missing_fields_no_grant': (stage_writing(valid_http(), {'exit_code': 1}, grant=False), None,
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'unknown', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'sealed': True, 'terminal_event': 'episode_rejected', 'read_failure': 'schema'}),
        'reconciliation_receipt_failure': (interrupted(), json_writer_failure('campaign-reconciliation.json'),
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'evidence_complete': False, 'sealed': True, 'terminal_event': 'episode_rejected', 'receipt_absent': True}),
        'reservation_uncertain_event_failure': (interrupted(), event_failure_once('reservation_uncertain', head_failure_at(2)),
            {'reservations': 1, 'open': 0, 'consumed': 0, 'terminal': 'release', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 0, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'harness_failure'}),
        'reservation_recovered_event_failure': (interrupted(), event_failure_once('reservation_recovered', head_failure_at(2)),
            {'reservations': 1, 'open': 0, 'consumed': 0, 'terminal': 'release', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 0, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'harness_failure'}),
        'reservation_reconciled_event_failure': (interrupted(), event_failure_once('reservation_reconciled'),
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 1, 'evidence_complete': False, 'sealed': True, 'terminal_event': 'episode_rejected'}),
        'reconcile_append_failure_after_marker': (interrupted(), append_failure,
            {'reservations': 1, 'open': 1, 'consumed': 0, 'terminal': None, 'attempts': 1, 'reconciled': False, 'allowance': None,
             'evidence_complete': False, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'reconciliation_failure', 'events': ['reconciliation_failed']}),
        'reconcile_head_failure_after_row': (interrupted(), head_failure_at(3),
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected', 'recovered': 'OSError'}),
        'reconcile_recovery_snapshot_failure': (interrupted(), head_failure_at(3, also_snapshot=True),
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'evidence_complete': False, 'sealed': True, 'terminal_event': 'episode_rejected', 'recovered': 'OSError'}),
        'evidence_copy_failure': (interrupted(), copyfile_failure,
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'evidence_complete': False, 'sealed': True, 'terminal_event': 'episode_rejected'}),
    }

    def fault_sweep():
        """Table-driven: for each injected fault, authoritative state, lifecycle state, allowance accounting and evidence completion are checked separately."""
        results = {}
        for name, (stage, patches, expect) in FAULTS.items():
            p = production(stage, patches=patches)
            require(p.raised is None, f'{name}: execute raised {p.raised}')
            observed = {'reservations': sum(1 for r in p.ledger_rows if r['kind'] == 'reservation'), 'open': len(p.state['open_reservations']), 'consumed': p.state['transmissions_consumed'],
                        'terminal': next((r['kind'] for r in p.ledger_rows if r['kind'] in ledger.TERMINAL), None),
                        'attempts': p.accounting['attempts_reserved'], 'state': p.accounting['reservation_state'],
                        'reconciled': p.accounting['ledger_reconciled'], 'allowance': p.accounting['allowance_consumed'],
                        'evidence_complete': p.accounting.get('evidence_complete'), 'sealed': p.sealed,
                        'terminal_event': p.events[-1] if p.events else None, 'category': p.summary['failure_category'],
                        'receipt_absent': p.reconciliation is None, 'events': p.events,
                        'read_failure': (next((f['error'] for f in (p.reconciliation or {}).get('evidence', {}).get('record_read_failures', [])), None)),
                        'recovered': (p.summary['accounting'].get('reconciliation_recovered') if p.summary else None)}
            observed['recovered'] = next((r['payload'].get('recovered') for r in p.rows if r['event'] == 'reservation_reconciled'), None)
            for key, value in expect.items():
                if key == 'events': require(all(e in observed['events'] for e in value), f'{name}: events {value} not all present in {observed["events"]}')
                else: require(observed[key] == value, f'{name}: {key} observed {observed[key]!r}, expected {value!r}')
            require(p.summary['ledger_reconciled'] == p.accounting['ledger_reconciled'] and p.summary['reservation_state'] == p.accounting['reservation_state']
                    and p.summary['evidence_complete'] == p.accounting['evidence_complete'], f'{name}: summary disagrees with accounting')
            if p.accounting['evidence_complete'] and p.accounting['attempts_reserved'] == 1:
                require(p.reconciliation is not None and 'reservation_reconciled' in p.events, f'{name}: evidence_complete without the reconciliation receipt or event')
            require(p.rows[-1]['payload']['evidence_complete'] == p.accounting['evidence_complete'] and p.rows[-1]['payload']['accepted'] is False,
                    f'{name}: terminal payload disagrees')
            results[name] = {k: observed[k] for k in ('reservations', 'open', 'consumed', 'terminal', 'attempts', 'state', 'reconciled', 'allowance', 'evidence_complete', 'sealed', 'terminal_event', 'category')}
        return results
    suite.case('persistence_fault_sweep', fault_sweep)

    def counters():
        source = (r6.ROOT/'cohort_episode.py').read_text()
        for key in ('transmissions_observed', 'transmissions_returned', 'grant_committed', 'send_outcome', 'ledger_outcome', 'allowance_consumed',
                    'transport_record_observed', 'ledger_reconciled', 'evidence_complete', 'reservation_state'):
            require("'"+key+"'" in source)
        require('live_model_cost_usd' not in source and 'live_transmissions_consumed' not in source)
        return {'accounting_fields': 'R6-008 revision 6 shape, unchanged'}
    suite.case('counters_separate', counters)

    def ca_pinned():
        path, described = contract.bundle()
        require(described['sha256'] == c['tls']['public_ca_bundle']['sha256'] and c['tls']['verify_mode'] == 'CERT_REQUIRED')
        return {'bundle': str(path), 'sha256': described['sha256']}
    suite.case('ca_bundle_pinned', ca_pinned)

    def endpoint():
        require(c['endpoint'] == contract.ENDPOINT == {'scheme': 'https', 'host': 'api.openai.com', 'port': 443, 'path': '/v1/responses'})
        return {'endpoint': c['endpoint']}
    suite.case('endpoint_allowlist_exact', endpoint)
    suite.finish()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    units(args.output.resolve())
    print(json.dumps({'passed': True, 'cases': len(CASES)}, indent=1))


if __name__ == '__main__':
    main()

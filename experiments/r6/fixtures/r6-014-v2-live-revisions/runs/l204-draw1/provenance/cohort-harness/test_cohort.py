#!/usr/bin/env python3
"""R6-009 focused controls: the scientific contract, the campaign identity and the task-by-draw ledger. Canned; nothing connects.

The actor runs as a plain subprocess against the loopback TLS fixture with a synthetic canary, so the contract validation of the
envelope, the slot-bound permit and the identical model-input bytes across policy revisions are read from real records. The
R6-008 persistence fault sweep is carried forward against the cohort driver and ledger.

Revision 4 (R6-012) runs the same cases on census sites under contract v2: `D1` is `bracket-l070`, whose prepared problem is
the D1 control's byte for byte, and `C8` is `bracket-l204`. Added: gate v4 derived from gate v3 by exactly its listed
substitutions; the site sender stage and site final validation each one line from the frozen function; contract v2 equal to
contract v1 outside its request; the posable set confirmed through the gate; policy C requests for every site; the narrow
pricing review; and the driver's refusals before any reservation for an SDK-refused and an ambiguous site.
Revision 6 (R6-013): the driver's consumption receipt and its diagnosed reconstruction refusal, each accepted only on bound evidence and
refused for a removed or forged receipt, a wrong closer or certificate, and any other failure of the reconstruction stage. The
evidence is the retained v5 records with a closer selection written in, rechained; the native paths run in the rehearsals.
Revision 7 (R6-014): the signing lifecycle, each case on an isolated policy, lock, checkpoint and ledgers frozen into a temporary directory by
the production `freeze`: the first block's binding and checkpoint; refusals outside the plan and for stale or future pricing or approval;
interruption at each persistence boundary and its resumption; repeated, conflicting and rolled-back signing; a later block that needs a new,
later authority while consumed slots persist and request bytes stay fixed; and a pricing revision under the same authority.
Revision 8 (R6-014 review, finding 1): the live activation completes only with a durable receipt kept beside the policy. After a slot is
consumed, removing the established live ledger (whole, its files, or its head) refuses re-signing, authorization and revision, and no
activation made without the receipt can reserve; the interrupted first activation, including between its row and its receipt, still resumes.
"""
import argparse
import copy
import difflib
import inspect
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
import pricing_gate_v4 as gate
import pricing_gate_v3 as gate_v3
import site_network
import site_request
import site_stage
import site_task
import campaign_network
import run as r6
from test_proposals import Suite, rejected, require
from unittest.mock import patch

CASES = '''policy_frozen_disabled contract_frozen_canonical_and_bound request_carries_contract_not_policy envelope_identical_across_revisions
slot_identity_absent_from_model_bytes policy_conflicts_with_contract_rejected host_admission_recomputes_envelope actor_validates_envelope_against_contract
request_task_joined_to_funded_slot request_grammar_enforced_at_admission generation_option_types_exact slot_hierarchy_durable slot_ancestry_durable_after_interrupted_creation
actor_permit_bound_to_slot actor_live_rejects_unsigned_policy campaign_identity_survives_revision unregistered_revision_refused
revision_registration_rules distinct_campaigns_share_contract slot_rules activation_bound_to_policy_and_mode
actor_grant_before_first_header_byte actor_commitment_recorded actor_credential_format_classified persistence_fault_sweep
counters_separate ca_bundle_pinned endpoint_allowlist_exact gate_v4_is_gate_v3_with_listed_substitutions site_driver_stages_one_line_each
contract_v2_differs_from_v1_only_in_request posable_set_confirmed_through_gate policy_c_requests_for_sites pricing_review_is_narrow
driver_refuses_unposable_sites_before_reservation runtime_pin_divergence_recorded consumption_receipt_required
reconstruction_refusal_requires_bound_evidence signing_binds_block_and_preserves_checkpoint signing_refuses_outside_plan_and_bad_pricing
signing_interrupted_at_each_boundary_resumes signing_repeated_conflicting_or_rolled_back later_block_requires_new_authority
pricing_revision_keeps_authority lost_authority_fails_closed live_reservation_requires_activation_receipt'''.split()
REPRESENTABILITY = r6.ROOT/'census-runs/representability-v4'
UNREPAIRED = r6.ROOT/'census-runs/representability-v2'
PREPARED = REPRESENTABILITY/'bracket-l070/prepared.json'
TERMINATED = {'exit_code': 1, 'workload_empty_after_cleanup': True, 'monitor_error': None, 'observation_error': None, 'accounting_scope': 'sandbox_process_tree'}
SENT = {'body_sends_started': 1, 'header_sends_started': 1, 'send_outcome': 'returned'}
UNSENT = {'body_sends_started': 0, 'header_sends_started': 0}
D1, C8 = 'bracket-l070', 'bracket-l204'  # l070's prepared problem is the D1 control's; l204 is a second family


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
    if not live: book = ledger.Ledger(directory, policy['campaign']['id']); book.activate(policy, live); return book
    directory = Path(directory)/'live'  # revision 8: a live ledger activates with its receipt, kept outside its directory
    book = ledger.Ledger(directory, policy['campaign']['id'], directory.with_name('live.activation.json')); book.ensure_activated(policy, True); return book


def bind(): return {'request_sha256': 'b'*64, 'arguments_sha256': 'c'*64, 'contract_sha256': contract.contract_sha256()}
def reservation_shape(): return {'reserved_micro_usd': 102400, 'message_utf8_bytes': 5000}
def reserve(book, policy, task, draw, episode='run'): return book.reserve(episode, policy, task, draw, reservation_shape(), bind(), {'accepted': True})[0]
def with_grant(book, permit):
    ledger.commit_grant(book.grant_slot(permit), ledger.grant_record(permit, 1)); return book.grant_slot(permit)

from pathlib import Path


def units(output):
    suite = Suite(output, CASES)
    c = contract.config(); contract_value = contract.contract(); task = site_task.get(D1); prepared = r6.read_json(PREPARED)

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
        require(contract_value['request_schema']['sha256'] == r6.sha(r6.ROOT/contract.REQUEST_SCHEMA_PATH))
        return {'contract_sha256': contract.contract_sha256(), 'instruction_bytes': contract_value['instruction']['bytes'], 'omitted_options': len(contract_value['generation']['omitted'])}
    suite.case('contract_frozen_canonical_and_bound', contract_frozen)

    def request_binding():
        request = budget.request(task, prepared)[0]; value = json.loads(request)
        require('policy_sha256' not in value and value['contract_sha256'] == contract.contract_sha256() and value['schema_version'] == gate.REQUEST_SCHEMA)
        require(set(value['binding']) >= {'task_id', 'manifest_sha256', 'challenge_sha256', 'input_ir_sha256', 'final_ir_sha256', 'prompt_sha256'})
        require(contract.policy_sha256()[:8] not in request.decode() and c['campaign']['id'] not in request.decode())
        return {'request_keys': sorted(value), 'binding_keys': sorted(value['binding'])}
    suite.case('request_carries_contract_not_policy', request_binding)

    sources = r6.ROOT/c['pricing_sources']

    def identical_envelopes():
        request = budget.request(task, prepared)[0]; arguments = budget.arguments(request); body = v2.entity_body(arguments)
        other = revised(signed(c, approved_utc='2026-09-15T00:00:00Z'))
        with patch.object(contract, 'config', lambda: other):
            require(budget.request(task, prepared)[0] == request and budget.arguments(request) == arguments and v2.entity_body(budget.arguments(request)) == body)
        a1 = gate.admission(c, contract_value, contract.PROMPT.read_text(), sources, arguments, request, time.time())
        require(a1['contract_sha256'] == contract.contract_sha256() and a1['body_sha256'] == v2.sha(body))
        return {'entity_body_sha256': v2.sha(body), 'identical_under_revised_policy': True}
    suite.case('envelope_identical_across_revisions', identical_envelopes)

    def slot_absent():
        request = budget.request(task, prepared)[0]; arguments = budget.arguments(request); text = v2.entity_body(arguments).decode()
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
        request = budget.request(task, prepared)[0]; arguments = budget.arguments(request); instruction = contract.PROMPT.read_text(); now = time.time()
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

    def actor_run(directory, *, credential_text=None, mode='rehearsal', policy=None, book=None, permit=None, arguments_mutation=None, request_mutation=None,
                  task_id=D1, draw=1, actor_task=None, actor_draw=None, funded_task=None):
        d = Path(directory); run = d/'run'; run.mkdir(exist_ok=True)
        policy_value = policy or c; policy_path = d/'policy.json'; policy_path.write_bytes(v2.canonical(policy_value)+b'\n')
        request = budget.request(task, prepared)[0]
        if request_mutation: request = request_mutation(request)
        arguments = budget.arguments(request)
        if arguments_mutation: arguments = arguments_mutation(copy.deepcopy(arguments))
        (d/'request.json').write_bytes(request); r6.write_json(d/'arguments.json', arguments)
        if book is None:
            admitted = gate.admission(policy_value, contract_value, contract.PROMPT.read_text(), sources, budget.arguments(request), request, time.time()) if not (arguments_mutation or request_mutation) else {'accepted': True, 'evaluated_at_unix': time.time()}
            book = temp_book(d/'ledger', policy_value, mode == 'live' and policy_value.get('live_enabled') is True)
            identity = budget.task_identity(funded_task or task_id)
            permit, _ = book.reserve('probe', policy_value, funded_task or task_id, draw, budget.reservation(arguments), {'request_sha256': gate.sha(request), 'arguments_sha256': gate.sha(gate.canonical(budget.arguments(request))), 'contract_sha256': contract.contract_sha256(), **identity}, admitted)
        r6.write_json(d/'permit.json', permit)
        out = d/'out'; out.mkdir(exist_ok=True); grant = book.grant_slot(permit)
        nonce = credential.nonce(); canary = credential.derive(nonce)
        cred = d/'credential'; cred.write_text(credential.header(canary)+'\n' if credential_text is None else credential_text)
        base_args = ['--mode', mode, '--policy', str(policy_path), '--contract', str(contract.CONTRACT), '--instruction', str(contract.PROMPT), '--arguments', str(d/'arguments.json'),
                     '--credential-file', str(cred), '--out', str(out), '--sources', str(sources), '--permit', str(d/'permit.json'), '--ledger', str(book.path),
                     '--request', str(d/'request.json'), '--episode', 'probe', '--task', actor_task or funded_task or task_id, '--draw', str(actor_draw or draw), '--grant', str(grant), '--commitment-nonce', nonce]
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

    def task_join():
        c8 = site_task.get(C8); c8_prepared = r6.read_json(REPRESENTABILITY/C8/'prepared.json')
        request = budget.request(task, prepared)[0]; arguments = budget.arguments(request); identity_d1 = budget.task_identity(D1); identity_c8 = budget.task_identity(C8)
        # host: an authentic D1 request may not fund C8, in either direction of the identity
        gate_refused(lambda: gate.check_task_join(gate.strict(request), C8, identity_c8['task_manifest_sha256'], identity_c8['challenge_sha256']), 'cohort_request_task_mismatch')
        gate_refused(lambda: gate.check_task_join(gate.strict(request), D1, identity_c8['task_manifest_sha256'], identity_d1['challenge_sha256']), 'cohort_request_task_identity')
        require(gate.check_task_join(gate.strict(request), D1, identity_d1['task_manifest_sha256'], identity_d1['challenge_sha256']) is None)
        with tempfile.TemporaryDirectory() as d:  # production host reservation refuses the crossing
            book = temp_book(d, c, False)
            with patch.object(contract, 'campaign_ledger', lambda live, cfg=None: book):
                gate_refused(lambda: budget.reserve('probe', C8, 1, arguments, request, sources, False), 'cohort_request_task_mismatch')
                row, _, _ = budget.reserve('probe', D1, 1, arguments, request, sources, False)
                require(row['task_id'] == D1 and row['task_manifest_sha256'] == identity_d1['task_manifest_sha256'])
        with tempfile.TemporaryDirectory() as d:  # the actor: a D1 request under a C8-funded permit does not send
            r = actor_run(d, funded_task=C8)
            require(r.http['failure_category'] == 'contract_admission' and r.http['pricing_failure_code'] == 'cohort_request_task_mismatch' and r.http['connection_attempts'] == 0
                    and r.http['grant_committed'] is False and r.http['credential_commitment_sha256'] is None)
        outcome = {'host_d1_request_c8_slot': 'cohort_request_task_mismatch', 'host_identity_mismatch': 'cohort_request_task_identity', 'actor_d1_request_c8_permit': 'cohort_request_task_mismatch, no credential read, no connection'}
        if c8_prepared is not None:
            c8_request = budget.request(c8, c8_prepared)[0]
            gate_refused(lambda: gate.check_task_join(gate.strict(c8_request), D1, identity_d1['task_manifest_sha256'], identity_d1['challenge_sha256']), 'cohort_request_task_mismatch')
            outcome['host_c8_request_d1_slot'] = 'cohort_request_task_mismatch'
        return outcome
    suite.case('request_task_joined_to_funded_slot', task_join)

    def grammar():
        request = budget.request(task, prepared)[0]; value = json.loads(request); instruction = contract.PROMPT.read_text(); now = time.time()
        def mutated(fn):
            v = copy.deepcopy(value); fn(v); return events.canonical(v)+b'\n'
        cases = {'policy_digest_injected': (lambda v: v.__setitem__('policy_sha256', 'f'*64), 'contract_request_keys'),
                 'binding_task_deleted': (lambda v: v['binding'].pop('task_id'), 'contract_request_binding_keys'),
                 'extra_binding_key': (lambda v: v['binding'].__setitem__('note', 'x'), 'contract_request_binding_keys'),
                 'unknown_task': (lambda v: v['binding'].__setitem__('task_id', 'other'), 'contract_request_task'),
                 'bad_digest_form': (lambda v: v['binding'].__setitem__('manifest_sha256', 'zz'), 'contract_request_binding_form'),
                 'empty_rows': (lambda v: v['problem'].__setitem__('rows', []), 'contract_request_rows_empty'),
                 'row_extra_key': (lambda v: v['problem']['rows'][0].__setitem__('x', 1), 'contract_request_row_keys'),
                 'constant_leading_zero': (lambda v: v['problem']['rows'][0].__setitem__('constant', '01'), 'contract_request_constant_grammar'),
                 'coefficient_float': (lambda v: v['problem']['rows'][0]['terms'][0].__setitem__('coefficient', '1.0'), 'contract_request_term_grammar'),
                 'duplicate_row': (lambda v: v['problem']['rows'].append(dict(v['problem']['rows'][0])), 'contract_request_duplicate_row'),
                 'fragment_changed': (lambda v: v['problem'].__setitem__('fragment', 'LRA'), 'contract_request_problem_keys'),
                 'neg_goal_not_last': (lambda v: v['problem']['rows'].insert(0, v['problem']['rows'].pop()), 'contract_request_neg_goal'),
                 'neg_goal_missing': (lambda v: v['problem']['rows'][-1].__setitem__('name', 'goal'), 'contract_request_neg_goal')}
        host = {}; stricter = {'duplicate_row', 'neg_goal_not_last', 'neg_goal_missing'}  # the validator's own rule beyond the frozen schema; recorded, not claimed as schema parity
        for label, (fn, code) in cases.items():
            bad = mutated(fn); a = gate.render_arguments(contract_value, instruction, bad)
            host[label] = gate_refused(lambda: gate.admission(c, contract_value, instruction, sources, a, bad, now), code)['code']
            if label in stricter: continue
            try: r6.jsonschema.validate(json.loads(bad), r6.read_json(r6.ROOT/contract.REQUEST_SCHEMA_PATH)); raise AssertionError('schema accepts '+label)
            except r6.jsonschema.ValidationError: pass  # parity: the frozen schema rejects every case the validator rejects
        r6.jsonschema.validate(value, r6.read_json(r6.ROOT/contract.REQUEST_SCHEMA_PATH))
        with tempfile.TemporaryDirectory() as d:  # the actor, on an injected policy digest rendered consistently
            r = actor_run(d, request_mutation=lambda rq: mutated(lambda v: v.__setitem__('policy_sha256', 'f'*64)))
            require(r.http['failure_category'] == 'contract_admission' and r.http['pricing_failure_code'] == 'contract_request_keys' and r.http['connection_attempts'] == 0)
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d, request_mutation=lambda rq: mutated(lambda v: v['binding'].pop('task_id')))
            require(r.http['failure_category'] == 'contract_admission' and r.http['pricing_failure_code'] == 'contract_request_binding_keys' and r.http['connection_attempts'] == 0)
        return {'host': host, 'actor': {'policy_digest_injected': 'contract_request_keys', 'binding_task_deleted': 'contract_request_binding_keys'}, 'schema_parity': len(cases)-len(stricter), 'validator_only': sorted(stricter)}
    suite.case('request_grammar_enforced_at_admission', grammar)

    def option_types():
        request = budget.request(task, prepared)[0]; arguments = budget.arguments(request); instruction = contract.PROMPT.read_text(); now = time.time()
        host = {}
        for label, key, value, code in (('float_for_int', 'max_output_tokens', 4096.0, 'contract_generation_max_output_tokens'), ('int_for_bool', 'store', 0, 'contract_generation_store'),
                                        ('bool_for_int', 'max_output_tokens', True, 'contract_generation_max_output_tokens')):
            a = copy.deepcopy(arguments); a[key] = value
            host[label] = gate_refused(lambda: gate.admission(c, contract_value, instruction, sources, a, request, now), code)['code']
        bad = copy.deepcopy(c); bad['request'] = {**bad['request'], 'max_output_tokens': 4096.0}
        gate_refused(lambda: gate.check_policy(bad, contract_value), 'policy_generation_conflict')
        bad = copy.deepcopy(c); bad['request'] = {**bad['request'], 'store': 0}
        gate_refused(lambda: gate.check_policy(bad, contract_value), 'policy_generation_conflict')
        require(gate.same_json({'a': [1, {'b': False}]}, {'a': [1, {'b': False}]}) and not gate.same_json(1, 1.0) and not gate.same_json(False, 0) and not gate.same_json({'a': 1}, {'a': 1, 'b': 2}))
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d, arguments_mutation=lambda a: (a.__setitem__('max_output_tokens', 4096.0), a)[1])
            require(r.http['failure_category'] == 'contract_admission' and r.http['pricing_failure_code'] == 'contract_generation_max_output_tokens' and r.http['connection_attempts'] == 0)
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d, arguments_mutation=lambda a: (a.__setitem__('store', 0), a)[1])
            require(r.http['failure_category'] == 'contract_admission' and r.http['pricing_failure_code'] == 'contract_generation_store' and r.http['connection_attempts'] == 0)
        return {'host': host, 'policy': ['float_for_int', 'int_for_bool'], 'actor': ['float_for_int', 'int_for_bool']}
    suite.case('generation_option_types_exact', option_types)

    def durability():
        calls = []; original = base_ledger.fsync_directory; observe = lambda path: (calls.append(str(Path(path).resolve())), original(path))[1]
        with tempfile.TemporaryDirectory() as d, patch.object(ledger, 'fsync_directory', observe), patch.object(base_ledger, 'fsync_directory', observe):
            live_policy = signed(c, schedule={D1: 2, C8: 1}, maximum_micro_usd=3*102400); book = temp_book(d, live_policy, True)
            slots = str(book.slots.resolve()); root = str(book.directory.resolve()); calls.clear()
            def ancestry(permit, task, draw):  # the whole authority ancestry, deepest first, each parent after its child, before the row
                chain = [slots+'/'+task+'/'+str(draw)+'/'+permit['reservation_id'], slots+'/'+task+'/'+str(draw), slots+'/'+task, slots, root]
                require(all(x in calls for x in chain), 'ancestry not synced: '+str(calls))
                require([calls.index(x) for x in chain] == sorted(calls.index(x) for x in chain), 'child before parent')
            p1 = reserve(book, live_policy, D1, 1); ancestry(p1, D1, 1)  # first task, first draw: every component new
            with_grant(book, p1); book.reconcile(p1, TERMINATED, SENT, {})
            calls.clear(); p2 = reserve(book, live_policy, D1, 2); ancestry(p2, D1, 2)  # new draw under an existing task: the existing task and slots links are synced again
            calls.clear(); with_grant(book, p2); require(any(x.endswith(p2['reservation_id']) for x in calls), 'grant slot not fsynced')
        return {'first_task_first_draw': 'attempt, draw, task, slots, ledger directory - child before parent', 'new_draw_existing_task': 'the same ancestry, existing links included'}
    suite.case('slot_hierarchy_durable', durability)

    def interrupted_creation():
        """An attempt that created directories and failed before syncing their ancestors leaves them behind; the retry must sync the whole ancestry again."""
        results = {}
        for where in ('task', 'slots'):
            with tempfile.TemporaryDirectory() as d:
                live_policy = signed(c, schedule={D1: 2, C8: 1}, maximum_micro_usd=3*102400); book = temp_book(d, live_policy, True)
                slots = book.slots.resolve(); task_dir = slots/D1; draw_dir = task_dir/'1'; root = book.directory.resolve()
                require(not task_dir.exists() and not draw_dir.exists(), 'fresh hierarchy')
                original = base_ledger.fsync_directory; completed = []; failed = []
                def sync(path):
                    path = Path(path).resolve()
                    if ((where == 'task' and path == task_dir) or (where == 'slots' and path == slots)) and not failed:
                        failed.append(str(path)); raise OSError(5, 'injected directory fsync failure')
                    original(path); completed.append(str(path))
                with patch.object(ledger, 'fsync_directory', sync), patch.object(base_ledger, 'fsync_directory', sync):
                    try: reserve(book, live_policy, D1, 1, 'interrupted')
                    except OSError as error: require('injected' in str(error), 'wrong failure: '+str(error))
                    else: raise AssertionError('the injected fsync failure did not stop the reservation')
                    require(len(failed) == 1 and len(ledger.parse(book.path.read_bytes())) == 1 and task_dir.exists() and draw_dir.exists(),
                            'the interrupted attempt must leave directories and no row')
                    completed.clear(); permit = reserve(book, live_policy, D1, 1, 'retry')
                chain = [str(draw_dir/permit['reservation_id']), str(draw_dir), str(task_dir), str(slots), str(root)]
                require(all(x in completed for x in chain), 'retry did not sync the whole ancestry: '+str(completed))
                require([completed.index(x) for x in chain] == sorted(completed.index(x) for x in chain), 'child before parent on retry')
                require(len(ledger.parse(book.path.read_bytes())) == 2 and permit['reserved_micro_usd'] == 102400, 'retry reserved')
                results[where] = {'first_attempt_failed_at': failed[0].split('/')[-1], 'rows_after_failure': 1, 'retry_synced': [x.split('/')[-1] for x in chain]}
        return results
    suite.case('slot_ancestry_durable_after_interrupted_creation', interrupted_creation)

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
            tools = {'expected': site_task.frozen_site(task)[1], 'runtime': {'stdlib': '/probe', 'extension_binaries': []}, 'runtime_path': d, 'python': Path(sys.executable)}
            def prepare_double(run, task, tools):
                request = budget.request(task, prepared)[0]
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

    def gate_derivation():
        v3 = (r6.ROOT/'pricing_gate_v3.py').read_text(); v4 = (r6.ROOT/'pricing_gate_v4.py').read_text()
        diff = [l for l in difflib.unified_diff(v3.splitlines(), v4.splitlines(), lineterm='', n=0) if l[:1] in '+-' and not l.startswith(('+++', '---'))]
        expected = ['-"""R6-009 admission: the scientific contract, then pricing. Standard library only.',
                    "-REQUEST_SCHEMA = 'r6-farkas-request-9'", "-TASKS = ('verinf-d1-70', 'c1-c8-2p18')",
                    '+"""R6-012 admission, gate v4: gate v3 with the census sites as tasks and exactly one final neg_goal row. Standard library only.', '+',
                    "+Every other line is gate v3's; `test_cohort.py` pins the difference to the substitutions listed in `gen_v4`.",
                    "+REQUEST_SCHEMA = 'r6-farkas-request-10'", '+TASKS = '+repr(tuple(site_task.primary())),
                    "+    require(names.count('neg_goal') == 1 and names[-1] == 'neg_goal', 'contract_request_neg_goal')"]
        require(sorted(diff) == sorted(expected), str(diff))
        require(gate.TASKS == site_task.primary() and r6.read_json(r6.ROOT/contract.REQUEST_SCHEMA_PATH)['properties']['binding']['properties']['task_id']['enum'] == list(site_task.primary()))
        old_schema = r6.read_json(r6.ROOT/'schema/cohort-request.schema.json'); new_schema = r6.read_json(r6.ROOT/contract.REQUEST_SCHEMA_PATH)
        old_schema['properties']['binding']['properties']['task_id'] = new_schema['properties']['binding']['properties']['task_id']
        old_schema['properties']['schema_version'] = new_schema['properties']['schema_version']
        require(old_schema == new_schema, 'the schema changed beyond its version and task enumeration')
        return {'changed_lines': len(diff), 'tasks': len(gate.TASKS)}
    suite.case('gate_v4_is_gate_v3_with_listed_substitutions', gate_derivation)

    def site_driver_stages():
        def delta(a, b):
            return [l for l in difflib.unified_diff(inspect.getsource(a).splitlines(), inspect.getsource(b).splitlines(), lineterm='', n=0)
                    if l[:1] in '+-' and not l.startswith(('+++', '---'))]
        require(delta(campaign_network.stage, site_network.stage) == ["-             sys.executable, str(r6.ROOT/'supervise.py'), str(records/'command.json')]",
                                                                      "+             sys.executable, str(r6.ROOT/'site_supervise.py'), str(records/'command.json')]"])
        require(delta(episode.final_validation, site_network.final_validation) == ["-        out = stage(run, 'validation-'+name, checker,",
                                                                                   "+        out = site_stage.stage(run, 'validation-'+name, checker,"])
        require(delta(driver.publication_driver.seal, site_network.seal) == ['-    rows = episode.observations(run)', '+    rows = observations(run)'])
        require(site_network.command is campaign_network.command and site_network.local_policy is episode.local_policy and site_network.contract is driver.publication_driver.contract)
        schema = r6.read_json(r6.ROOT/'schema/event.schema.json'); rows = events.read(REPRESENTABILITY/'bracket-l070/events.ndjson')
        require(rows and all(r['task_id'] == 'bracket-l070' for r in rows) and site_network.observations(REPRESENTABILITY/'bracket-l070') == rows)
        wrong = dict(rows[0]); wrong['task_id'] = 'bracket-l999'
        with patch.object(events, 'read', lambda path: [wrong]): rejected(lambda: site_network.observations(REPRESENTABILITY/'bracket-l070'), 'bracket-l999')
        source = (r6.ROOT/'cohort_episode.py').read_text()
        require('episode.stage(' not in source and 'episode.final_validation(' not in source and 'consumer.downstream' not in source
                and 'publication_driver.seal(' not in source, 'a frozen stage or seal is still called directly')
        return {'sender_stage': 'one line', 'final_validation': 'one line', 'seal': 'one line; event schema widened to the reviewed sites only', 'driver_calls': 'site stages only'}
    suite.case('site_driver_stages_one_line_each', site_driver_stages)

    def contract_v2():
        v1 = r6.read_json(contract.PREVIOUS_CONTRACT); v2c = contract_value
        require({k: v for k, v in v1.items() if k not in ('name', 'request_schema')} == {k: v for k, v in v2c.items() if k not in ('name', 'request_schema')},
                'contract v2 differs from v1 outside the request')
        require(v1['name'] == 'farkas_proposal_contract_v1' and v2c['name'] == 'farkas_proposal_contract_v2')
        changed = sorted(k for k in set(v1['request_schema']) | set(v2c['request_schema']) if v1['request_schema'].get(k) != v2c['request_schema'].get(k))
        require(changed == ['admission_policy', 'path', 'schema_version', 'sha256', 'tasks'], str(changed))
        require(c['supersedes']['contract_sha256'] == r6.sha(contract.PREVIOUS_CONTRACT) and v2c['instruction'] == v1['instruction'])
        return {'unchanged': sorted(k for k in v1 if k not in ('name', 'request_schema')), 'request_schema_changed': changed}
    suite.case('contract_v2_differs_from_v1_only_in_request', contract_v2)

    def posable():
        confirmation = c['posable_confirmation']; classes = r6.read_json(REPRESENTABILITY/'representability.json')['classes']
        require(confirmation == contract.confirm_posable() and confirmation['denominator'] == 15)
        derived = sorted(classes['posable_certificate'] + classes['posable_negative_control'])  # derived again, never carried over from R6-011
        require(sorted(s for s, o in confirmation['outcome'].items() if o['posable']) == derived == sorted(contract.POSABLE))
        require(sorted(s for s, o in confirmation['outcome'].items() if o['code'] == 'interface_refused') == sorted(classes['interface_refused']))
        require(c['campaign']['schedule'] == {s: contract.DRAWS for s in contract.POSABLE} and c['limits']['total_micro_usd'] == contract.ATTEMPT_MICRO_USD*8*len(contract.POSABLE))
        return {'posable': len(contract.POSABLE), 'refused': {s: o['code'] for s, o in confirmation['outcome'].items() if not o['posable']}}
    suite.case('posable_set_confirmed_through_gate', posable)

    def site_requests():
        built = {}
        for site_id in contract.POSABLE:
            t = site_task.get(site_id); p = r6.read_json(REPRESENTABILITY/site_id/'prepared.json')
            request, evidence = budget.request(t, p); value = json.loads(request)
            gate.check_request_grammar(value); r6.jsonschema.validate(value, r6.read_json(r6.ROOT/contract.REQUEST_SCHEMA_PATH))
            require(value['binding']['task_id'] == site_id and value['problem']['fragment'] == 'LIA' and value['problem']['rows'] == p['rows'])
            require(evidence['omitted_names'] == p['farkas_omissions'] and not any('"'+n+'"' in request.decode() for n in evidence['omitted_names']), site_id)
            require(value['binding']['manifest_sha256'] == r6.sha(t.path/'manifest.json') and value['binding']['challenge_sha256'] == site_task.frozen_site(t)[1]['challenge_sha256'])
            built[site_id] = {'rows': len(value['problem']['rows']), 'source_fragment': evidence['source_fragment'], 'omitted': evidence['omitted_names']}
        # l178 as prepared before the repair carries two `this` rows and stays refused; as repaired, its rows are uniquely named
        rejected(lambda: budget.request(site_task.get('bracket-l178'), r6.read_json(UNREPAIRED/'bracket-l178/prepared.json')), 'policy_ambiguous_reference')
        names = [r['name'] for r in r6.read_json(REPRESENTABILITY/'bracket-l178/prepared.json')['rows']]
        require('bracket-l178' in built and len(names) == len(set(names)), 'repaired l178 admitted with unique row names')
        return built
    suite.case('policy_c_requests_for_sites', site_requests)

    def pricing_review():
        review = c['pricing_admission']['source_review']
        require(review['differing_extract_fields'] == {'model': ['snapshot_section'], 'caching': []} and review['semantic_fields_identical'] and review['rates_identical_to_previous'])
        refusals = {}
        for label, change in (('listed_ids', lambda v: v['listed_ids'].append('gpt-5.4-other')), ('price', lambda v: v.__setitem__('output', '16.00')),
                              ('pricing_section', lambda v: v.__setitem__('pricing_section', v['pricing_section']+' changed')),
                              ('unreviewed_snapshot_prose', lambda v: v.__setitem__('snapshot_section', v['snapshot_section'].replace('consistent', 'mostly consistent'))),
                              ('whitespace_elsewhere_in_snapshot', lambda v: v.__setitem__('snapshot_section', v['snapshot_section'].replace('a list', 'a  list')))):
            with tempfile.TemporaryDirectory(dir=r6.ROOT/'sources') as d:  # inside the repository, so only the semantic review can refuse
                copy_dir = Path(d)/'capture'; shutil.copytree(r6.ROOT/c['pricing_sources'], copy_dir)
                v = r6.read_json(copy_dir/'model.extract.json'); change(v); (copy_dir/'model.extract.json').write_text(json.dumps(v))
                real = contract.v2.source_evidence(r6.ROOT/c['pricing_sources'])  # the raw pages are unchanged; only the extract under review differs
                with patch.object(contract.v2, 'source_evidence', lambda directory: real):
                    require(contract.pinned_admission(r6.ROOT/c['pricing_sources'])['source_review']['semantic_fields_identical'])
                    try: contract.pinned_admission(copy_dir)
                    except ValueError as error:
                        require('differs semantically' in str(error), label+': '+str(error)); refusals[label] = 'differs semantically'; continue
                raise AssertionError(label+' was accepted')
        return {'recorded': review['differing_extract_fields'], 'refused': refusals}
    suite.case('pricing_review_is_narrow', pricing_review)

    def unposable():
        outcomes = {}
        for site_id, category, stage, source in (('bracket-l178', 'policy_refused', 'request_admission', UNREPAIRED), ('bracket-l098', 'interface_refused', 'preparation', REPRESENTABILITY)):
            with tempfile.TemporaryDirectory() as d:
                d = Path(d); run = d/'run'; run.mkdir(); t = site_task.get(site_id)
                book = ledger.Ledger(d/'ledgers'/c['campaign']['id']/'rehearsal', c['campaign']['id']); book.activate(c, False)
                tools = {'expected': site_task.frozen_site(t)[1], 'runtime': {'stdlib': '/probe', 'extension_binaries': []}, 'runtime_path': d, 'python': Path(sys.executable)}
                retained = source/site_id  # l178 as emitted before the repair still carries two `this` rows
                def prepare_from_retained(run, task, tools):
                    if not (retained/'prepared.json').exists():  # the SDK refused this site in the retained classification run: replay that refusal
                        stage = run/'stages/pipeline-prepare'; stage.mkdir(parents=True)
                        shutil.copyfile(retained/'stages/pipeline-prepare/pipeline-prepare.stderr', stage/'pipeline-prepare.stderr')
                        raise episode.StageFailure('pipeline-prepare', 'stage_rejected', 'retained SDK refusal')
                    return driver.budget.request(task, r6.read_json(retained/'prepared.json'))
                with patch.object(contract, 'campaign_ledger', lambda live, cfg=None: book), patch.object(driver, 'setup', lambda *a: tools), \
                     patch.object(driver, 'prepare', prepare_from_retained):
                    result = driver.execute(run, t, 1, 'rehearsal', d, None)
                summary = r6.read_json(run/'credential-summary.json'); _, s = book.snapshot()
                require(result['failure_category'] == category and summary['failure_phase'] == stage and s['rows'] == 1 and s['open_reservations'] == []
                        and not (run/'campaign-permit.json').exists() and (run/'seal.json').exists(), f'{site_id}: {result["failure_category"]}')
                outcomes[site_id] = {'category': category, 'ledger_rows': s['rows'], 'sealed': True}
        return outcomes
    suite.case('driver_refuses_unposable_sites_before_reservation', unposable)

    def runtime_boundary():
        divergence = c['runtime_divergence']; record = contract.runtime_record()
        require(c['runtime_lock_sha256'] == r6.sha(contract.RUNTIME) and divergence == contract.runtime_divergence())
        require(divergence['python_unchanged'] and divergence['stdlib_unchanged'] and divergence['extensions_unchanged']
                and not divergence['libraries_added'] and not divergence['libraries_removed'], str(divergence))
        require(divergence['previous_runtime_sha256'] == r6.sha(contract.PREVIOUS_RUNTIME) == r6.read_json(r6.ROOT/'policies/responses-campaign-v7.json')['runtime_lock_sha256'])
        require(sorted(divergence['libraries_changed']) == ['/usr/lib/libexpat.so.1', '/usr/lib/libreadline.so.8'], str(divergence['libraries_changed']))
        with patch.object(r6, 'sha', lambda path: '0'*64 if str(path).endswith('libreadline.so.8.3') else r6.hashlib.sha256(r6.Path(path).read_bytes()).hexdigest()):
            rejected(lambda: contract.runtime_record(), 'Python library changed')
        return {'changed': divergence['libraries_changed'], 'python': 'unchanged', 'stdlib': 'unchanged', 'host_drift': 'rejected'}
    suite.case('runtime_pin_divergence_recorded', runtime_boundary)
    V5 = r6.ROOT/'cohort-runs-v5'

    def rechain(rows):
        previous = '0'*64
        for i, row in enumerate(rows):
            row.update(sequence=i, previous_hash=previous); row.pop('event_hash', None); row['event_hash'] = events.digest(row); previous = row['event_hash']
        return b''.join(events.canonical(r)+b'\n' for r in rows)

    def staged(source, change):
        """A temporary run: the retained v5 events (with `change` applied, rechained), reconstruction records and packet."""
        temp = Path(tempfile.mkdtemp(prefix='r6-013-receipt-')); run = temp/'run'; (run/'stages').mkdir(parents=True)
        shutil.copytree(source/'stages/reconstruct', run/'stages/reconstruct'); shutil.copyfile(source/'evidence.json', run/'evidence.json')
        rows = events.read(source/'events.ndjson'); change(run, rows); (run/'events.ndjson').write_bytes(rechain(rows))
        return run

    def child(rows, event, data, after):
        index = max(i for i, r in enumerate(rows) if r['source'] == 'child_report' and r['event'] == after)
        template = copy.deepcopy(rows[index]); template['event'] = event; template['payload'] = {**template['payload'], 'data': data}
        rows.insert(index+1, template)

    def select(closer, comparison='ℕ', certificate=None):
        def change(run, rows):
            packet = r6.read_json(run/'evidence.json')
            child(rows, 'closer_selected', {'certificate': certificate or packet['certificate'], 'closer': closer, 'goal': 'g', 'comparison_type': comparison}, 'reconstruction_started')
        return change

    def receipt():
        source = V5/'l069-draw1'; packet = r6.read_json(source/'evidence.json'); outcomes = {}
        def attempt(label, change, ok):
            run = staged(source, change)
            try: value = driver.consumption_receipt(run, packet); accepted = True
            except driver.wire.Failure as error: accepted = False; require(error.category == 'consumption_unobserved', label)
            finally: shutil.rmtree(run.parent)
            require(accepted is ok, label); outcomes[label] = accepted
        attempt('selected_then_finished', select('term_mode_nat'), True)
        attempt('v5_record_without_selection', lambda run, rows: None, False)
        def removed(run, rows):
            select('term_mode_nat')(run, rows); rows[:] = [r for r in rows if r['event'] != 'reconstruction_finished']
        attempt('receipt_removed', removed, False)
        def forged(run, rows):
            select('term_mode_nat')(run, rows)
            r = next(r for r in rows if r['event'] == 'reconstruction_finished'); r['payload']['data']['certificate'] = {'forged': True}
        attempt('receipt_certificate_forged', forged, False)
        attempt('selection_names_another_certificate', select('term_mode_nat', certificate={'other': True}), False)
        attempt('selection_names_another_closer', select('term_mode_int'), False)
        def unconsumed(run, rows):
            select('term_mode_nat')(run, rows)
            next(r for r in rows if r['event'] == 'reconstruction_finished')['payload']['data']['certificate_consumed'] = False
        attempt('receipt_without_consumption', unconsumed, False)
        return outcomes
    suite.case('consumption_receipt_required', receipt)

    def refusal():
        source = V5/'l166-draw1'; packet = r6.read_json(source/'evidence.json'); outcomes = {}
        def attempt(label, change, expected):
            run = staged(source, change)
            try: result = driver.reconstruction_refusal(run, packet)
            finally: shutil.rmtree(run.parent)
            got = None if result is None else result['diagnosis']
            require(got == expected, f'{label}: {got}'); outcomes[label] = got
        def process(field, value):
            def change(run, rows):
                select('term_mode_nat', 'ℤ')(run, rows)
                p = run/'stages/reconstruct/reconstruct.process.json'; record = r6.read_json(p); record[field] = value; r6.write_json(p, record)
            return change
        attempt('nat_closer_int_goal', select('term_mode_nat', 'ℤ'), 'nat_closer_int_goal')
        attempt('v5_record_without_selection', lambda run, rows: None, None)
        attempt('nat_closer_nat_goal', select('term_mode_nat', 'ℕ'), None)
        attempt('int_closer_selected', select('term_mode_int', 'ℤ'), None)
        attempt('selection_names_another_certificate', select('term_mode_nat', 'ℤ', {'other': True}), None)
        attempt('process_killed', process('exit_code', 137), None)
        attempt('resource_exhausted', process('resource_exhausted', 'wall'), None)
        attempt('monitor_failed', process('monitor_error', 'lost'), None)
        def extra_error(run, rows):
            select('term_mode_nat', 'ℤ')(run, rows)
            p = run/'stages/reconstruct/reconstruct.stderr'; p.write_text(p.read_text()+'\n/input/Frozen.lean:1:1: error: unrelated\n')
        attempt('unrelated_error_as_well', extra_error, None)
        def success_receipt(run, rows):
            select('term_mode_nat', 'ℤ')(run, rows); child(rows, 'reconstruction_finished', {'certificate': packet['certificate']}, 'closer_selected')
        attempt('success_receipt_present', success_receipt, None)
        def guard_bypassed(run, rows):
            select('term_mode_nat', 'ℤ')(run, rows)
            next(r for r in rows if r['event'] == 'dispatch_started')['payload']['data']['ir'] = {'other': True}
        attempt('dispatched_ir_differs_from_packet', guard_bypassed, None)
        return outcomes
    suite.case('reconstruction_refusal_requires_bound_evidence', refusal)
    # ---------------------------------------------------------------- revision 7: signing lifecycle
    CAPTURE = r6.ROOT/'sources/pricing-approved-campaign-3'
    NOW = max(v['finished_unix'] for v in v2.source_evidence(CAPTURE).values()) + 3600  # an hour after the capture: admissible
    APPROVED, LATER = '2026-09-22T21:00:00Z', '2026-09-22T21:10:00Z'
    BLOCK1 = {s: 1 for s in contract.POSABLE}; BLOCK2 = {s: 2 for s in contract.POSABLE}
    SCOPE = 'canned signing control; isolated temporary policy and ledgers; no transmission'
    SIGNED_FIELDS = ('live_enabled', 'authorization', 'live_model_calls_authorized', 'signed_from_checkpoint_sha256')

    def refused_signing(fn, code):
        try: fn()
        except (ValueError, ledger.Failure, gate.Failure) as error:
            got = getattr(error, 'code', None) or str(error)
            require(got == code, f'refused with {got}, expected {code}'); return got
        raise AssertionError('accepted, expected '+code)

    from contextlib import contextmanager
    @contextmanager
    def sandbox():
        with tempfile.TemporaryDirectory(prefix='r6-014-signing-') as temp:
            temp = Path(temp)
            with patch.object(contract, 'CONFIG', temp/'policy.json'), patch.object(contract, 'LOCK', temp/'lock.json'), \
                 patch.object(contract, 'CHECKPOINT', temp/'policy.checkpoint.json'), patch.object(contract, 'LEDGERS', temp/'ledgers'):
                contract.freeze(CAPTURE); yield temp

    def dirs(c): return sorted(p.name for p in (contract.LEDGERS/c['campaign']['id']).iterdir())
    def live_rows(c):
        book = contract.campaign_ledger(True, c)
        return ledger.parse(book.path.read_bytes()) if book.path.exists() else []

    def complete(before):
        c = contract.config(); record, s_live = contract.live_permitted(c); _, s_reh = contract.campaign_ledger(False, c).snapshot()
        require(contract.CHECKPOINT.read_bytes() == before and c['signed_from_checkpoint_sha256'] == v2.sha(before), 'checkpoint')
        require(s_live['purpose'] == 'live' and s_live['schedule'] == c['campaign']['schedule'] and s_live['revisions'] == [v2.sha(contract.CONFIG.read_bytes())], 'live ledger')
        require(s_reh['revisions'][-1] == v2.sha(contract.CONFIG.read_bytes()) and len(s_reh['revisions']) == 2, 'rehearsal ledger')
        require(dirs(c) == ['live', 'rehearsal'] and len(live_rows(c)) == 1, 'one ledger per purpose, one activation')
        receipt = json.loads(contract.activation_receipt().read_bytes())
        require(receipt['activation_row_hash'] == live_rows(c)[0]['row_hash'] and receipt['campaign_id'] == c['campaign']['id'], 'activation receipt')
        return c, s_live

    def signing_binds():
        with sandbox():
            before = contract.CONFIG.read_bytes(); disabled = json.loads(before)
            refused_signing(lambda: contract.live_permitted(contract.config()), 'cohort_live_disabled')
            contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW)
            c, s = complete(before)
            require(c['authorization'] == contract.block_record('author', APPROVED, BLOCK1, SCOPE) and c['live_model_calls_authorized'] == 11)
            require(c['limits']['total_micro_usd'] == 1126400 == 11*contract.ATTEMPT_MICRO_USD and s['maximum_micro_usd'] == 1126400 and s['maximum_transmissions'] == 11)
            require(c['campaign']['planned_schedule'] == contract.PLANNED and c['campaign']['planned_micro_usd'] == 9011200 == 88*contract.ATTEMPT_MICRO_USD)
            unchanged = lambda v: {k: x for k, x in v.items() if k not in (*SIGNED_FIELDS, 'campaign', 'limits')}
            require(unchanged(c) == unchanged(disabled) and c['contract_sha256'] == disabled['contract_sha256'] and c['source_lock_sha256'] == disabled['source_lock_sha256']
                    and c['pricing_admission'] == disabled['pricing_admission'] and {k: v for k, v in c['campaign'].items() if k != 'schedule'} == {k: v for k, v in disabled['campaign'].items() if k != 'schedule'},
                    'the signature changes the authority only')
            return {'block': 'eleven sites, draw 1', 'reserved_micro_usd': 1126400, 'planned_micro_usd': 9011200}
    suite.case('signing_binds_block_and_preserves_checkpoint', signing_binds)

    def signing_refuses():
        with sandbox():
            before = contract.CONFIG.read_bytes(); codes = {}
            for label, schedule in (('site_outside_plan', {**BLOCK1, 'bracket-l098': 1}), ('draw_outside_plan', {**BLOCK1, 'bracket-l069': 9}),
                                    ('empty', {}), ('zero_draws', {**BLOCK1, 'bracket-l069': 0}), ('boolean_draws', {**BLOCK1, 'bracket-l069': True})):
                codes[label] = refused_signing(lambda: contract.sign('author', APPROVED, schedule, CAPTURE, SCOPE, now=NOW), 'cohort_signing_outside_plan')
            codes['stale_capture'] = refused_signing(lambda: contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW+86400), 'cohort_signing_capture_stale')
            codes['capture_in_future'] = refused_signing(lambda: contract.sign('author', '2026-09-22T19:00:00Z', BLOCK1, CAPTURE, SCOPE, now=NOW-7200), 'cohort_signing_capture_in_future')
            codes['approval_in_future'] = refused_signing(lambda: contract.sign('author', '2026-09-23T23:00:00Z', BLOCK1, CAPTURE, SCOPE, now=NOW), 'cohort_signing_approval_in_future')
            codes['blank_approver'] = refused_signing(lambda: contract.sign(' ', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW), 'cohort_authorization_approver')
            c = contract.config()
            require(contract.CONFIG.read_bytes() == before and not contract.CHECKPOINT.exists() and dirs(c) == ['rehearsal'], 'a refusal writes nothing')
            return codes
    suite.case('signing_refuses_outside_plan_and_bad_pricing', signing_refuses)

    class Crash(RuntimeError): pass

    def signing_interrupted():
        outcomes = {}
        def boundary(label, patcher, after=None):
            with sandbox():
                before = contract.CONFIG.read_bytes()
                with patcher():
                    try: contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW); raise AssertionError(label+': no interruption')
                    except Crash: pass
                if after: after()
                c = json.loads(contract.CONFIG.read_bytes())
                require(contract.CONFIG.read_bytes() in (before, contract.CONFIG.read_bytes()) and c['live_enabled'] in (False, True), label)
                if c['live_enabled']: refused_signing(lambda: contract.live_permitted(contract.config()), 'cohort_activation_receipt_missing')  # nothing can fund
                else: refused_signing(lambda: contract.live_permitted(contract.config()), 'cohort_live_disabled')
                contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW)  # the same call resumes
                complete(before); outcomes[label] = 'resumed'
        def crash_on(target, when):
            original = getattr(*target)
            def wrapper(*args, **kwargs):
                if when(*args, **kwargs): raise Crash()
                return original(*args, **kwargs)
            return patch.object(target[0], target[1], wrapper)
        boundary('before_checkpoint', lambda: crash_on((ledger, 'write_exclusive'), lambda path, data: Path(path) == contract.CHECKPOINT))
        boundary('after_checkpoint_before_policy', lambda: crash_on((contract, 'atomic_write'), lambda path, data: True))
        boundary('policy_replace_interrupted', lambda: crash_on((os, 'replace'), lambda a, b: Path(b) == contract.CONFIG))
        boundary('after_policy_before_rehearsal_registration', lambda: crash_on((ledger.Ledger, 'register_revision'), lambda self, policy, live: True))
        boundary('live_activation_row_without_head', lambda: crash_on((ledger.Ledger, '_write_head'), lambda self, rows, last: self.directory.name == 'live'))
        def tear():  # the activation row itself torn: a partial first line and no head
            c = json.loads(contract.CONFIG.read_bytes()); book = contract.campaign_ledger(True, c); raw = book.path.read_bytes()
            book.path.write_bytes(raw[:len(raw)//2])
        boundary('live_activation_row_torn', lambda: crash_on((ledger.Ledger, '_write_head'), lambda self, rows, last: self.directory.name == 'live'), tear)
        boundary('after_activation_before_receipt', lambda: crash_on((ledger.Ledger, '_write_receipt'), lambda self, row: True))
        def torn_receipt():  # a receipt torn mid-write: refused, never repaired or replaced by a second activation
            c = json.loads(contract.CONFIG.read_bytes())
            refused_signing(lambda: contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW), 'cohort_activation_authority_lost')
            receipt = contract.activation_receipt(); receipt.unlink()  # the operator removes the torn file after inspection; the ledger is unchanged
        boundary('receipt_torn', lambda: crash_on((ledger, 'write_exclusive'), lambda path, data: Path(path) == contract.activation_receipt()
                                                   and (Path(path).write_bytes(data[:len(data)//2]) or True)), torn_receipt)
        return outcomes
    suite.case('signing_interrupted_at_each_boundary_resumes', signing_interrupted)

    def signing_repeats():
        with sandbox():
            before = contract.CONFIG.read_bytes()
            contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW); c = contract.config(); signed_bytes = contract.CONFIG.read_bytes()
            codes = {'repeated': refused_signing(lambda: contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW), 'cohort_already_signed'),
                     'another_scope': refused_signing(lambda: contract.sign('author', APPROVED, BLOCK2, CAPTURE, SCOPE, now=NOW), 'cohort_already_signed_for_another_scope'),
                     'another_approver': refused_signing(lambda: contract.sign('other', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW), 'cohort_already_signed_for_another_scope')}
            require(len(live_rows(c)) == 1 and contract.CONFIG.read_bytes() == signed_bytes)
            contract.atomic_write(contract.CONFIG, before)  # authority rolled back after activation
            codes['rolled_back_cannot_fund'] = refused_signing(lambda: contract.live_permitted(contract.config()), 'cohort_live_disabled')
            codes['rolled_back_other_scope'] = refused_signing(lambda: contract.sign('author', APPROVED, {**BLOCK1, 'bracket-l069': 2}, CAPTURE, SCOPE, now=NOW), 'cohort_signing_conflicts_with_activation')
            contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW)  # the identical authority restores; no second activation
            require(contract.CONFIG.read_bytes() == signed_bytes); complete(before)
            missing = {**json.loads(signed_bytes), 'authorization': None}; contract.atomic_write(contract.CONFIG, contract.canonical_policy(missing))
            codes['missing_authority'] = refused_signing(lambda: contract.authorization(json.loads(contract.CONFIG.read_bytes())), 'cohort_authorization_absent')
            return codes
    suite.case('signing_repeated_conflicting_or_rolled_back', signing_repeats)

    def later_block():
        with sandbox():
            contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW); c1 = contract.config(); book = contract.campaign_ledger(True, c1)
            p1 = reserve(book, c1, D1, 1); with_grant(book, p1); book.reconcile(p1, TERMINATED, SENT, {})  # a consumed slot
            p2 = reserve(book, c1, C8, 1); book.reconcile(p2, TERMINATED, UNSENT, {})  # a pre-send release: C8/1 stays available
            codes = {'draw_two_before_authority': refused_signing(lambda: reserve(book, c1, D1, 2), 'cohort_slot_not_scheduled')}
            enlarged = signed(c1, schedule=BLOCK2, maximum_micro_usd=22*contract.ATTEMPT_MICRO_USD, approved_utc=APPROVED, scope=SCOPE)
            enlarged['limits']['total_micro_usd'] = 22*contract.ATTEMPT_MICRO_USD
            codes['ledger_enlargement_same_authority'] = refused_signing(lambda: book.register_revision(enlarged, True), 'cohort_revision_scope_requires_new_authority')
            older = signed(c1, schedule=BLOCK2, maximum_micro_usd=22*contract.ATTEMPT_MICRO_USD, approved_utc='2026-09-22T20:00:00Z', approved_by='other', scope=SCOPE)
            codes['ledger_enlargement_older_authority'] = refused_signing(lambda: book.register_revision(older, True), 'cohort_revision_scope_requires_new_authority')
            codes['authorize_not_newer'] = refused_signing(lambda: contract.authorize('author', APPROVED, BLOCK2, CAPTURE, SCOPE, 'block 2', now=NOW), 'cohort_authorize_not_newer')
            codes['authorize_not_larger'] = refused_signing(lambda: contract.authorize('author', LATER, BLOCK1, CAPTURE, SCOPE, 'block 2', now=NOW), 'cohort_authorize_not_larger')
            codes['authorize_shrinks'] = refused_signing(lambda: contract.authorize('author', LATER, {t: 2 for t in contract.POSABLE if t != D1}, CAPTURE, SCOPE, 'block 2', now=NOW), 'cohort_authorize_shrinks_schedule')
            codes['authorize_outside_plan'] = refused_signing(lambda: contract.authorize('author', LATER, {**BLOCK2, D1: 9}, CAPTURE, SCOPE, 'block 2', now=NOW), 'cohort_signing_outside_plan')
            codes['authorize_stale'] = refused_signing(lambda: contract.authorize('author', LATER, BLOCK2, CAPTURE, SCOPE, 'block 2', now=NOW+86400), 'cohort_signing_capture_stale')
            request_before = budget.request(site_task.get(D1), r6.read_json(REPRESENTABILITY/D1/'prepared.json'))[0]
            old_bytes = contract.CONFIG.read_bytes()
            with patch.object(contract, 'atomic_write', side_effect=Crash()):  # interrupted after the retained copy, before the new policy
                try: contract.authorize('author', LATER, BLOCK2, CAPTURE, SCOPE, 'block 2', now=NOW)
                except Crash: pass
            require(contract.CONFIG.read_bytes() == old_bytes and contract.CONFIG.with_name(contract.CONFIG.stem+'.r1.json').read_bytes() == old_bytes)
            contract.authorize('author', LATER, BLOCK2, CAPTURE, SCOPE, 'block 2', now=NOW); c2 = contract.config()
            codes['authorize_repeated'] = refused_signing(lambda: contract.authorize('author', LATER, BLOCK2, CAPTURE, SCOPE, 'block 2', now=NOW), 'cohort_already_authorized')
            _, s = contract.live_permitted(c2)
            require(c2['revision'] == 2 and c2['previous_policy_sha256'] == v2.sha(old_bytes) and s['revisions'] == [v2.sha(old_bytes), v2.sha(contract.CONFIG.read_bytes())])
            require(s['slots'][f'{D1}/1']['consumed'] and s['transmissions_consumed'] == 1 and s['maximum_transmissions'] == 22 and s['maximum_micro_usd'] == 2252800)
            codes['consumed_slot_stays_consumed'] = refused_signing(lambda: reserve(book, c2, D1, 1), 'cohort_slot_consumed')
            codes['old_revision_refused'] = refused_signing(lambda: reserve(book, c1, D1, 2), 'cohort_revision_not_current')
            p3 = reserve(book, c2, D1, 2); require(p3['draw'] == 2); book.reconcile(p3, TERMINATED, UNSENT, {})
            p4 = reserve(book, c2, C8, 1); require(p4['slot_attempt'] == 2)  # the released first-block slot, retried under the new authority
            request_after = budget.request(site_task.get(D1), r6.read_json(REPRESENTABILITY/D1/'prepared.json'))[0]
            require(request_before == request_after, 'model-visible request bytes are fixed across authorizations')
            return codes
    suite.case('later_block_requires_new_authority', later_block)

    def pricing_revision():
        with sandbox():
            contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW); c1 = contract.config(); book = contract.campaign_ledger(True, c1)
            p1 = reserve(book, c1, D1, 1); with_grant(book, p1); book.reconcile(p1, TERMINATED, SENT, {})
            contract.revise(CAPTURE, 'pricing refresh'); c2 = contract.config()
            _, s = contract.live_permitted(c2)
            require(c2['authorization'] == c1['authorization'] and c2['revision'] == 2 and c2['signed_from_checkpoint_sha256'] == c1['signed_from_checkpoint_sha256'])
            require(s['slots'][f'{D1}/1']['consumed'] and s['schedule'] == BLOCK1 and len(s['revisions']) == 2)
            swapped = {**c2, 'revision': 3, 'authorization': {**c2['authorization'], 'approved_by': 'other'}}
            code = refused_signing(lambda: book.register_revision(swapped, True), 'cohort_revision_authority_not_newer')  # a same-time substitute authority
            return {'same_authority': True, 'consumed_persisted': True, 'authority_swap_without_scope': code}
    suite.case('pricing_revision_keeps_authority', pricing_revision)

    def lost_authority():
        """The review's scenario: a consumed slot, then the established live authority removed; every re-entry is refused and consumption kept."""
        outcomes = {}
        losses = {'live_directory_moved_aside': lambda book, temp: book.directory.rename(temp/'retained-live'),
                  'ledger_and_head_removed_slots_kept': lambda book, temp: [p.rename(temp/('retained-'+p.name)) for p in (book.path, book.head)],
                  'head_removed': lambda book, temp: book.head.rename(temp/'retained-head.json'),
                  'ledger_replaced_by_a_fresh_activation': lambda book, temp: (book.directory.rename(temp/'retained-live'),
                                                                               ledger.Ledger(book.directory, book.campaign_id).activate(contract.config(), True))}
        for label, lose in losses.items():
            with sandbox() as temp:
                contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW); c = contract.config(); book = contract.campaign_ledger(True, c)
                p1 = reserve(book, c, D1, 1); with_grant(book, p1); book.reconcile(p1, TERMINATED, SENT, {})
                codes = {'spent_slot': refused_signing(lambda: reserve(book, c, D1, 1), 'cohort_slot_consumed')}
                _, before = book.snapshot(); signed_bytes = contract.CONFIG.read_bytes(); present = book.directory.exists()
                lose(book, temp)
                existed = book.directory.exists()
                codes['resign'] = refused_signing(lambda: contract.sign('author', APPROVED, BLOCK1, CAPTURE, SCOPE, now=NOW), 'cohort_activation_authority_lost')
                codes['authorize'] = refused_signing(lambda: contract.authorize('author', LATER, BLOCK2, CAPTURE, SCOPE, 'block 2', now=NOW), 'cohort_activation_authority_lost')
                codes['revise'] = refused_signing(lambda: contract.revise(CAPTURE, 'pricing refresh'), 'cohort_activation_authority_lost')
                codes['live_permitted'] = refused_signing(lambda: contract.live_permitted(contract.config()), 'cohort_activation_authority_lost')
                if label == 'ledger_replaced_by_a_fresh_activation':
                    codes['reserve_on_fresh_activation'] = refused_signing(lambda: reserve(contract.campaign_ledger(True, c), c, D1, 1), 'cohort_activation_receipt_missing')
                require(contract.CONFIG.read_bytes() == signed_bytes and book.directory.exists() == existed and present, label+': a refusal writes nothing')
                if label == 'live_directory_moved_aside':  # restored, the preserved authority serves again with its consumption intact
                    (temp/'retained-live').rename(book.directory); _, after = book.snapshot()
                    require(after['transmissions_consumed'] == before['transmissions_consumed'] == 1 and after['last_hash'] == before['last_hash'])
                    codes['restored_spent_slot'] = refused_signing(lambda: reserve(book, c, D1, 1), 'cohort_slot_consumed')
                outcomes[label] = codes
        return outcomes
    suite.case('lost_authority_fails_closed', lost_authority)

    def receipt_required():
        with sandbox():
            c0 = contract.config()
            unsigned_live = signed(c0, schedule=BLOCK1, maximum_micro_usd=11*contract.ATTEMPT_MICRO_USD, approved_utc=APPROVED, scope=SCOPE)
            unsigned_live['limits']['total_micro_usd'] = 11*contract.ATTEMPT_MICRO_USD
            book = contract.campaign_ledger(True, unsigned_live); book.activate(unsigned_live, True)  # an activation made without its receipt
            codes = {'reserve_without_receipt': refused_signing(lambda: reserve(book, unsigned_live, D1, 1), 'cohort_activation_receipt_missing'),
                     'unbound_ledger': refused_signing(lambda: ledger.Ledger(book.directory, book.campaign_id).ensure_activated(unsigned_live, True), 'cohort_activation_receipt_unbound')}
            other = contract.activation_receipt(); other.write_bytes(b'{}\n')  # a receipt naming no activation
            codes['reserve_with_foreign_receipt'] = refused_signing(lambda: reserve(book, unsigned_live, D1, 1), 'cohort_activation_receipt_missing')
            codes['established_with_foreign_receipt'] = refused_signing(lambda: book.established(), 'cohort_activation_authority_lost')
            return codes
    suite.case('live_reservation_requires_activation_receipt', receipt_required)
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

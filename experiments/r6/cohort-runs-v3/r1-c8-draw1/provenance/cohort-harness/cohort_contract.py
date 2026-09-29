"""R6-009: a scientific contract that survives pricing and authorization revisions.

What the model sees, and what shapes its answer, is fixed by one frozen
contract file: the exact instruction bytes, the rendering of a request into
messages, the request schema and row semantics, the response schema, the model
identity, the generation options with the options that must stay omitted, and
the scientific resource limits. A request carries the contract's digest, not a
policy digest, together with the task, challenge and exact-IR bindings it always
carried. So a pricing refresh or a new signature changes the authorization
envelope only: the bytes sent to the model for a given task are identical
across revisions.

A policy binds to the contract by digest, may not disagree with its generation
settings or scientific limits, carries the pricing evidence and the spending
limits, and names a *campaign*: a stable identity chosen at the first freeze
and carried into every revision. The campaign ledger is keyed by that identity;
each revised policy is registered in it, and consumed (task, draw) slots stay
consumed. This checkpoint is canned: `live_enabled` is false, the schedule is
small, and no live ledger exists.
"""
import json
import uuid

import admission
import campaign_contract as previous
import cohort_ledger as ledger
import credential
import envelope_payload
import pricing_gate_v2 as v2
import pricing_gate_v3 as gate
import provider_contract as base_runtime
import publication
import run as r6

NAME = 'farkas_cohort_v3'
CONTRACT = r6.ROOT/'contracts/farkas-proposal-contract-v1.json'
CONFIG = r6.ROOT/'policies/farkas-cohort-v3.json'
LOCK = r6.ROOT/'policies/cohort-harness-v3.sha256.json'
RUNTIME = previous.RUNTIME
LEDGERS = r6.ROOT/'ledgers/campaigns'
PROMPT = previous.PROMPT
FILES = ('cohort_contract.py', 'cohort_ledger.py', 'cohort_budget.py', 'cohort_https.py', 'cohort_episode.py', 'pricing_gate_v3.py', 'test_cohort.py')
MODEL = previous.MODEL
ENDPOINT = previous.ENDPOINT
ATTEMPT_MICRO_USD = previous.ATTEMPT_MICRO_USD
MAXIMUM_PRESEND_ATTEMPTS = 3
SCHEDULE = {'verinf-d1-70': 3}  # the canned checkpoint's schedule; a signed cohort freezes its own
REHEARSAL_SCHEDULE = {'verinf-d1-70': 64, 'c1-c8-2p18': 64}
SCIENTIFIC_LIMITS = ('message_utf8_bytes', 'maximum_request_bytes', 'maximum_response_bytes', 'output_tokens', 'input_tokens_reserved',
                     'request_wall_seconds', 'io_timeout_seconds')
OMITTED_OPTIONS = ('temperature', 'top_p', 'seed', 'top_logprobs', 'metadata', 'previous_response_id', 'instructions', 'text', 'include',
                   'prompt_cache_key', 'safety_identifier', 'user', 'max_tool_calls', 'service_tier_fallback')
COMMITMENT_DOMAIN = previous.COMMITMENT_DOMAIN
PHASES = {**previous.PHASES, 'cohort-ledger': 'cohort_ledger'}
bundle = previous.bundle
REHEARSAL_AUTHORIZATION = {'approved_by': 'rehearsal', 'approved_utc': '1970-01-01T00:00:00Z', 'model_id': MODEL, 'schedule': REHEARSAL_SCHEDULE,
                           'maximum_micro_usd': 128*ATTEMPT_MICRO_USD, 'maximum_presend_attempts': MAXIMUM_PRESEND_ATTEMPTS,
                           'scope': 'loopback rehearsals only; no provider transmission is possible on this ledger'}


def contract_record():
    """Built from the frozen upstream pieces; frozen as canonical bytes."""
    earlier = r6.read_json(previous.CONFIG); prompt = PROMPT.read_bytes()
    return {'schema_version': gate.CONTRACT_SCHEMA, 'name': 'farkas_proposal_contract_v1',
            'instruction': {'path': str(PROMPT.relative_to(r6.ROOT)), 'sha256': r6.hashlib.sha256(prompt).hexdigest(), 'bytes': len(prompt)},
            'rendering': {'system_role': 'system', 'user_role': 'user', 'prefix': envelope_payload.PREFIX, 'separator': envelope_payload.SEPARATOR,
                          'user_message': 'prefix + sha256(request bytes) + separator + request bytes',
                          'request_encoding': 'json.dumps(sort_keys, separators=(",",":"), ensure_ascii=False) + newline',
                          'entity_body_encoding': 'json.dumps(sort_keys, separators=(",",":"), ensure_ascii=True) + newline'},
            'request_schema': {'schema_version': gate.REQUEST_SCHEMA, 'path': 'schema/cohort-request.schema.json',
                               'sha256': r6.sha(r6.ROOT/'schema/cohort-request.schema.json'), 'row_relations': ['le', 'eq'],
                               'row_semantics': 'f = constant + sum(coefficient*variable); le means f <= 0, eq means f = 0; strict source bounds '
                                                'are pre-tightened by one; decimal integer strings; the row named neg_goal is the negated target',
                               'context_policy': earlier['admission_rule'] if isinstance(earlier.get('admission_rule'), str) else 'farkas_rows_only_v1'},
            'response_schema': {'path': 'schema/proposal-response.schema.json', 'sha256': r6.sha(r6.ROOT/'schema/proposal-response.schema.json'),
                                'shape': '{request_sha256, witness: {coefficients: [{hypothesis, coefficient}]}}',
                                'coefficient_grammar': '-?(0|[1-9][0-9]*), at most 128 characters', 'support': '1 to 32 distinct emitted row names'},
            'model': {'requested_id': MODEL, 'allowed_response_ids': [MODEL], 'model_computation_attested': False},
            'generation': {'options': earlier['request'], 'omitted': list(OMITTED_OPTIONS),
                           'scope': 'options are sent exactly as listed; omitted options are never sent; omission is not a determinism claim'},
            'limits': {k: earlier['limits'][k] for k in SCIENTIFIC_LIMITS},
            'scope': 'the model-visible input and the constraints that shape its answer; authorization, pricing and spending are outside it'}


def contract():
    value = r6.read_json(CONTRACT)
    if CONTRACT.read_bytes() != v2.canonical(value)+b'\n': raise ValueError('Contract is not in canonical form')
    if value != contract_record(): raise ValueError('Contract differs from its frozen inputs')
    gate.check_contract(value)
    return value


def contract_sha256():
    return r6.sha(CONTRACT)


def policy_sha256():
    return r6.sha(CONFIG)


def config():
    c = r6.read_json(CONFIG)
    if c['name'] != NAME or c['source_lock_sha256'] != r6.sha(LOCK): raise ValueError('Cohort policy identity changed')
    if c['contract_sha256'] != contract_sha256(): raise ValueError('Cohort policy contract binding changed')
    gate.check_policy(c, contract())
    if c['revision'] == 1 and c['previous_policy_sha256'] != r6.sha(previous.CONFIG): raise ValueError('Cohort dependency identity changed')
    if c['admission_sha256'] != r6.sha(admission.FROZEN): raise ValueError('Cohort admission identity changed')
    if c['endpoint'] != ENDPOINT or c['runtime_lock_sha256'] != r6.sha(RUNTIME): raise ValueError('Cohort endpoint/runtime identity changed')
    if CONFIG.read_bytes() != v2.canonical(c)+b'\n': raise ValueError('Cohort policy is not in canonical form')
    if c['campaign']['schedule'] != SCHEDULE and c['live_enabled'] is False: raise ValueError('Cohort checkpoint schedule changed')
    return c


def source_lock():
    values = r6.read_json(LOCK)
    if set(values) != set(FILES): raise ValueError('Cohort source inventory changed')
    config(); return values


def verify_sources():
    previous.verify_sources()
    if any(r6.sha(r6.ROOT/p) != h for p, h in source_lock().items()): raise ValueError('Cohort policy requires its frozen source revision')


def materialize_runtime(): return previous.materialize_runtime()
def sources(c=None): return r6.ROOT/(c or config())['pricing_sources']  # per revision: the capture this policy admits under
def authorization(c): return ledger.authorization_scope(c)


def campaign_ledger(live, c=None):
    c = c or config()
    return ledger.Ledger(LEDGERS/c['campaign']['id']/('live' if live else 'rehearsal'), c['campaign']['id'])


def live_permitted(c):
    record = authorization(c); _, s = campaign_ledger(True, c).snapshot(); ledger.check_activation(s, c, True)
    return record, s


def pinned_admission(sources):
    approved = json.loads(json.dumps(r6.read_json(previous.CONFIG)['pricing_admission']))
    evidence = v2.source_evidence(sources); earlier = r6.read_json(previous.CONFIG)['pricing_admission']['sources']
    approved['sources'] = {role: {'raw_sha256': v['raw_sha256'], 'extract_sha256': v['extract_sha256']} for role, v in evidence.items()}
    approved['source_review'] = {'previous_approved': earlier, 'capture': str(sources.relative_to(r6.ROOT)),
        'model_extract_identical_to_previous': evidence['model']['extract_sha256'] == earlier['model']['extract_sha256'],
        'caching_extract_identical_to_previous': evidence['caching']['extract_sha256'] == earlier['caching']['extract_sha256'],
        'rates_identical_to_previous': v2.rates_from(evidence) == r6.read_json(previous.CONFIG)['pricing']['nano_usd_per_token'],
        'scope': 'a capture within the 24-hour admission window; extracts and rates reviewed against the approved v7 capture'}
    if not all(approved['source_review'][k] for k in ('model_extract_identical_to_previous', 'caching_extract_identical_to_previous', 'rates_identical_to_previous')):
        raise ValueError('Cohort pricing capture differs semantically from the approved extracts; review before freezing')
    return approved


def policy_record(sources, campaign_id, revision, previous_sha256, record=None, reason=None):
    earlier = r6.read_json(previous.CONFIG); _, ca = bundle(); contract_value = contract()
    return {'schema_version': 'r6-cohort-policy-1', 'name': NAME, 'revision': revision, 'revision_reason': reason,
            'contract_sha256': contract_sha256(),
            'campaign': {'id': campaign_id, 'schedule': (record or {}).get('schedule', SCHEDULE), 'rehearsal_authorization': REHEARSAL_AUTHORIZATION,
                         'ledger_directory': 'ledgers/campaigns/<campaign_id>/{live,rehearsal}',
                         'scope': 'stable identity across pricing and authorization revisions; consumed (task, draw) slots persist; '
                                  'distinct campaigns may share a contract and are distinct ledgers'},
            'provider_api': earlier['provider_api'], 'transport': earlier['transport'], 'mode': 'provider_request', 'endpoint': ENDPOINT,
            'live_enabled': record is not None, 'authorization': record,
            'model': contract_value['model'] | {'revision_status': earlier['model']['revision_status']},
            'sampling': earlier['sampling'], 'network': earlier['network'], 'tls': {**earlier['tls'], 'public_ca_bundle': ca},
            'credential': earlier['credential'],
            'attribution': {**earlier['attribution'], 'consumer': earlier['attribution']['consumer']},
            'request': contract_value['generation']['options'],
            'limits': {**{k: v for k, v in earlier['limits'].items() if k not in ('maximum_transmissions',)}, 'attempts_per_episode': 1,
                       'automatic_retries': 0, 'redirects': 0, 'maximum_presend_attempts': MAXIMUM_PRESEND_ATTEMPTS,
                       'total_micro_usd': (record or {}).get('maximum_micro_usd', ATTEMPT_MICRO_USD*sum(SCHEDULE.values()))},
            'pricing': earlier['pricing'], 'pricing_admission': pinned_admission(sources), 'pricing_sources': str(sources.relative_to(r6.ROOT)),
            'publication': earlier['publication'], 'prompt_sha256': r6.sha(PROMPT), 'source_lock_sha256': r6.sha(LOCK),
            'runtime_lock_sha256': r6.sha(RUNTIME), 'runtime_divergence': earlier['runtime_divergence'],
            'previous_policy_sha256': previous_sha256, 'previous_source_lock_sha256': r6.sha(previous.LOCK),
            'admission_sha256': r6.sha(admission.FROZEN), 'admission_rule': admission.RULE, 'pricing_gate_sha256': r6.sha(r6.ROOT/'pricing_gate_v3.py'),
            'live_model_calls_authorized': sum(record['schedule'].values()) if record else 0,
            'scope': 'canned checkpoint of the cohort contract, campaign identity and task-by-draw ledger; a signed revision authorizes exactly its schedule'}


def freeze(sources):
    """First revision, disabled: contract, lock, policy, and the campaign's rehearsal ledger."""
    if CONFIG.exists() or LOCK.exists(): raise ValueError('Cohort policy is already frozen')
    previous.verify_sources(); admission.verify()
    CONTRACT.parent.mkdir(exist_ok=True)
    if not CONTRACT.exists():
        with CONTRACT.open('xb') as f: f.write(v2.canonical(contract_record())+b'\n')
    contract()
    with LOCK.open('x') as f: f.write(json.dumps({p: r6.sha(r6.ROOT/p) for p in FILES}, indent=2)+'\n')
    policy = policy_record(r6.Path(sources).resolve(), uuid.uuid4().hex, 1, r6.sha(previous.CONFIG))
    with CONFIG.open('xb') as f: f.write(v2.canonical(policy)+b'\n')
    config()
    campaign_ledger(False).activate(policy, False)
    return policy_sha256()


def revise(sources, reason):
    """A pricing refresh: a new policy revision under the same campaign, contract and lock; the previous revision is retained;
    the campaign's ledgers register the revision, so consumed slots persist and the previous digest can no longer reserve."""
    verify_sources(); c = config(); sources = r6.Path(sources).resolve()
    retained = CONFIG.with_name(f'{CONFIG.stem}.r{c["revision"]}.json')
    if retained.exists(): raise ValueError('Retained revision exists')
    policy = policy_record(sources, c['campaign']['id'], c['revision']+1, policy_sha256(), c['authorization'], reason)
    retained.write_bytes(CONFIG.read_bytes()); CONFIG.write_bytes(v2.canonical(policy)+b'\n'); config()
    campaign_ledger(False).register_revision(policy, False)
    if policy['live_enabled']: campaign_ledger(True).register_revision(policy, True)
    return policy_sha256()


if __name__ == '__main__':
    import sys
    if sys.argv[1:2] == ['revise']: print(revise(sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else 'pricing refresh'))
    else: print(freeze(sys.argv[1] if len(sys.argv) > 1 else r6.ROOT/'sources/pricing-approved-campaign-1'))

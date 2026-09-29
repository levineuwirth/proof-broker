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

Revision 4 (R6-012) poses census sites instead of the two registered controls. Contract v2 keeps the instruction bytes,
rendering, response schema, model, generation options and scientific limits of contract v1 exactly, and changes only the
request: schema `r6-farkas-request-10` enumerates the fifteen reviewed primary sites, and the admission rule is policy C
(`site_request.admit`): arithmetic rows derived independently from the final IR, omissions derived and recorded as evaluator
evidence, negated order comparisons expressed, unique references and one final `neg_goal` required. The canned schedule is
the sites that policy C poses, confirmed at freeze by running the gate over every site's prepared problem; the denominator
stays fifteen. Nothing here authorizes a live call.
"""
import json
import uuid

import admission
import campaign_contract as previous
import cohort_ledger as ledger
import credential
import envelope_payload
import pricing_gate_v2 as v2
import pricing_gate_v4 as gate
import provider_contract as base_runtime
import publication
import run as r6
import site_request
import site_task

NAME = 'farkas_cohort_v4'
CONTRACT = r6.ROOT/'contracts/farkas-proposal-contract-v2.json'
PREVIOUS_CONTRACT = r6.ROOT/'contracts/farkas-proposal-contract-v1.json'
REQUEST_SCHEMA_PATH = 'schema/cohort-request-v2.schema.json'
CONFIG = r6.ROOT/'policies/farkas-cohort-v4.json'
LOCK = r6.ROOT/'policies/cohort-harness-v4.sha256.json'
REPRESENTABILITY = r6.ROOT/'census-runs/representability-v2'
RUNTIME = r6.ROOT/'policies/cohort-runtime-v1.json'  # revision 4: the host's shared libraries moved; see runtime_divergence
PREVIOUS_RUNTIME = previous.RUNTIME
LEDGERS = r6.ROOT/'ledgers/campaigns'
PROMPT = previous.PROMPT
FILES = ('cohort_contract.py', 'cohort_ledger.py', 'cohort_budget.py', 'cohort_https.py', 'cohort_episode.py', 'site_network.py', 'pricing_gate_v4.py', 'test_cohort.py')
MODEL = previous.MODEL
ENDPOINT = previous.ENDPOINT
ATTEMPT_MICRO_USD = previous.ATTEMPT_MICRO_USD
MAXIMUM_PRESEND_ATTEMPTS = 3
# The sites policy C poses (confirmed at freeze against every site's prepared problem), eight draws each: the canned schedule.
POSABLE = ('bracket-l069', 'bracket-l070', 'bracket-l071', 'bracket-l078', 'bracket-l096', 'bracket-l099', 'bracket-l166', 'bracket-l170',
           'bracket-l175', 'bracket-l204')
DRAWS = 8
SCHEDULE = {s: DRAWS for s in POSABLE}  # the canned checkpoint's schedule; a signed cohort freezes its own
REHEARSAL_SCHEDULE = {s: 64 for s in POSABLE}
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
    return {'schema_version': gate.CONTRACT_SCHEMA, 'name': 'farkas_proposal_contract_v2',
            'instruction': {'path': str(PROMPT.relative_to(r6.ROOT)), 'sha256': r6.hashlib.sha256(prompt).hexdigest(), 'bytes': len(prompt)},
            'rendering': {'system_role': 'system', 'user_role': 'user', 'prefix': envelope_payload.PREFIX, 'separator': envelope_payload.SEPARATOR,
                          'user_message': 'prefix + sha256(request bytes) + separator + request bytes',
                          'request_encoding': 'json.dumps(sort_keys, separators=(",",":"), ensure_ascii=False) + newline',
                          'entity_body_encoding': 'json.dumps(sort_keys, separators=(",",":"), ensure_ascii=True) + newline'},
            'request_schema': {'schema_version': gate.REQUEST_SCHEMA, 'path': REQUEST_SCHEMA_PATH,
                               'sha256': r6.sha(r6.ROOT/REQUEST_SCHEMA_PATH), 'row_relations': ['le', 'eq'],
                               'admission_policy': 'C: rows derived independently from the final IR; inexpressible hypotheses omitted, the omissions '
                                                   'derived and equal to the compiler\'s, recorded as evaluator evidence, not model-visible; negated order '
                                                   'comparisons expressed; unique row names; exactly one final neg_goal; the source fragment is evidence, '
                                                   'the posed rows are LIA',
                               'tasks': list(gate.TASKS),
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


def runtime_record():
    """The pinned runtime, verified against the host: interpreter, stdlib sources and extensions, and every ELF dependency."""
    r = r6.read_json(RUNTIME)
    if r6.sha(r6.Path(r['python'])) != r['python_sha256']: raise ValueError('Python interpreter changed')
    if any(r6.sha(r6.Path(p)) != h for p, h in r['stdlib_files'].items()): raise ValueError('Python stdlib changed')
    if any(r6.sha(r6.Path(v['host'])) != v['sha256'] for v in r['libraries']): raise ValueError('Python library changed')
    return r


def runtime_divergence():
    """How this pin differs from the signed v7 campaign's, stated rather than hidden (the pilot's precedent)."""
    earlier = r6.read_json(PREVIOUS_RUNTIME); record = r6.read_json(RUNTIME)
    before = {v['guest']: (v['host'], v['sha256']) for v in earlier['libraries']}; after = {v['guest']: (v['host'], v['sha256']) for v in record['libraries']}
    return {'previous_runtime_sha256': r6.sha(PREVIOUS_RUNTIME), 'python_unchanged': earlier['python_sha256'] == record['python_sha256'],
            'stdlib_unchanged': earlier['stdlib_files'] == record['stdlib_files'], 'extensions_unchanged': earlier['extension_binaries'] == record['extension_binaries'],
            'libraries_removed': sorted(set(before)-set(after)), 'libraries_added': sorted(set(after)-set(before)),
            'libraries_changed': {k: {'from': before[k][0], 'to': after[k][0]} for k in sorted(before.keys() & after.keys()) if before[k] != after[k]},
            'cause': 'host package updates between the v7 signing and this checkpoint; recorded as a runtime boundary, not pooled'}


def materialize_runtime():
    """`campaign_contract.materialize_runtime` over this revision's pin."""
    import shutil
    record = runtime_record()
    root = r6.ROOT/'.cache/campaign-runtime'/r6.sha(RUNTIME)/'stdlib'
    original = r6.Path(record['stdlib'])
    wanted = {str(r6.Path(p).relative_to(original)): h for p, h in record['stdlib_files'].items()}
    root.mkdir(parents=True, exist_ok=True)
    for name in wanted:
        destination = root/name
        if not destination.exists():
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original/name, destination)
    actual = {str(p.relative_to(root)): r6.sha(p) for p in root.rglob('*') if p.is_file()}
    if actual != wanted or any(p.is_symlink() for p in root.rglob('*')):
        raise ValueError('Filtered Python runtime inventory changed')
    return root, record
def sources(c=None): return r6.ROOT/(c or config())['pricing_sources']  # per revision: the capture this policy admits under
def authorization(c): return ledger.authorization_scope(c)


def campaign_ledger(live, c=None):
    c = c or config()
    return ledger.Ledger(LEDGERS/c['campaign']['id']/('live' if live else 'rehearsal'), c['campaign']['id'])


def live_permitted(c):
    record = authorization(c); _, s = campaign_ledger(True, c).snapshot(); ledger.check_activation(s, c, True)
    return record, s


PROSE_FIELDS = ('snapshot_section',)
APPROVED_CAPTURE = 'sources/pricing-approved-campaign-2'  # the capture the signed v7 policy's extracts were reviewed against


def pinned_admission(sources):
    """The signed v7 policy's pricing admission, pinned to a fresh capture. Revision 4 replaces byte identity of the extracts with a
    narrow semantic review: rates, listed model identifiers, prices and price conditions must equal the approved capture's, and
    any other differing extract field must be listed prose that admission does not read; the differing fields are recorded."""
    approved = json.loads(json.dumps(r6.read_json(previous.CONFIG)['pricing_admission']))
    evidence = v2.source_evidence(sources); earlier = r6.read_json(previous.CONFIG)['pricing_admission']['sources']
    approved['sources'] = {role: {'raw_sha256': v['raw_sha256'], 'extract_sha256': v['extract_sha256']} for role, v in evidence.items()}
    old = {r: json.loads((r6.ROOT/APPROVED_CAPTURE/f'{r}.extract.json').read_bytes()) for r in evidence}
    new = {r: json.loads((sources/f'{r}.extract.json').read_bytes()) for r in evidence}
    differing = {r: sorted(k for k in set(old[r]) | set(new[r]) if old[r].get(k) != new[r].get(k)) for r in evidence}
    semantic = ('listed_ids', 'price_conditions', 'input', 'cached_input', 'output', 'role')
    approved['source_review'] = {'previous_approved': earlier, 'approved_capture': APPROVED_CAPTURE, 'capture': str(sources.relative_to(r6.ROOT)),
        'model_extract_identical_to_previous': evidence['model']['extract_sha256'] == earlier['model']['extract_sha256'],
        'caching_extract_identical_to_previous': evidence['caching']['extract_sha256'] == earlier['caching']['extract_sha256'],
        'rates_identical_to_previous': v2.rates_from(evidence) == r6.read_json(previous.CONFIG)['pricing']['nano_usd_per_token'],
        'semantic_fields_identical': all(old[r].get(k) == new[r].get(k) for r in evidence for k in semantic),
        'differing_extract_fields': differing, 'allowed_differing_fields': list(PROSE_FIELDS),
        'scope': 'a capture within the 24-hour admission window; rates, listed ids, prices and conditions identical to the approved capture; '
                 'any other differing extract field must be listed prose'}
    review = approved['source_review']
    if not (review['rates_identical_to_previous'] and review['semantic_fields_identical']) or any(set(f) - set(PROSE_FIELDS) for f in differing.values()):
        raise ValueError('Cohort pricing capture differs semantically from the approved extracts; review before freezing')
    return approved


def confirm_posable():
    """Policy C and gate v4 over every primary site's retained prepared problem (representability revision 2): the posable set must
    be exactly POSABLE, and each refusal is recorded with its code. The schedule is frozen from this, never from success."""
    site_task.verify_lock(); summary = r6.read_json(REPRESENTABILITY/'representability.json'); outcome = {}
    if summary['population'] != list(site_task.primary()): raise ValueError('representability population differs from the reviewed one')
    for site_id in site_task.primary():
        prepared = REPRESENTABILITY/site_id/'prepared.json'
        if not prepared.exists():
            outcome[site_id] = {'posable': False, 'code': 'interface_refused'}; continue
        try:
            rows, _ = site_request.admit(r6.read_json(prepared))
            gate.check_request_grammar({'schema_version': gate.REQUEST_SCHEMA, 'contract_sha256': '0'*64,
                'binding': {'task_id': site_id, **{k: '0'*64 for k in gate.BINDING_KEYS if k != 'task_id'}}, 'problem': {'fragment': 'LIA', 'rows': rows}})
            outcome[site_id] = {'posable': True, 'code': None}
        except (site_request.Refusal, gate.Failure) as refusal:
            outcome[site_id] = {'posable': False, 'code': getattr(refusal, 'code', type(refusal).__name__)}
    if tuple(s for s in site_task.primary() if outcome[s]['posable']) != POSABLE: raise ValueError('policy C poses a different set than POSABLE')
    return {'representability_sha256': r6.sha(REPRESENTABILITY/'representability.json'), 'outcome': outcome, 'denominator': len(outcome)}


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
            'runtime_lock_sha256': r6.sha(RUNTIME), 'runtime_divergence': runtime_divergence(),
            'previous_policy_sha256': previous_sha256, 'previous_source_lock_sha256': r6.sha(previous.LOCK),
            'supersedes': {'cohort_policy_sha256': r6.sha(r6.ROOT/'policies/farkas-cohort-v3.json'), 'cohort_lock_sha256': r6.sha(r6.ROOT/'policies/cohort-harness-v3.sha256.json'),
                           'contract_sha256': r6.sha(PREVIOUS_CONTRACT)},
            'admission_sha256': r6.sha(admission.FROZEN), 'admission_rule': admission.RULE, 'pricing_gate_sha256': r6.sha(r6.ROOT/'pricing_gate_v4.py'),
            'site_lock_sha256': r6.sha(site_task.LOCK), 'posable_confirmation': confirm_posable(),
            'live_model_calls_authorized': sum(record['schedule'].values()) if record else 0,
            'scope': 'canned checkpoint of contract v2 on census sites; a signed revision authorizes exactly its schedule; this one authorizes nothing'}


def freeze(sources):
    """First revision, disabled: contract, lock, policy, and the campaign's rehearsal ledger."""
    if CONFIG.exists() or LOCK.exists(): raise ValueError('Cohort policy is already frozen')
    previous.verify_sources(); admission.verify()
    if not RUNTIME.exists():
        with RUNTIME.open('x') as f: f.write(json.dumps(base_runtime.runtime_record(), indent=2)+'\n')
    runtime_record()
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
    else: print(freeze(sys.argv[1] if len(sys.argv) > 1 else r6.ROOT/'sources/pricing-approved-campaign-3'))

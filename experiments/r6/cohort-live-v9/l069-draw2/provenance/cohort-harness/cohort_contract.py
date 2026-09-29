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

Revision 5 (R6-013) keeps contract v2, gate v4 and policy C, and takes its prepared problems from representability revision 3,
where the preparation reifies exactly what reconstruction reifies (site harness v3). The posable set is derived again from
those problems by the same mechanical rule. The pricing review admits exactly the reviewed prose change, an old/new pair
pinned by digest, and nothing else.

Revision 6 (R6-013 outcome decision) keeps revision 5's contract, gate, policy C, posable set and schedule, and takes its prepared
problems from representability revision 4 (site harness v4), byte-identical to revision 3's. Site harness v4 builds the bridge with
closer-specific reconstruction observations, so the driver now requires the closer's own consumption receipt before a proof and
records the pinned ℕ closer's goal-shape refusal as `reconstruction_refused`, diagnosed from bound evidence.

Revision 7 (R6-014) adds the signing lifecycle; the contract, gate, policy C, posable set, driver and site harness are revision 6's. The
policy records the planned design (`PLANNED`: eleven sites, eight draws) separately from the authorized execution schedule. `sign()`
authorizes a first block within the plan: it refuses a stale or future pricing capture, preserves the disabled checkpoint bytes, writes
the signed policy atomically, registers it on the rehearsal ledger and activates the live ledger; interrupted at any persistence
boundary, the same call completes the remaining steps and never creates a second ledger, resets consumption or changes the scope, and a
different authority is refused. `authorize()` adds a later block: a larger scope needs a new, later approval, and the ledger enforces
that independently. `revise()` refreshes pricing under the same authority. The money limit is always the exact reservation of the
authorized slots at the frozen per-slot reservation.
"""
import json
import os
import time
import uuid
from datetime import datetime, timezone

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

NAME = 'farkas_cohort_v9'
CONTRACT = r6.ROOT/'contracts/farkas-proposal-contract-v2.json'
PREVIOUS_CONTRACT = r6.ROOT/'contracts/farkas-proposal-contract-v1.json'
REQUEST_SCHEMA_PATH = 'schema/cohort-request-v2.schema.json'
CONFIG = r6.ROOT/'policies/farkas-cohort-v9.json'
LOCK = r6.ROOT/'policies/cohort-harness-v9.sha256.json'
CHECKPOINT = r6.ROOT/'policies/farkas-cohort-v9.checkpoint.json'
REPRESENTABILITY = r6.ROOT/'census-runs/representability-v4'
SUPERSEDED_POLICY = r6.ROOT/'policies/farkas-cohort-v8.json'
SUPERSEDED_LOCK = r6.ROOT/'policies/cohort-harness-v8.sha256.json'
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
           'bracket-l175', 'bracket-l178', 'bracket-l204')  # revision 5: l178 posable once its duplicate names are renamed as reconstruction renames them
DRAWS = 8
SCHEDULE = {s: DRAWS for s in POSABLE}  # the canned checkpoint's schedule; a signed cohort freezes its own
PLANNED = dict(SCHEDULE)  # revision 7: the planned design, retained separately from any authorized execution schedule
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
    if c['campaign'].get('planned_schedule') != PLANNED: raise ValueError('Cohort planned design changed')
    if c['live_enabled'] is True: within_plan(c['campaign']['schedule'])
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


def activation_receipt():
    """Revision 8: the durable record, kept beside the policy and outside the ledger directory, that live activation completed."""
    return CONFIG.with_name(CONFIG.stem+'.activation.json')


def progress_floor():
    """Revision 9: the live ledger's progress floor (row count and last row hash), beside the policy and outside the ledger directory."""
    return CONFIG.with_name(CONFIG.stem+'.floor.json')


def campaign_ledger(live, c=None):
    c = c or config()
    return ledger.Ledger(LEDGERS/c['campaign']['id']/('live' if live else 'rehearsal'), c['campaign']['id'],
                         activation_receipt() if live else None, progress_floor() if live else None)


def live_permitted(c):
    record = authorization(c); book = campaign_ledger(True, c)
    ledger.require(book.established(), 'cohort_activation_receipt_missing')
    _, s = book.snapshot(); ledger.check_activation(s, c, True)
    return record, s


# The one reviewed prose change (R6-012 review): the model page's snapshot sentence lost a space before its full stop.
REVIEWED_PROSE = {('model', 'snapshot_section'): ('ef0c3fbf08d2b836a415f13c9511307e30b29abf30192cc9e7ea715dd4a0fc14',
                                                  'c33572e1aa67cb33d0fbee960f05af924b38bc34d806d26f3ae4801f4687c9cb')}
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
        'differing_extract_fields': differing, 'reviewed_prose_changes': {f'{r}.{k}': list(v) for (r, k), v in REVIEWED_PROSE.items()},
        'scope': 'a capture within the 24-hour admission window; rates, listed ids, prices and conditions identical to the approved capture; '
                 'any other differing extract field must be listed prose'}
    review = approved['source_review']
    def reviewed(role, key):  # exactly the reviewed old and new values, by digest
        pair = REVIEWED_PROSE.get((role, key))
        return pair is not None and (r6.hashlib.sha256(old[role][key].encode()).hexdigest(), r6.hashlib.sha256(new[role][key].encode()).hexdigest()) == pair
    if not (review['rates_identical_to_previous'] and review['semantic_fields_identical']) or not all(reviewed(r, k) for r, f in differing.items() for k in f):
        raise ValueError('Cohort pricing capture differs semantically from the approved extracts; review before freezing')
    return approved


def confirm_posable():
    """Policy C and gate v4 over every primary site's retained prepared problem (`REPRESENTABILITY`): the posable set must
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
                         'planned_schedule': PLANNED, 'planned_micro_usd': ATTEMPT_MICRO_USD*sum(PLANNED.values()),
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
            'supersedes': {'cohort_policy_sha256': r6.sha(SUPERSEDED_POLICY), 'cohort_lock_sha256': r6.sha(SUPERSEDED_LOCK),
                           'reason': 'v8 accepted a restored same-activation ledger snapshot and reset consumption (R6-014 revision 2 review, finding 1); revision 9 adds a durable progress floor, with nothing model-visible changed',
                           'contract_sha256': r6.sha(PREVIOUS_CONTRACT)},
            'admission_sha256': r6.sha(admission.FROZEN), 'admission_rule': admission.RULE, 'pricing_gate_sha256': r6.sha(r6.ROOT/'pricing_gate_v4.py'),
            'site_lock_sha256': r6.sha(site_task.LOCK), 'posable_confirmation': confirm_posable(),
            'live_model_calls_authorized': sum(record['schedule'].values()) if record else 0,
            'scope': 'contract v2 on census sites; a signed revision authorizes exactly its schedule and money, within the planned design; a disabled one authorizes nothing'}


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


def atomic_write(path, data):
    """Temporary file, fsync, rename, directory fsync: a reader sees the old bytes or the new ones, never a torn file."""
    temp = path.with_name(path.name+'.tmp')
    fd = os.open(temp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o644)
    try: ledger.write_all(fd, data); os.fsync(fd)
    finally: os.close(fd)
    os.replace(temp, path); ledger.fsync_directory(path.parent)


def write_exclusive_or_equal(path, data):
    """Create `path` with exactly `data`; if an interrupted earlier call created it, it must hold exactly these bytes."""
    if path.exists():
        if path.read_bytes() != data: raise ValueError('cohort_signing_retained_bytes_conflict')
        return
    ledger.write_exclusive(path, data)


def utc_unix(stamp):
    if not (isinstance(stamp, str) and len(stamp) == 20 and stamp.endswith('Z')): raise ValueError('cohort_authorization_timestamp')
    return datetime.strptime(stamp, '%Y-%m-%dT%H:%M:%SZ').replace(tzinfo=timezone.utc).timestamp()


def within_plan(schedule):
    """An authorized schedule is a prefix of the planned draws of planned sites."""
    if not (isinstance(schedule, dict) and schedule and all(t in PLANNED and isinstance(n, int) and not isinstance(n, bool) and 1 <= n <= PLANNED[t]
                                                           for t, n in schedule.items())):
        raise ValueError('cohort_signing_outside_plan')


def block_record(approved_by, approved_utc, schedule, scope):
    return {'approved_by': approved_by, 'approved_utc': approved_utc, 'scope': scope, 'model_id': MODEL, 'schedule': dict(schedule),
            'maximum_micro_usd': ATTEMPT_MICRO_USD*sum(schedule.values()), 'maximum_presend_attempts': MAXIMUM_PRESEND_ATTEMPTS}


def fresh_capture(sources, c, now):
    """The admission rule's capture-age check, applied before any signature: a stale or future capture cannot be signed."""
    approved = c['pricing_admission']
    for role, value in v2.source_evidence(sources).items():
        age = now-value['finished_unix']
        if age < -approved['future_clock_tolerance_seconds']: raise ValueError('cohort_signing_capture_in_future')
        if age > approved['maximum_source_age_seconds']: raise ValueError('cohort_signing_capture_stale')


def approval_time(approved_utc, c, now):
    if utc_unix(approved_utc) > now+c['pricing_admission']['future_clock_tolerance_seconds']: raise ValueError('cohort_signing_approval_in_future')


def signing_complete(policy):
    digest = r6.hashlib.sha256(canonical_policy(policy)).hexdigest()
    try:
        _, rehearsal = campaign_ledger(False, policy).snapshot(); book = campaign_ledger(True, policy); _, live = book.snapshot()
        established = book.established()
    except ledger.Failure as error:
        if error.code in ('cohort_activation_authority_lost', 'cohort_ledger_rolled_back'): raise
        return False
    return rehearsal['policy_sha256'] == digest and live['policy_sha256'] == digest and established


def canonical_policy(policy):
    return v2.canonical(policy)+b'\n'


def sign(approved_by, approved_utc, schedule, sources, scope, now=None):
    """The first block. Resumable: interrupted at any boundary, the same call completes the remaining steps; a different call is refused."""
    verify_sources(); now = time.time() if now is None else now; sources = r6.Path(sources).resolve()
    within_plan(schedule); record = block_record(approved_by, approved_utc, schedule, scope)
    current = r6.read_json(CONFIG)
    campaign_ledger(True, current).established()  # revision 8: a completed activation whose ledger is gone fails closed before any write
    if current['live_enabled'] is False:
        c = config(); disabled = CONFIG.read_bytes()
        if CHECKPOINT.exists() and CHECKPOINT.read_bytes() != disabled: raise ValueError('cohort_signing_checkpoint_conflict')
        approval_time(approved_utc, c, now); fresh_capture(sources, c, now)
        signed = {**policy_record(sources, c['campaign']['id'], c['revision'], c['previous_policy_sha256'], record),
                  'signed_from_checkpoint_sha256': r6.hashlib.sha256(disabled).hexdigest()}
        ledger.authorization_scope(signed)
        live = campaign_ledger(True, signed)
        if live.head.exists():  # a completed activation (a rolled-back policy): only the identical signature may resume
            _, s = live.snapshot()
            if s['authorization'] != record or s['revisions'][0] != r6.hashlib.sha256(canonical_policy(signed)).hexdigest(): raise ValueError('cohort_signing_conflicts_with_activation')
        write_exclusive_or_equal(CHECKPOINT, disabled)
        atomic_write(CONFIG, canonical_policy(signed)); config()
    else:
        signed = current
        if signed.get('authorization') != record: raise ValueError('cohort_already_signed_for_another_scope')
        if not CHECKPOINT.exists() or r6.sha(CHECKPOINT) != signed.get('signed_from_checkpoint_sha256'): raise ValueError('cohort_signing_checkpoint_conflict')
        if signing_complete(signed): raise ValueError('cohort_already_signed')
        config()
    campaign_ledger(False, signed).ensure_registered(signed, False)
    campaign_ledger(True, signed).ensure_activated(signed, True)
    return policy_sha256()


def authorize(approved_by, approved_utc, schedule, sources, scope, reason, now=None):
    """A later block under the same campaign: a larger schedule within the plan, a new and later approval, fresh pricing; the previous
    revision is retained; consumed slots persist. Resumable like `sign`."""
    verify_sources(); now = time.time() if now is None else now; sources = r6.Path(sources).resolve()
    within_plan(schedule); record = block_record(approved_by, approved_utc, schedule, scope)
    c = config()
    if c['live_enabled'] is not True: raise ValueError('cohort_authorize_requires_signed_policy')
    ledger.require(campaign_ledger(True, c).established(), 'cohort_activation_receipt_missing')
    if c['authorization'] == record:  # resuming an interrupted authorization
        if signing_complete(c): raise ValueError('cohort_already_authorized')
        policy = c
    else:
        current = c['authorization']
        if not all(schedule.get(t, 0) >= n for t, n in current['schedule'].items()): raise ValueError('cohort_authorize_shrinks_schedule')
        if schedule == current['schedule']: raise ValueError('cohort_authorize_not_larger')
        if utc_unix(approved_utc) <= utc_unix(current['approved_utc']): raise ValueError('cohort_authorize_not_newer')
        approval_time(approved_utc, c, now); fresh_capture(sources, c, now)
        policy = {**policy_record(sources, c['campaign']['id'], c['revision']+1, policy_sha256(), record, reason),
                  'signed_from_checkpoint_sha256': c['signed_from_checkpoint_sha256']}
        ledger.authorization_scope(policy)
        write_exclusive_or_equal(CONFIG.with_name(f'{CONFIG.stem}.r{c["revision"]}.json'), CONFIG.read_bytes())
        atomic_write(CONFIG, canonical_policy(policy)); config()
    campaign_ledger(False, policy).ensure_registered(policy, False)
    campaign_ledger(True, policy).ensure_registered(policy, True)
    return policy_sha256()


def revise(sources, reason):
    """A pricing refresh: a new policy revision under the same campaign, contract and lock; the previous revision is retained;
    the campaign's ledgers register the revision, so consumed slots persist and the previous digest can no longer reserve."""
    verify_sources(); c = config(); sources = r6.Path(sources).resolve()
    if c['live_enabled']: ledger.require(campaign_ledger(True, c).established(), 'cohort_activation_receipt_missing')
    retained = CONFIG.with_name(f'{CONFIG.stem}.r{c["revision"]}.json')
    if retained.exists(): raise ValueError('Retained revision exists')
    policy = policy_record(sources, c['campaign']['id'], c['revision']+1, policy_sha256(), c['authorization'], reason)
    if 'signed_from_checkpoint_sha256' in c: policy['signed_from_checkpoint_sha256'] = c['signed_from_checkpoint_sha256']
    ledger.write_exclusive(retained, CONFIG.read_bytes()); atomic_write(CONFIG, canonical_policy(policy)); config()
    campaign_ledger(False).register_revision(policy, False)
    if policy['live_enabled']: campaign_ledger(True).register_revision(policy, True)
    return policy_sha256()


if __name__ == '__main__':
    import sys
    if sys.argv[1:2] == ['revise']: print(revise(sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else 'pricing refresh'))
    else: print(freeze(sys.argv[1] if len(sys.argv) > 1 else r6.ROOT/'sources/pricing-approved-campaign-3'))

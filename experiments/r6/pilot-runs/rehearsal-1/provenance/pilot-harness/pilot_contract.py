"""R6-007: the first policy that permits a real provider request.

Everything downstream of the wire is the reviewed R6-006 v2 machinery: the same
pricing gate and retained sources, the same credential channel, the same Farkas
consumption and independent kernel replay. This policy changes exactly four
things, and each is recorded rather than implied:

1. `live_enabled` is true, and an explicit author authorization record must be
   present and match before any live destination is used.
2. The transport reaches the real endpoint. The sandbox therefore shares the
   host network namespace for that one stage; every other stage keeps
   `--unshare-all`.
3. The client trusts the public CA bundle, pinned by digest, instead of the
   synthetic rehearsal root.
4. Attribution becomes `live_model_response`. No canned receipt is reused and no
   earlier component is relabelled.

The ledger ceiling is one attempt, not the $5 policy ceiling: a single-call
pilot should not be able to spend twice even if something retries.
"""
import json
import ssl

import admission
import credential
import priced_contract_v2 as previous
import pricing_gate_v2 as gate
import provider_contract as base_runtime
import publication
import run as r6

NAME = 'responses_live_pilot_v1'
CONFIG = r6.ROOT/'policies/responses-live-pilot-v1.json'
LOCK = r6.ROOT/'policies/pilot-harness-v1.sha256.json'
# The pilot pins the runtime it actually runs on. R6-003's pin is host- and
# time-specific; the chain to earlier policies is by source and policy hash.
RUNTIME = r6.ROOT/'policies/pilot-runtime-v1.json'
SOURCES = previous.SOURCES
PROMPT = previous.PROMPT
FILES = ('pilot_contract.py', 'pilot_https.py', 'pilot_network.py', 'pilot_budget.py',
         'pilot_episode.py', 'test_pilot.py')
MODEL = 'gpt-5.4-2026-03-05'
ENDPOINT = {'scheme': 'https', 'host': 'api.openai.com', 'port': 443, 'path': '/v1/responses'}
# One attempt's conditional reservation; see the R6-006 v2 rate basis.
ATTEMPT_MICRO_USD = 102400
PHASES = {**getattr(previous, 'PHASES', {}), 'authorization': 'authorization'}


def bundle():
    """The public trust root, resolved and pinned by digest, never by path alone."""
    path = r6.Path(ssl.get_default_verify_paths().cafile).resolve()
    raw = path.read_bytes()
    return path, {'path': str(path), 'sha256': r6.hashlib.sha256(raw).hexdigest(),
                  'bytes': len(raw), 'certificates': raw.count(b'BEGIN CERTIFICATE')}


def config():
    c = r6.read_json(CONFIG)
    if c['name'] != NAME or c['source_lock_sha256'] != r6.sha(LOCK):
        raise ValueError('Pilot policy identity changed')
    if c['previous_policy_sha256'] != r6.sha(previous.CONFIG):
        raise ValueError('Pilot dependency identity changed')
    if c['prompt_sha256'] != r6.sha(PROMPT) or c['admission_sha256'] != r6.sha(admission.FROZEN):
        raise ValueError('Pilot prompt/admission identity changed')
    if c['endpoint'] != ENDPOINT or c['model']['requested_id'] != MODEL:
        raise ValueError('Pilot endpoint/model identity changed')
    if c['limits']['total_micro_usd'] != ATTEMPT_MICRO_USD or c['limits']['campaign_attempts'] != 1:
        raise ValueError('Pilot ledger ceiling is not exactly one attempt')
    if c['runtime_lock_sha256'] != r6.sha(RUNTIME):
        raise ValueError('Pilot runtime identity changed')
    return c


def verify_runtime():
    r = r6.read_json(RUNTIME)
    if r6.sha(r6.Path(r['python'])) != r['python_sha256']: raise ValueError('Python interpreter changed')
    if any(r6.sha(r6.Path(p)) != h for p, h in r['stdlib_files'].items()): raise ValueError('Python stdlib changed')
    if any(r6.sha(r6.Path(v['host'])) != v['sha256'] for v in r['libraries']): raise ValueError('Python library changed')
    return r


def materialize_runtime():
    import shutil
    record = verify_runtime()
    root = r6.ROOT/'.cache/pilot-runtime'/r6.sha(RUNTIME)/'stdlib'
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


def runtime_divergence(record):
    """How this pin differs from R6-003's, stated rather than hidden."""
    earlier = r6.read_json(base_runtime.RUNTIME)
    before = {v['guest']: v['sha256'] for v in earlier['libraries']}
    after = {v['guest']: v['sha256'] for v in record['libraries']}
    return {'previous_runtime_sha256': r6.sha(base_runtime.RUNTIME),
            'python_unchanged': earlier['python_sha256'] == record['python_sha256'],
            'stdlib_unchanged': earlier['stdlib_files'] == record['stdlib_files'],
            'libraries_removed': sorted(set(before)-set(after)), 'libraries_added': sorted(set(after)-set(before)),
            'libraries_changed': sorted(k for k in before.keys() & after.keys() if before[k] != after[k])}


def source_lock():
    values = r6.read_json(LOCK)
    if set(values) != set(FILES): raise ValueError('Pilot source inventory changed')
    config()
    return values


def verify_sources():
    previous.verify_sources()
    if any(r6.sha(r6.ROOT/p) != h for p, h in source_lock().items()):
        raise ValueError('Pilot policy requires its frozen source revision')


def authorization(c):
    """A live destination needs a present, complete author authorization."""
    record = c.get('authorization')
    required = {'approved_by', 'approved_utc', 'scope', 'maximum_attempts', 'maximum_micro_usd', 'model_id'}
    if not isinstance(record, dict) or set(record) != required:
        raise ValueError('pilot_authorization_absent')
    if record['maximum_attempts'] != 1 or record['maximum_micro_usd'] != ATTEMPT_MICRO_USD:
        raise ValueError('pilot_authorization_scope')
    if record['model_id'] != MODEL or not str(record['approved_by']).strip():
        raise ValueError('pilot_authorization_subject')
    return record


def live_permitted(c):
    """Live transport requires the flag and the authorization together."""
    if c['live_enabled'] is not True: raise ValueError('pilot_live_disabled')
    return authorization(c)


def freeze(approved_by=None, approved_utc=None):
    if any(p.exists() for p in (CONFIG, LOCK, RUNTIME)): raise ValueError('Pilot policy is already frozen')
    previous.verify_sources(); admission.verify()
    _, ca = bundle()
    runtime = base_runtime.runtime_record()
    with RUNTIME.open('x') as f:
        f.write(json.dumps(runtime, indent=2)+'\n')
    with LOCK.open('x') as f:
        f.write(json.dumps({p: r6.sha(r6.ROOT/p) for p in FILES}, indent=2)+'\n')
    record = None if approved_by is None else {
        'approved_by': approved_by, 'approved_utc': approved_utc, 'model_id': MODEL,
        'maximum_attempts': 1, 'maximum_micro_usd': ATTEMPT_MICRO_USD,
        'scope': 'one provider request for the D1/70 arithmetic obligation; no campaign, no second attempt'}
    policy = {
            'schema_version': 'r6-live-pilot-policy-1', 'name': NAME,
            'provider_api': 'OpenAI Responses', 'transport': 'python_stdlib_https_client',
            'mode': 'provider_request', 'endpoint': ENDPOINT,
            'live_enabled': record is not None, 'authorization': record,
            'selection_status': 'author-signed dated snapshot; provider availability untested',
            'model': {'requested_id': MODEL, 'allowed_response_ids': [MODEL],
                      'model_computation_attested': False,
                      'revision_status': 'documented dated provider snapshot; not a model-content hash '
                                         'or an attestation that the returned text came from it'},
            'sampling': {'reasoning_effort': 'medium', 'service_tier': 'default',
                         'temperature': None, 'top_p': None, 'seed': None,
                         'scope': 'omitted sampling controls are not a determinism claim'},
            'network': {'sandbox': 'proposal stage shares the host network namespace; every other stage '
                                   'keeps --unshare-all',
                        'intended_destination': ENDPOINT, 'egress_restriction_enforced_by_harness': False,
                        'scope': 'the namespace is shared, not filtered; destination control is the '
                                 'endpoint allowlist and the audited command, not a network policy'},
            'tls': {'minimum_version': 'TLSv1.2', 'verify_mode': 'CERT_REQUIRED', 'check_hostname': True,
                    'alpn': ['http/1.1'], 'public_ca_bundle': ca},
            'credential': {'channel': 'private_read_only_file', 'guest_path': '/credential',
                           'operator_supplied': True, 'retained': False,
                           'scope': 'the operator supplies the file path; the harness never reads an '
                                    'environment credential and never copies the value into the run'},
            'attribution': {'witness_proposer': 'live_model_response',
                            'certificate_assembler': 'sdk_proposal_assembler_v1',
                            'scope': 'new proposer identity; no canned or earlier receipt is reused'},
            'request': r6.read_json(previous.CONFIG)['request'],
            'limits': {**r6.read_json(previous.CONFIG)['limits'],
                       'attempts_per_episode': 1, 'campaign_attempts': 1, 'automatic_retries': 0,
                       'redirects': 0, 'total_micro_usd': ATTEMPT_MICRO_USD},
            'pricing': r6.read_json(previous.CONFIG)['pricing'],
            'pricing_admission': r6.read_json(previous.CONFIG)['pricing_admission'],
            'publication_scan_version': publication.VERSION,
            'canary_derivation': credential.DOMAIN,
            'prompt_sha256': r6.sha(PROMPT), 'source_lock_sha256': r6.sha(LOCK),
            'runtime_lock_sha256': r6.sha(RUNTIME), 'runtime_divergence': runtime_divergence(runtime),
            'previous_policy_sha256': r6.sha(previous.CONFIG),
            'previous_source_lock_sha256': r6.sha(previous.LOCK),
            'admission_sha256': r6.sha(admission.FROZEN), 'admission_rule': admission.RULE,
            'pricing_gate_sha256': r6.sha(r6.ROOT/'pricing_gate_v2.py'),
            'live_model_calls_authorized': 1 if record else 0,
            'scope': 'one canned-rehearsed provider request; no capability, benchmark or reliability '
                     'claim follows from a single attempt'}
    # Canonical bytes: the frozen gate binds requests to sha(canonical(policy)+'\\n').
    with CONFIG.open('xb') as f:
        f.write(gate.canonical(policy)+b'\n')


if __name__ == '__main__':
    import sys
    freeze(*(sys.argv[1:3] or [None, None]))

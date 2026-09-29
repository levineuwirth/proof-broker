"""R6-008 v7: the executing guards the pilot lacked, under a new policy.

The pilot's live result stands; its harness was reviewed and found wanting in
six places. This policy repairs the executing ones, each as a recorded change:

1. The allowance is per *authorization*, not per run directory. One ledger,
   `ledgers/live/<policy_sha256>.ndjson`, activated when the author signs,
   counts transmissions: a durable single-use send grant, committed with
   O_EXCL into the reservation's authoritative slot beside the ledger,
   consumes the slot before the first header byte; a release returns it only
   for a pre-send failure whose sender termination is established by
   validated supervisor evidence; anything else stays consumed. Activation
   records its purpose and the exact authorization it serves, so a rehearsal
   ledger for the same bytes is inadmissible to live mode.
2. The full authorization scope is one function, `campaign_ledger.
   authorization_scope`, run by the host and again by the actor.
3. The actor's credential read sits inside its exception boundary; a format
   failure is a classified record, not a traceback.
4. Interpretation checks `serialized == outbound` locally; remote receipt is
   recorded as unobservable. Attempt and transmission counters are separate.
5. Proposer provenance passes through the consumer; the supervisor alone owns
   stage receipts.
6. Every stage failure finalizes: scan, terminal event, seal. A commitment to
   the credential actually sent is recorded at the handoff, so an operator
   scan can be bound to it and to the sealed inventory. In live mode the
   synthetic-canary scan is reported as what it is, not as a real-credential
   admission gate.

This checkpoint is canned: `live_enabled` is false and no authorization
exists until the author signs a policy, which activates its ledger.
"""
import json
import ssl

import admission
import campaign_ledger as ledger
import credential
import pilot_contract as previous
import pricing_gate_v2 as gate
import provider_contract as base_runtime
import publication
import run as r6

NAME = 'responses_campaign_v7'
CONFIG = r6.ROOT/'policies/responses-campaign-v7.json'
CHECKPOINT = r6.ROOT/'policies/responses-campaign-v7.checkpoint.json'
LOCK = r6.ROOT/'policies/campaign-harness-v7.sha256.json'
RUNTIME = r6.ROOT/'policies/campaign-runtime-v1.json'
LEDGERS = r6.ROOT/'ledgers'
# A fresh capture for signing: reviewed by diff against the pilot's approved extracts (see pinned_admission).
SOURCES = r6.ROOT/'sources/pricing-approved-campaign-1'
PROMPT = previous.PROMPT
FILES = ('campaign_contract.py', 'campaign_ledger.py', 'campaign_https.py', 'campaign_network.py',
         'campaign_budget.py', 'campaign_episode.py', 'test_campaign.py')
MODEL = previous.MODEL
ENDPOINT = previous.ENDPOINT
ATTEMPT_MICRO_USD = previous.ATTEMPT_MICRO_USD
MAXIMUM_TRANSMISSIONS = 1
MAXIMUM_PRESEND_ATTEMPTS = 3
COMMITMENT_DOMAIN = 'r6-campaign-credential-commitment-1'
PHASES = {**previous.PHASES, 'campaign-ledger': 'campaign_ledger'}

bundle = previous.bundle


def policy_sha256():
    return r6.sha(CONFIG)


def config():
    c = r6.read_json(CONFIG)
    if c['name'] != NAME or c['source_lock_sha256'] != r6.sha(LOCK):
        raise ValueError('Campaign policy identity changed')
    if c['previous_policy_sha256'] != r6.sha(previous.CONFIG):
        raise ValueError('Campaign dependency identity changed')
    if c['prompt_sha256'] != r6.sha(PROMPT) or c['admission_sha256'] != r6.sha(admission.FROZEN):
        raise ValueError('Campaign prompt/admission identity changed')
    if c['endpoint'] != ENDPOINT or c['model']['requested_id'] != MODEL:
        raise ValueError('Campaign endpoint/model identity changed')
    if c['limits']['maximum_transmissions'] != MAXIMUM_TRANSMISSIONS or c['limits']['total_micro_usd'] != ATTEMPT_MICRO_USD:
        raise ValueError('Campaign allowance is not one transmission')
    if c['runtime_lock_sha256'] != r6.sha(RUNTIME):
        raise ValueError('Campaign runtime identity changed')
    if CONFIG.read_bytes() != gate.canonical(c)+b'\n':
        raise ValueError('Campaign policy is not in canonical form')
    return c


def _runtime_record():
    r = r6.read_json(RUNTIME)
    if r6.sha(r6.Path(r['python'])) != r['python_sha256']: raise ValueError('Python interpreter changed')
    if any(r6.sha(r6.Path(p)) != h for p, h in r['stdlib_files'].items()): raise ValueError('Python stdlib changed')
    if any(r6.sha(r6.Path(v['host'])) != v['sha256'] for v in r['libraries']): raise ValueError('Python library changed')
    return r


def materialize_runtime():
    import shutil
    record = _runtime_record()
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


def source_lock():
    values = r6.read_json(LOCK)
    if set(values) != set(FILES): raise ValueError('Campaign source inventory changed')
    config()
    return values


def verify_sources():
    previous.verify_sources()
    if any(r6.sha(r6.ROOT/p) != h for p, h in source_lock().items()):
        raise ValueError('Campaign policy requires its frozen source revision')


def authorization(c):
    """Host side: the same function the actor runs."""
    return ledger.authorization_scope(c)


REHEARSAL_AUTHORIZATION = {'approved_by': 'rehearsal', 'approved_utc': '1970-01-01T00:00:00Z', 'model_id': MODEL,
                           'maximum_transmissions': 64, 'maximum_micro_usd': 64*ATTEMPT_MICRO_USD, 'maximum_presend_attempts': 64,
                           'scope': 'loopback rehearsals only; no provider transmission is possible on this ledger'}


def live_permitted(c):
    record = authorization(c)
    _, s = campaign_ledger(True).snapshot()  # activated, not truncated, chain valid
    ledger.check_activation(s, c, True)      # and serving exactly this authorization
    return record, s


def campaign_ledger(live):
    """Live runs share the authorization's ledger; rehearsals share a separate one that never funds a transmission."""
    return ledger.Ledger(LEDGERS/('live' if live else 'rehearsal'), policy_sha256())


def freeze(approved_by=None, approved_utc=None):
    """Freeze the policy; signing also activates its ledger, and only then."""
    if CONFIG.exists() or LOCK.exists(): raise ValueError('Campaign policy is already frozen')
    previous.verify_sources(); admission.verify()
    _, ca = bundle()
    if RUNTIME.exists():
        runtime = _runtime_record()  # the v1 pin, re-verified against this host rather than re-recorded
    else:
        runtime = base_runtime.runtime_record()
        with RUNTIME.open('x') as f:
            f.write(json.dumps(runtime, indent=2)+'\n')
    with LOCK.open('x') as f:
        f.write(json.dumps({p: r6.sha(r6.ROOT/p) for p in FILES}, indent=2)+'\n')
    record = None if approved_by is None else {
        'approved_by': approved_by, 'approved_utc': approved_utc, 'model_id': MODEL,
        'maximum_transmissions': MAXIMUM_TRANSMISSIONS, 'maximum_micro_usd': ATTEMPT_MICRO_USD,
        'maximum_presend_attempts': MAXIMUM_PRESEND_ATTEMPTS,
        'scope': 'one provider transmission for the D1/70 arithmetic obligation under one shared ledger'}
    earlier = r6.read_json(previous.CONFIG)
    policy = {
        'schema_version': 'r6-campaign-policy-1', 'name': NAME,
        'provider_api': earlier['provider_api'], 'transport': earlier['transport'], 'mode': 'provider_request',
        'endpoint': ENDPOINT, 'live_enabled': record is not None, 'authorization': record,
        'ledger': {'directory': 'ledgers/live', 'rehearsal_directory': 'ledgers/rehearsal', 'file': '<policy_sha256>.ndjson',
                   'slots': '<policy_sha256>.slots/<reservation_id>', 'domain': ledger.DOMAIN,
                   'counts': 'transmissions', 'grant': 'O_EXCL single-use send grant in the authoritative slot before the first header byte',
                   'release': 'only a pre-send failure with sender termination established by validated supervisor evidence',
                   'ambiguity': 'consumed; send_outcome_unknown is recorded, not a delivery claim',
                   'activation': 'at signing, by the author, with purpose and the exact authorization served; a changed policy has no ledger',
                   'rehearsal_authorization': REHEARSAL_AUTHORIZATION,
                   'scope': 'protects against harness errors in trusted local state; not against operator rollback'},
        'model': earlier['model'], 'sampling': earlier['sampling'], 'network': earlier['network'],
        'tls': {**earlier['tls'], 'public_ca_bundle': ca},
        'credential': {**earlier['credential'],
                       'commitment': {'domain': COMMITMENT_DOMAIN, 'form': 'sha256(domain:nonce:authorization_header)',
                                      'scope': 'recorded at the handoff so an operator scan can be bound to the value sent'}},
        'attribution': {'witness_proposer': 'live_model_response', 'rehearsal_witness_proposer': 'canned_provider_response',
                        'certificate_assembler': 'sdk_proposal_assembler_v1',
                        'consumer': 'provider_episode.consume (R6-003) with proposer and route passed through',
                        'scope': 'attribution names the observed proposer in every receipt; no canned label is reused for a live witness'},
        'request': earlier['request'],
        'limits': {**{k: v for k, v in earlier['limits'].items() if k != 'campaign_attempts'},
                   'attempts_per_episode': 1, 'automatic_retries': 0, 'redirects': 0,
                   'maximum_transmissions': MAXIMUM_TRANSMISSIONS, 'maximum_presend_attempts': MAXIMUM_PRESEND_ATTEMPTS,
                   'total_micro_usd': ATTEMPT_MICRO_USD},
        'pricing': earlier['pricing'], 'pricing_admission': pinned_admission(),
        'publication': {'scan_version': publication.VERSION, 'canary_derivation': credential.DOMAIN,
                        'live_mode': 'synthetic-canary scan reported as pending_operator_scan; real-credential admission is the operator scan bound to the commitment and the seal'},
        'prompt_sha256': r6.sha(PROMPT), 'source_lock_sha256': r6.sha(LOCK),
        'runtime_lock_sha256': r6.sha(RUNTIME), 'runtime_divergence': previous.runtime_divergence(runtime),
        'previous_policy_sha256': r6.sha(previous.CONFIG), 'previous_source_lock_sha256': r6.sha(previous.LOCK),
        'admission_sha256': r6.sha(admission.FROZEN), 'admission_rule': admission.RULE,
        'pricing_gate_sha256': r6.sha(r6.ROOT/'pricing_gate_v2.py'),
        'live_model_calls_authorized': MAXIMUM_TRANSMISSIONS if record else 0,
        'scope': 'guard repairs under a canned checkpoint; a signed copy authorizes one transmission and nothing about capability'}
    with CONFIG.open('xb') as f:
        f.write(gate.canonical(policy)+b'\n')
    campaign_ledger(False).activate(REHEARSAL_AUTHORIZATION, 'rehearsal')
    if record is not None:
        ledger.authorization_scope(policy)
        campaign_ledger(True).activate(record, 'live')


def pinned_admission():
    """The pilot's admission rules over this policy's own fresh capture, with the review recorded."""
    approved = json.loads(json.dumps(r6.read_json(previous.CONFIG)['pricing_admission']))
    evidence = gate.source_evidence(SOURCES)
    earlier = r6.read_json(previous.CONFIG)['pricing_admission']['sources']
    approved['sources'] = {role: {'raw_sha256': v['raw_sha256'], 'extract_sha256': v['extract_sha256']} for role, v in evidence.items()}
    approved['source_review'] = {
        'previous_approved': earlier, 'capture': str(SOURCES.relative_to(r6.ROOT)),
        'model_extract_identical_to_previous': evidence['model']['extract_sha256'] == earlier['model']['extract_sha256'],
        'caching_extract_identical_to_previous': evidence['caching']['extract_sha256'] == earlier['caching']['extract_sha256'],
        'rates_identical_to_previous': gate.rates_from(evidence) == r6.read_json(previous.CONFIG)['pricing']['nano_usd_per_token'],
        'scope': 'a fresh capture within the 24-hour admission window; both extracts byte-identical to the pilot approval; raw pages differ'}
    if not (approved['source_review']['model_extract_identical_to_previous'] and approved['source_review']['caching_extract_identical_to_previous']
            and approved['source_review']['rates_identical_to_previous']):
        raise ValueError('Campaign pricing capture differs semantically from the approved extracts; review before freezing')
    return approved


def sign(approved_by, approved_utc):
    """The reviewed lifecycle step: the disabled checkpoint is retained byte-for-byte, the signed policy
    replaces it under the same lock, and only then do a live ledger and a rehearsal ledger exist for it."""
    verify_sources()
    c = config()
    if c['live_enabled'] is not False or c['authorization'] is not None: raise ValueError('Campaign policy is already signed')
    if CHECKPOINT.exists(): raise ValueError('Campaign checkpoint copy already exists')
    record = {'approved_by': approved_by, 'approved_utc': approved_utc, 'model_id': MODEL,
              'maximum_transmissions': MAXIMUM_TRANSMISSIONS, 'maximum_micro_usd': ATTEMPT_MICRO_USD,
              'maximum_presend_attempts': MAXIMUM_PRESEND_ATTEMPTS,
              'scope': 'one provider transmission for the D1/70 arithmetic obligation under one shared ledger'}
    signed = {**c, 'live_enabled': True, 'authorization': record, 'live_model_calls_authorized': MAXIMUM_TRANSMISSIONS,
              'signed_from_checkpoint_sha256': r6.sha(CONFIG)}
    ledger.authorization_scope(signed)
    disabled = CONFIG.read_bytes()
    with CHECKPOINT.open('xb') as f: f.write(disabled)
    CONFIG.write_bytes(gate.canonical(signed)+b'\n')
    config()
    campaign_ledger(True).activate(record, 'live')
    campaign_ledger(False).activate(REHEARSAL_AUTHORIZATION, 'rehearsal')
    return policy_sha256()


if __name__ == '__main__':
    import sys
    if sys.argv[1:2] == ['sign']: print(sign(*sys.argv[2:4]))
    else: freeze(*(sys.argv[1:3] or [None, None]))

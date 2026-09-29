"""R6-004: a credential-channel policy over immutable R6-001/2/3 dependencies.

Version 3 is the second review-corrected revision; v1 and v2 stay on disk as
reviewed records and are not the policy any new episode runs under.

The credential mount contract and receipt format change, so the adapter and
auditor are versioned with their own policy and source lock. The pinned Python
runtime, the frozen prompt/request contract and the shared proof checker are
reused by hash, not copied.
"""
import json

import admission
import credential
import provider_contract as previous
import publication
import run as r6

NAME = 'credential_http_fixture_v3'
CONFIG = r6.ROOT/'policies/credential-http-v3.json'
LOCK = r6.ROOT/'policies/credential-harness-v3.sha256.json'
PROMPT = previous.PROMPT
RUNTIME = previous.RUNTIME
MODEL = previous.MODEL
FIXTURES = previous.FIXTURES
FILES = ('credential.py', 'publication.py', 'credential_contract.py', 'credential_http.py',
         'credential_episode.py', 'credential_audit.py', 'test_credentials.py',
         'schema/credential-verdict.schema.json')
PHASES = {**previous.PHASES, 'credential-receipt': 'credential', 'publication': 'publication'}
RETAINED_SOURCES = previous.RETAINED_SOURCES | {'provenance/credential-harness/credential_http.py'}
GUEST_CREDENTIAL = '/credential'


def development(directory):
    """Versioned disposable locks for development; never overwrite a freeze."""
    global CONFIG, LOCK
    directory = r6.Path(directory).resolve()
    if not directory.is_relative_to(r6.ROOT/'.cache'):
        raise ValueError('Development policies must stay inside the ignored R6 cache')
    previous.development(directory)
    directory.mkdir(parents=True, exist_ok=True)
    CONFIG, LOCK = directory/CONFIG.name, directory/LOCK.name
    globals()['RUNTIME'] = previous.RUNTIME
    if not CONFIG.exists(): freeze()


def config():
    c = r6.read_json(CONFIG)
    if c['name'] != NAME or c['source_lock_sha256'] != r6.sha(LOCK): raise ValueError('Credential policy identity changed')
    if c['previous_policy_sha256'] != r6.sha(previous.CONFIG) or c['previous_source_lock_sha256'] != r6.sha(previous.LOCK):
        raise ValueError('Credential policy dependency identity changed')
    if c['prompt_sha256'] != r6.sha(PROMPT) or c['runtime_lock_sha256'] != r6.sha(RUNTIME):
        raise ValueError('Credential prompt/runtime identity changed')
    if c['shared_proof_checker_sha256'] != previous.config()['shared_proof_checker_sha256']:
        raise ValueError('Shared proof checker changed')
    if c['admission_sha256'] != r6.sha(admission.FROZEN): raise ValueError('Admission changed')
    if (c['publication_scan_version'] != publication.VERSION
            or c['publication_representations'] != list(publication.REPRESENTATIONS)
            or c['publication_encoded_forms'] != list(publication.FORMS)
            or c['publication_decompression_limit_bytes'] != publication.LIMIT
            or c['finalization_order'] != list(publication.FINALIZATION)):
        raise ValueError('Frozen publication coverage differs from the scanner')
    return c


def source_lock():
    values = r6.read_json(LOCK)
    if set(values) != set(FILES): raise ValueError('Credential source inventory changed')
    config()
    return values


def verify_sources():
    previous.verify_sources()
    if any(r6.sha(r6.ROOT/p) != h for p, h in source_lock().items()):
        raise ValueError('Credential policy requires its frozen source revision')


def freeze():
    if any(p.exists() for p in (CONFIG, LOCK)): raise ValueError('Credential policy is already frozen')
    previous.verify_sources(); admission.verify()
    with LOCK.open('x') as f: f.write(json.dumps({p: r6.sha(r6.ROOT/p) for p in FILES}, indent=2)+'\n')
    with CONFIG.open('x') as f: f.write(json.dumps({
        'schema_version': 'r6-credential-policy-3', 'name': NAME,
        'provider_api': 'OpenAI Responses', 'transport': 'python_stdlib_http_client', 'provider_sdk': None,
        'mode': 'isolated_loopback_http_fixture', 'live_endpoint': None, 'model_revision': None,
        'wire_model': MODEL, 'sampling_settings': None, 'live_spending_limit': None,
        'credential_channel': 'private_read_only_file', 'credential_guest_path': GUEST_CREDENTIAL,
        'credential_in_argv': False, 'credential_in_environment': False, 'credential_retained': False,
        'canary_derivation': credential.DOMAIN, 'canary_tag': credential.TAG,
        'receipt_evidence': 'endpoint_digest_of_incoming_authorization_header',
        'publication_scan_version': publication.VERSION,
        'publication_representations': list(publication.REPRESENTATIONS),
        'publication_encoded_forms': list(publication.FORMS),
        'publication_decompression_limit_bytes': publication.LIMIT,
        'publication_symlink_policy': 'rejected_never_followed',
        'publication_non_regular_entry_policy': 'rejected',
        'publication_unenumerable_directory_policy': 'rejects_publication',
        'publication_unreadable_artifact_policy': 'rejects_publication',
        'publication_canary_bearing_path_policy': 'reported_by_digest_and_treated_as_disclosure',
        'publication_exemptions': [], 'finalization_order': list(publication.FINALIZATION),
        'publication_acceptance_is_separate': True,
        'prompt_sha256': r6.sha(PROMPT), 'source_lock_sha256': r6.sha(LOCK),
        'runtime_lock_sha256': r6.sha(RUNTIME), 'previous_policy_sha256': r6.sha(previous.CONFIG),
        'previous_source_lock_sha256': r6.sha(previous.LOCK),
        'shared_proof_checker_sha256': previous.config()['shared_proof_checker_sha256'],
        'admission_sha256': r6.sha(admission.FROZEN), 'admission_rule': admission.RULE,
        'context_policy': 'farkas_lia_le_eq_only_v1', 'allowed_relations': ['le', 'eq'],
        'attempt_limit': 1, 'automatic_retries': 0, 'follow_redirects': False, 'fallback_routes': [],
        'request_wall_seconds': 12, 'request_cpu_seconds': 5, 'request_memory_bytes': 384*1024**2,
        'request_output_bytes': 4*1024**2, 'maximum_request_bytes': 1024**2,
        'maximum_provider_response_bytes': 256*1024, 'maximum_response_bytes': 131072,
        'http_timeout_seconds': 1, 'max_output_tokens': 256,
        'witness_proposer': 'canned_provider_response', 'certificate_assembler': 'sdk_proposal_assembler_v1',
        'certificate_backend': 'r6_fixture_witness', 'certificate_type': 'farkas', 'trust_tier': 1,
        'phase_mapping': PHASES, 'live_model_calls': 0, 'live_model_cost_usd': 0,
        'preparation_closer': 'frozen_human_omega'}, indent=2)+'\n')


if __name__ == '__main__': freeze()

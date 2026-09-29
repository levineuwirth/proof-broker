"""R6-002 policy identity; R6-001 sources and policy are immutable dependencies."""
import json

import admission
import proposal_instrument as downstream
import run as r6

POLICY = 'canned_envelope_v1'
CONFIG = r6.ROOT/'policies/canned-envelope-v1.json'
LOCK = r6.ROOT/'policies/canned-envelope-harness-v1.sha256.json'
PROMPT = r6.ROOT/'prompts/farkas-rows-v1.txt'
FILES = ('envelope_contract.py', 'envelope_payload.py', 'envelope_episode.py', 'envelope_audit.py',
         'envelope_proof_audit.py', 'test_envelopes.py', 'validate/envelope_receiver.c',
         'schema/envelope-request.schema.json', 'schema/envelope-verdict.schema.json',
         'prompts/farkas-rows-v1.txt')
RETAINED_SOURCES = downstream.RETAINED_SOURCES | {'provenance/envelope-harness/validate/envelope_receiver.c'}
FIXTURES = {r6.D1.id: ('hZ', '6'), r6.C8.id: ('hhi', '786432')}
PHASES = {'preparation-build': 'preparation', 'preparation': 'preparation', 'pipeline-prepare': 'preparation',
    'context-admission': 'admission', 'payload': 'preparation', 'proposal': 'proposal', 'proposal-1': 'proposal',
    'response-decode': 'proposal', 'response-binding': 'proposal', 'envelope-audit': 'proposal',
    'assembly': 'certificate_assembly', 'certificate-check': 'certificate_verification',
    'capture-build': 'reconstruction', 'reconstruct': 'reconstruction', 'export': 'proof_export',
    'validation-local': 'final_validation', 'validation-whole': 'final_validation', 'harness': 'harness'}


def config():
    value = r6.read_json(CONFIG)
    if value['name'] != POLICY or value['prompt_sha256'] != r6.sha(PROMPT):
        raise ValueError('Frozen envelope policy/prompt identity changed')
    if value['admission_sha256'] != r6.sha(admission.FROZEN):
        raise ValueError('Frozen admission identity changed')
    if value['downstream_source_lock_sha256'] != r6.sha(downstream.SOURCE_LOCK):
        raise ValueError('Frozen downstream source identity changed')
    return value


def source_lock():
    values = r6.read_json(LOCK)
    if set(values) != set(FILES) or config()['source_lock_sha256'] != r6.sha(LOCK):
        raise ValueError('Frozen envelope source inventory changed')
    return values


def verify_live_sources():
    downstream.verify_live_sources()
    if any(r6.sha(r6.ROOT/name) != digest for name, digest in source_lock().items()):
        raise ValueError('Envelope v1 requires its frozen source revision')


def freeze():
    if CONFIG.exists() or LOCK.exists():
        raise ValueError('Envelope policy is already frozen')
    admission.verify()
    lock = {name: r6.sha(r6.ROOT/name) for name in FILES}
    with LOCK.open('x') as f:
        f.write(json.dumps(lock, indent=2)+'\n')
    policy = {'schema_version': 'r6-canned-envelope-policy-1', 'name': POLICY,
        'transport': 'isolated_local_file_receiver', 'provider': None, 'model_revision': None,
        'context_policy': 'farkas_rows_only_v1', 'prompt_sha256': r6.sha(PROMPT),
        'source_lock_sha256': r6.sha(LOCK), 'downstream_source_lock_sha256': r6.sha(downstream.SOURCE_LOCK),
        'admission_sha256': r6.sha(admission.FROZEN), 'admission_rule': admission.RULE,
        'witness_proposer': 'canned_response', 'certificate_assembler': 'sdk_proposal_assembler_v1',
        'certificate_backend': 'r6_fixture_witness', 'certificate_type': 'farkas', 'trust_tier': 1,
        'attempt_limit': 1, 'fallback_routes': [], 'automatic_retries': 0,
        'request_wall_seconds': 2, 'request_cpu_seconds': 1, 'request_memory_bytes': 192*1024**2,
        'request_output_bytes': 1024**2, 'maximum_request_bytes': 1024**2, 'maximum_response_bytes': 131072,
        'maximum_support': 32, 'maximum_coefficient_characters': 128,
        'serializer': 'local_json_messages_v1', 'response_usage': 'unreported_is_null',
        'live_model_calls': 0, 'live_model_cost_usd': 0,
        'phase_mapping': PHASES, 'preparation_closer': 'frozen_human_omega'}
    with CONFIG.open('x') as f:
        f.write(json.dumps(policy, indent=2)+'\n')


if __name__ == '__main__':
    freeze()

"""R6-003: a new policy with immutable R6-001/R6-002 dependencies."""
import hashlib
import json
from pathlib import Path
import sys
import sysconfig
import shutil

import admission
import envelope_contract as previous
import episode
import run as r6

NAME = 'openai_responses_http_fixture_v1'
CONFIG = r6.ROOT/'policies/openai-responses-http-v1.json'
LOCK = r6.ROOT/'policies/provider-harness-v1.sha256.json'
RUNTIME = r6.ROOT/'policies/provider-runtime-v1.json'
PROMPT = r6.ROOT/'prompts/farkas-lia-v1.txt'
FILES = ('provider_contract.py', 'provider_payload.py', 'provider_http.py', 'provider_episode.py',
         'provider_audit.py', 'test_provider.py', 'schema/provider-request.schema.json',
         'schema/provider-verdict.schema.json', 'prompts/farkas-lia-v1.txt')
MODEL = 'r6-canned-model-not-a-live-selection'
FIXTURES = {r6.D1.id: ('hZ', '8'), r6.C8.id: ('hhi', '1048576')}
PHASES = {**previous.PHASES, 'provider-response': 'proposal', 'provider-admission': 'admission'}
RETAINED_SOURCES = previous.RETAINED_SOURCES


def dump(path, value):
    with path.open('x') as f: f.write(json.dumps(value, indent=2)+'\n')


def development(directory):
    """Versioned disposable locks for development; never overwrite a freeze."""
    global CONFIG, LOCK, RUNTIME
    directory = Path(directory).resolve()
    if not directory.is_relative_to(r6.ROOT/'.cache'):
        raise ValueError('Development policies must stay inside the ignored R6 cache')
    directory.mkdir(parents=True, exist_ok=True)
    CONFIG, LOCK, RUNTIME = [directory/p.name for p in (CONFIG, LOCK, RUNTIME)]
    if not CONFIG.exists(): freeze()


def runtime_record():
    stdlib = Path(sysconfig.get_path('stdlib'))
    files = {str(p): r6.sha(p) for p in sorted(stdlib.rglob('*')) if p.is_file()
             and not {'__pycache__', 'site-packages', 'dist-packages'} & set(p.relative_to(stdlib).parts)
             and p.suffix in {'.py', '.so'}}
    extensions = sorted(p for p in files if p.endswith('.so'))
    libs = set(episode.libraries(Path(sys.executable)))
    for p in extensions: libs.update(episode.libraries(Path(p)))
    libraries = [{'host': str(p.resolve()), 'guest': str(p), 'sha256': r6.sha(p)} for p in sorted(libs)]
    return {'python': str(Path(sys.executable).resolve()), 'python_sha256': r6.sha(Path(sys.executable)),
        'version': sys.version, 'stdlib': str(stdlib), 'stdlib_files': files,
        'extension_binaries': extensions, 'libraries': libraries,
        'scope': 'pinned interpreter, stdlib sources/extensions and ELF dependencies; no compilation attestation'}


def config():
    c = r6.read_json(CONFIG)
    if c['name'] != NAME or c['prompt_sha256'] != r6.sha(PROMPT) or c['source_lock_sha256'] != r6.sha(LOCK):
        raise ValueError('Provider policy/source/prompt identity changed')
    if c['runtime_lock_sha256'] != r6.sha(RUNTIME) or c['previous_policy_sha256'] != r6.sha(previous.CONFIG):
        raise ValueError('Provider runtime/downstream identity changed')
    if c['previous_source_lock_sha256'] != r6.sha(previous.LOCK) or c['shared_proof_checker_sha256'] != previous.source_lock()['envelope_proof_audit.py']:
        raise ValueError('Shared proof checker/dependency lock changed')
    if c['admission_sha256'] != r6.sha(admission.FROZEN): raise ValueError('Admission changed')
    return c


def source_lock():
    values = r6.read_json(LOCK)
    if set(values) != set(FILES): raise ValueError('Provider source inventory changed')
    config()
    return values


def verify_sources():
    previous.verify_live_sources()
    if any(r6.sha(r6.ROOT/p) != h for p, h in source_lock().items()):
        raise ValueError('Provider policy requires its frozen source revision')


def verify_runtime():
    r = r6.read_json(RUNTIME)
    if r6.sha(Path(r['python'])) != r['python_sha256']: raise ValueError('Python interpreter changed')
    if any(r6.sha(Path(p)) != h for p, h in r['stdlib_files'].items()): raise ValueError('Python stdlib changed')
    if any(r6.sha(Path(v['host'])) != v['sha256'] for v in r['libraries']): raise ValueError('Python library changed')
    return r


def materialize_runtime():
    record = verify_runtime()
    root = r6.ROOT/'.cache/provider-runtime'/r6.sha(RUNTIME)/'stdlib'
    original = Path(record['stdlib'])
    wanted = {str(Path(p).relative_to(original)): h for p, h in record['stdlib_files'].items()}
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


def freeze():
    if any(p.exists() for p in (CONFIG, LOCK, RUNTIME)): raise ValueError('Provider policy is already frozen')
    previous.verify_live_sources(); admission.verify()
    runtime = runtime_record()
    dump(RUNTIME, runtime)
    dump(LOCK, {p: r6.sha(r6.ROOT/p) for p in FILES})
    dump(CONFIG, {'schema_version': 'r6-provider-policy-1', 'name': NAME,
        'provider_api': 'OpenAI Responses', 'transport': 'python_stdlib_http_client', 'provider_sdk': None,
        'mode': 'isolated_loopback_http_fixture', 'live_endpoint': None, 'model_revision': None,
        'wire_model': MODEL, 'sampling_settings': None, 'live_spending_limit': None,
        'context_policy': 'farkas_lia_le_eq_only_v1', 'allowed_relations': ['le', 'eq'],
        'prompt_sha256': r6.sha(PROMPT), 'source_lock_sha256': r6.sha(LOCK), 'runtime_lock_sha256': r6.sha(RUNTIME),
        'previous_policy_sha256': r6.sha(previous.CONFIG), 'previous_source_lock_sha256': r6.sha(previous.LOCK),
        'shared_proof_checker_sha256': r6.sha(r6.ROOT/'envelope_proof_audit.py'),
        'admission_sha256': r6.sha(admission.FROZEN), 'admission_rule': admission.RULE,
        'attempt_limit': 1, 'automatic_retries': 0, 'follow_redirects': False, 'fallback_routes': [],
        'request_wall_seconds': 12, 'request_cpu_seconds': 5, 'request_memory_bytes': 384*1024**2,
        'request_output_bytes': 4*1024**2, 'maximum_request_bytes': 1024**2,
        'maximum_provider_response_bytes': 256*1024, 'maximum_response_bytes': 131072,
        'http_timeout_seconds': 1, 'max_output_tokens': 256,
        'witness_proposer': 'canned_provider_response', 'certificate_assembler': 'sdk_proposal_assembler_v1',
        'certificate_backend': 'r6_fixture_witness', 'certificate_type': 'farkas', 'trust_tier': 1,
        'phase_mapping': PHASES, 'live_model_calls': 0, 'live_model_cost_usd': 0,
        'preparation_closer': 'frozen_human_omega'})


if __name__ == '__main__': freeze()

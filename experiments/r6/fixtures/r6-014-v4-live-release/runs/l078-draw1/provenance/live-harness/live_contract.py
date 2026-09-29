"""R6-005 policy identity. Never changes an earlier policy's source lock."""
from pathlib import Path
import hashlib
import json

import credential_contract as previous
import provider_contract as consumer
import run as r6

NAME = 'responses_https_canned_v1'
CONFIG = r6.ROOT/'policies/responses-https-v1.json'
LOCK = r6.ROOT/'policies/live-harness-v1.sha256.json'
PROMPT = consumer.PROMPT
RUNTIME = consumer.RUNTIME
FILES = ('live_contract.py', 'live_payload.py', 'live_budget.py', 'live_https.py', 'live_tls_fixture.py',
         'live_episode.py', 'live_audit.py', 'test_live.py')


def require(ok, message):
    if not ok: raise ValueError('Live contract: '+message)


def config():
    c = r6.read_json(CONFIG)
    require(c['name'] == NAME and c['live_enabled'] is False, 'this checkpoint permits canned traffic only')
    require(c['previous_policy_sha256'] == r6.sha(previous.CONFIG), 'credential policy chain')
    require(c['consumer_policy_sha256'] == r6.sha(consumer.CONFIG), 'consumer policy chain')
    require(c['prompt_sha256'] == r6.sha(PROMPT), 'prompt changed')
    require(c['runtime_sha256'] == r6.sha(RUNTIME), 'runtime changed')
    require(c['request']['model'] == c['model']['requested_id'], 'model selection differs')
    require(c['endpoint'] == {'scheme': 'https', 'host': 'api.openai.com', 'port': 443, 'path': '/v1/responses'}, 'endpoint changed')
    require(c['tls']['verify_mode'] == 'CERT_REQUIRED' and c['tls']['check_hostname'] is True
            and c['tls']['minimum_version'] == 'TLSv1_2', 'TLS policy weakened')
    require(c['limits']['attempts_per_episode'] == 1 and c['limits']['automatic_retries'] == 0
            and c['limits']['redirects'] == 0, 'one-attempt policy changed')
    require(c['request']['max_output_tokens'] == c['limits']['output_tokens'], 'output cap differs')
    require(c['limits']['input_tokens_reserved'] > c['limits']['message_utf8_bytes'], 'input reserve lacks framing allowance')
    return c


def source_lock():
    lock = r6.read_json(LOCK)
    require(set(lock) == set(FILES), 'source lock population changed')
    return lock


def verify_sources():
    previous.verify_sources()
    for name, digest in source_lock().items():
        require(r6.sha(r6.ROOT/name) == digest, 'locked source changed: '+name)
    config()


def freeze():
    config()
    with LOCK.open('x') as f:
        json.dump({p: r6.sha(r6.ROOT/p) for p in FILES}, f, indent=2, sort_keys=True)
        f.write('\n')


def development(directory):
    """Explicit disposable snapshot. Its paths cannot audit as the final lock."""
    global CONFIG, LOCK
    directory = Path(directory).resolve(); directory.mkdir(parents=True, exist_ok=False)
    import shutil
    destination=directory/CONFIG.name
    shutil.copyfile(CONFIG,destination)
    CONFIG=destination; LOCK=directory/LOCK.name
    freeze()


def bytes_hash(data): return hashlib.sha256(data).hexdigest()

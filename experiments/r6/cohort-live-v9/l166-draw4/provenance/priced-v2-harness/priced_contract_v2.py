"""R6-006: mandatory source admission; R6-005 remains an immutable dependency."""
from pathlib import Path
import json
import shutil

import priced_contract as previous
import provider_contract as consumer
import pricing_gate_v2 as gate
import run as r6

NAME='responses_priced_https_canned_v2'
CONFIG=r6.ROOT/'policies/responses-priced-https-v2.json'
LOCK=r6.ROOT/'policies/priced-harness-v2.sha256.json'
SOURCES=r6.ROOT/'sources/pricing-approved-v2'
PROMPT=previous.PROMPT
RUNTIME=previous.RUNTIME
FILES=('pricing_gate_v2.py','pricing_capture_v2.py','priced_contract_v2.py','priced_payload_v2.py','priced_budget_v2.py',
       'priced_https_v2.py','priced_episode_v2.py','priced_audit_v2.py','test_pricing_v2.py')
bytes_hash=gate.sha


def config():
    raw=CONFIG.read_bytes(); c=gate.strict(raw)
    gate.require(raw==gate.canonical(c)+b'\n','priced_policy_encoding')
    gate.require(c['name']==NAME and c['live_enabled'] is False,'canned_only_policy')
    gate.require(c['previous_policy_sha256']==r6.sha(previous.CONFIG),'previous_policy_binding')
    gate.require(c['consumer_policy_sha256']==r6.sha(consumer.CONFIG),'consumer_policy_binding')
    gate.require(c['prompt_sha256']==r6.sha(PROMPT) and c['runtime_sha256']==r6.sha(RUNTIME),'prompt_runtime_binding')
    gate.require(c['model']['requested_id']==c['request']['model']==gate.MODEL
        and c['model']['allowed_response_ids']==[gate.MODEL],'dated_model_binding')
    old=previous.config()
    for field in ('endpoint','tls','credential','limits'):
        gate.require(c[field]==old[field],'inherited_'+field+'_changed')
    expected={**old['request'],'model':gate.MODEL}
    gate.require(c['request']==expected,'request_configuration_changed')
    gate.require(set(c['pricing_admission']['sources'])==set(gate.URLS),'price_source_membership')
    gate.require(c['pricing_admission']['maximum_source_age_seconds']==86400
        and c['pricing_admission']['future_clock_tolerance_seconds']==5,'price_freshness_policy')
    return c


def source_lock():
    lock=r6.read_json(LOCK)
    gate.require(set(lock)==set(FILES),'priced_source_population')
    return lock


def capture_identity(directory):
    gate.source_evidence(directory)
    files={p.name:r6.sha(p) for p in sorted(Path(directory).iterdir())}
    return gate.sha(gate.canonical(files))


def verify_sources():
    previous.verify_sources()
    for path,h in source_lock().items():
        gate.require(r6.sha(r6.ROOT/path)==h,'priced_locked_source_changed_'+path)
    config()


def freeze():
    config()
    with LOCK.open('x') as f:
        json.dump({p:r6.sha(r6.ROOT/p) for p in FILES},f,sort_keys=True,indent=2); f.write('\n')


def development(directory):
    global CONFIG,LOCK,SOURCES
    directory=Path(directory).resolve()
    gate.require(directory.is_relative_to(r6.ROOT/'.cache'),'development_path')
    directory.mkdir(parents=True,exist_ok=False)
    shutil.copyfile(CONFIG,directory/CONFIG.name)
    CONFIG=directory/CONFIG.name; LOCK=directory/LOCK.name
    freeze()

#!/usr/bin/env python3
"""R6-005 closeout bindings, preservation and recorded replay observations.

Run after https_gates.py has freshly re-audited the original checkpoint.
No native episode, compilation, proof replay or model inference is executed.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

import pricing_source_controls as controls
import pricing_sources as p

HERE = Path(__file__).resolve().parent
R6 = HERE.parents[1]
REPO = R6.parents[1]


def run(output):
    public_path = HERE/'R6-005-CLOSEOUT-PUBLIC-GATE.json'
    public = json.loads(public_path.read_bytes())
    p.require(public['passed'] is True and public['total_checks'] == 96, 'checkpoint gate is incomplete')
    bundle = HERE/'R6-005-SOURCES'
    source_records = {}
    for model in p.MODELS:
        extracted, receipt = p.verify(bundle, model)
        source_records[model] = {'receipt_sha256': p.sha((bundle/(model+'.receipt.json')).read_bytes()),
            'raw_sha256': receipt['raw']['sha256'], 'raw_bytes': receipt['raw']['bytes'],
            'canonical_extract_sha256': receipt['extract']['canonical_sha256'],
            'listed_dated_ids': extracted['listed_dated_ids'],
            'cache_write_rate': extracted['per_million_tokens']['cache_write']}
    pricing = p.policy_check(bundle, R6/'policies/responses-https-v1.json')
    p.require(pricing['policy_sha256'] == public['policy_sha256'], 'source comparison checks a different policy')
    controls_path = HERE/'R6-005-CLOSEOUT-SOURCE-CONTROLS.json'
    tested = json.loads(controls_path.read_bytes())
    names = [x['name'] for x in tested['checks']]
    p.require(tested['passed'] is True and tested['check_count'] == len(controls.CASES)
        and tested['expected_cases'] == list(controls.CASES) and len(names) == len(set(names))
        and set(names) == set(controls.CASES) and all(x['passed'] is True for x in tested['checks']), 'source control population differs')
    p.require(all(x['detail']['unmutated_copy_passes'] is True and x['detail']['changed_relationships'] == 1
        for x in tested['checks'][2:]), 'source mutation preconditions differ')
    p.require(tested['program_sha256'] == p.sha(Path(controls.__file__).read_bytes())
        and tested['extractor_sha256'] == p.sha(Path(p.__file__).read_bytes()), 'source control program binding differs')

    prior = {}
    inventories = {}
    for name in ('R6-005-PRESERVATION.json', 'R6-005-CLOSEOUT-PRESERVATION.json'):
        path = HERE/name
        record = json.loads(path.read_bytes())
        for relative, digest in record['files'].items():
            p.require(relative not in prior or prior[relative] == digest, 'preservation inventories disagree')
            p.require(p.sha((REPO/relative).read_bytes()) == digest, 'prior file changed: '+relative)
            prior[relative] = digest
        inventories[name] = {'sha256': p.sha(path.read_bytes()), 'files_checked': len(record['files'])}

    replay = {}
    for name in ('d1_valid', 'c8_valid'):
        current = R6/'runs/https-checkpoint-v1'/name
        earlier = R6/'runs/provider-checkpoint-v1'/name
        v = json.loads((current/'verdict.json').read_bytes())
        old = json.loads((earlier/'verdict.json').read_bytes())
        p.require(public['episodes'][name]['accepted'] is True and public['episodes'][name]['proof_accepted'] is True,
                  'replay observation lacks a passing episode audit')
        p.require('proof_replayed' not in v, 'historical field observation differs')
        reports = v['final_validation']
        p.require(set(reports) == {'local', 'whole'} and all(x['accepted'] is True for x in reports.values()), 'replay report absent or incomplete')
        digest = hashlib.sha256()
        size = 0
        with gzip.open(current/'solution.ndjson.gz', 'rb') as a, gzip.open(earlier/'solution.ndjson.gz', 'rb') as b:
            while True:
                left, right = a.read(1024**2), b.read(1024**2)
                p.require(left == right, 'uncompressed proof exports differ')
                if not left:
                    break
                size += len(left)
                p.require(size <= 256*1024**2, 'proof comparison exceeds bound')
                digest.update(left)
        p.require(digest.hexdigest() == v['solution_sha256'] == old['solution_sha256'], 'proof digest declaration differs')
        replay[name] = {'verdict_sha256': p.sha((current/'verdict.json').read_bytes()),
            'r6_003_verdict_sha256': p.sha((earlier/'verdict.json').read_bytes()),
            'raw_proof_replayed_field_present': False, 'raw_proof_replayed': None,
            'recorded_proof_replay_confirmed_by_artifact_audit': True,
            'interpretation_basis': 'fresh passing original-tree episode audit, including the shared proof auditor; retained final_validation reports and receipts, not a new replay',
            'derivation_replayed': v['derivation_replayed'],
            'checked_declarations': {k: report['checked_declarations'] for k, report in reports.items()},
            'proof_export_sha256': digest.hexdigest(), 'proof_export_bytes': size,
            'uncompressed_export_byte_identical_to_r6_003': True}
    previous = json.loads((R6/'runs/credential-checkpoint-v3/d1_valid/verdict.json').read_bytes())
    p.require(previous['proof_replayed'] is True, 'R6-004 field observation differs')
    result = {'schema_version': 'r6-005-closeout-checks-1', 'passed': True,
        'checkpoint_checks': 96, 'source_controls': {'count': len(controls.CASES), 'sha256': p.sha(controls_path.read_bytes())},
        'fresh_public_gate_sha256': p.sha(public_path.read_bytes()), 'program_sha256': p.sha(Path(__file__).read_bytes()),
        'policy_sha256': public['policy_sha256'], 'source_lock_sha256': public['source_lock_sha256'],
        'preservation': inventories, 'distinct_prior_files_preserved': len(prior),
        'sources': source_records, 'pricing': pricing, 'replay_observations': replay,
        'r6_004_d1_raw_proof_replayed': True,
        'model_decision': {'status': 'recommendation; author selection pending',
            'recommended_measurement_id': 'gpt-5.4-2026-03-05',
            'frozen_canned_id': 'gpt-5.6-sol', 'policy_changed': False,
            'dated_id_is_model_content_hash': False, 'inference_attested': False},
        'native_episodes_rerun': 0, 'live_model_calls': 0, 'live_model_cost_usd': 0,
        'scope': 'closeout of local canned HTTPS evidence; source captures postdate the checkpoint; no live policy or spending authorization'}
    p.write(output, result)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.output)
    print(json.dumps({k: result[k] for k in ('passed', 'checkpoint_checks', 'source_controls', 'distinct_prior_files_preserved')}, indent=2))

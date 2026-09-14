#!/usr/bin/env python3
"""Independent R6-006 reporting counts; no native execution or inference."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
import priced_contract_v2 as contract
import pricing_gate_v2 as gate
import run as r6
import test_pricing_v2 as tests

FAILURES={
    'missing_permit':'pricing_permit_missing','forged_admission':'pricing_permit_binding',
    'wrong_reservation':'pricing_reservation_amount','changed_request':'pricing_request_body_binding',
    'raw_source_changed':'pricing_raw_drift_model','semantic_source_changed':'pricing_semantic_drift_model',
    'stale_source':'pricing_capture_stale','future_source':'pricing_capture_in_future',
    'host_stale_source':'pricing_capture_stale','wrong_request_model':'pricing_request_options',
    'context_at_limit':'pricing_long_context_out_of_scope','context_over_limit':'pricing_long_context_out_of_scope',
    'regional_endpoint':'pricing_regional_endpoint_out_of_scope',
}


def measure(root,output):
    counts={'episodes':0,'host_pricing_rejections':0,'actor_pricing_rejections':0,'actor_pricing_acceptances':0,
            'reservations':0,'connection_attempts':0,'body_sends':0,'endpoint_receipts':0,'proofs_accepted':0}
    episodes={}; origins=set()
    for name in tests.NATIVE_CASES:
        _,case,_=tests.expected_native(name); p=root/name
        host=r6.read_json(p/'host-pricing-admission.json'); account=r6.read_json(p/'accounting.json')
        counts['episodes']+=1
        for key,field in [('reservations','attempts_reserved'),('connection_attempts','connection_attempts'),
                          ('body_sends','bodies_started'),('endpoint_receipts','endpoint_receipts')]:
            gate.require(type(account[field]) is int,'reporting_count_type'); counts[key]+=account[field]
        if not host['accepted']:
            counts['host_pricing_rejections']+=1
            gate.require(case=='host_stale_source' and account['attempts_reserved']==0
                and not (p/'stages/proposal-1').exists(),'host_rejection_scope')
            code=host['failure_code']; actor=None
        else:
            actor=r6.read_json(p/'stages/proposal-1/output/pricing-check.json')
            counts['actor_pricing_acceptances' if actor['accepted'] else 'actor_pricing_rejections']+=1
            code=actor.get('failure_code')
        if case in FAILURES:
            gate.require(code==FAILURES[case] and account['connection_attempts']==0
                and account['bodies_started']==0 and account['endpoint_receipts']==0,'price_rejection_boundary')
        else: gate.require(code is None,'unexpected_price_failure')
        origin=contract.capture_identity(p/'pricing-origin')
        gate.require(origin==r6.read_json(p/'search-policy.json')['pricing_origin_sha256'],'capture_enrollment_binding')
        origins.add(origin)
        record={'host_admitted':host['accepted'],'actor_admitted':None if actor is None else actor['accepted'],
                'pricing_failure_code':code,'reservations':account['attempts_reserved'],
                'connection_attempts':account['connection_attempts'],'body_sends':account['bodies_started']}
        if host['accepted']:
            for premise in ('long_context_surcharge_applicable','regional_surcharge_applicable'):
                gate.require(host['applicability'][premise] is False,'host_applicability_report')
            record['host_applicability']=host['applicability']
        if actor is not None and actor['accepted']:
            gate.require(actor['current']['applicability']==host['applicability'],'actor_applicability_report')
            record['actor_applicability']=actor['current']['applicability']
        if case in ('context_at_limit','context_over_limit','regional_endpoint'):
            policy=r6.read_json(p/'transport-policy.json')
            record['substituted_actor_input']={'input_tokens_reserved':policy['limits']['input_tokens_reserved'],'endpoint':policy['endpoint']}
        if case=='valid':
            v=r6.read_json(p/'verdict.json'); counts['proofs_accepted']+=1
            gate.require(v['proof_replayed'] is True and v['certificate_consumed'] is True
                and v['derivation_replayed'] is False and v['residual_closer']=='omega','proof_scope')
            prior=ROOT/'runs/provider-checkpoint-v1'/name
            digest=hashlib.sha256();length=0
            with gzip.open(p/'solution.ndjson.gz','rb') as a,gzip.open(prior/'solution.ndjson.gz','rb') as b:
                while True:
                    x,y=a.read(1024**2),b.read(1024**2)
                    gate.require(x==y,'proof_export_changed')
                    if not x:break
                    length+=len(x);gate.require(length<=256*1024**2,'proof_export_bound');digest.update(x)
            gate.require(digest.hexdigest()==v['solution_sha256'],'proof_digest_binding')
            reports=v['final_validation']
            record.update(proof_sha256=digest.hexdigest(),proof_bytes=length,byte_identical_to_r6_003=True,
                checked_declarations={k:r['checked_declarations'] for k,r in reports.items()},
                type_hashes={k:r['targets'][0]['type_sha256'] for k,r in reports.items()},axiom_delta=v['axiom_delta'])
        episodes[name]=record
    gate.require(counts=={'episodes':20,'host_pricing_rejections':1,'actor_pricing_rejections':12,
        'actor_pricing_acceptances':7,'reservations':19,'connection_attempts':7,'body_sends':6,
        'endpoint_receipts':6,'proofs_accepted':2},'reporting_population_changed')
    source=gate.source_evidence(root/'d1_valid/pricing-origin')
    rates=gate.rates_from(source)
    gate.require(rates==contract.config()['pricing']['nano_usd_per_token'],'reported_rate_basis')
    result={'passed':True,'program_sha256':r6.sha(Path(__file__)),'counts':counts,'episodes':episodes,
        'distinct_enrolled_captures':len(origins),'capture_identities':sorted(origins),
        'applicability_policy':contract.config()['pricing_admission']['applicability'],
        'nano_usd_per_token':rates,'reservation_micro_usd':gate.cost_micro(16384,4096,rates),
        'captured_sources':{role:{'raw_sha256':data['raw_sha256'],'extract_sha256':data['extract_sha256'],
            'receipt_sha256':data['receipt_sha256'],'raw_bytes':(root/'d1_valid/pricing-origin'/(role+'.html')).stat().st_size}
            for role,data in source.items()},
        'live_model_calls':0,'live_model_cost_usd':0,
        'scope':'re-derived recorded boundary counts and bytewise proof comparison, separate from conformance-case counts; no new native replay or inference attestation'}
    with output.open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();result=measure(args.run_dir.resolve(),args.output.resolve())
    print(json.dumps(result['counts'],indent=2))

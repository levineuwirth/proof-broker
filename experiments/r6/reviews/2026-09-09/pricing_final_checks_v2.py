#!/usr/bin/env python3
"""R6-006 independent hash/count, preservation and publication preflight.

Re-derives event digests directly rather than calling events.read. No native
episode, TLS handshake, Lean compilation or proof replay is executed here.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
REPO=ROOT.parents[1]
sys.path.insert(0,str(ROOT))
import credential
import priced_contract_v2 as contract
import publication
import run as r6
import test_pricing_v2 as tests


def require(ok,message):
    if not ok: raise AssertionError(message)


def digest(data): return hashlib.sha256(data).hexdigest()


def verify(root,gate_record,output):
    contract.verify_sources()
    index=json.loads((root/'checkpoint.json').read_bytes())
    public=json.loads(gate_record.read_bytes())
    for label,record in [('checkpoint',index),('public gate',public)]:
        require(record['passed'] is True,label+' is not complete')
        require(record['policy_sha256']==r6.sha(contract.CONFIG),label+' policy declaration differs')
        require(record['source_lock_sha256']==r6.sha(contract.LOCK),label+' source declaration differs')
        require(record['live_model_calls']==0,label+' live count differs')
    gate_program=Path(__file__).with_name('pricing_gates_v2.py')
    spec=importlib.util.spec_from_file_location('r6_006_public_gate',gate_program)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    gate_file=gate_record.with_name('R6-006-V2-GATES.json')
    gates=json.loads(gate_file.read_bytes())
    gate_names=[row['name'] for row in gates['checks']]
    require(len(gate_names)==len(set(gate_names)) and set(gate_names)==set(module.CASES),'outer-gate population differs')
    require(gates['passed'] is True and gates['check_count']==len(module.CASES)
        and gates['expected_cases']==module.CASES,'outer gate is incomplete')
    require(all(row['passed'] is True and row['detail']['unmutated_copy_passes'] is True
        and row['detail']['changed_relationships']==1 for row in gates['checks']),'outer-gate control contract differs')
    require(public['gate_file_sha256']==r6.sha(gate_file) and public['gate_program_sha256']==r6.sha(gate_program),
            'outer-gate provenance differs')
    event_count=sealed_count=0; canaries=[]; episodes={}
    for name in tests.NATIVE_CASES:
        p=root/name; seal=json.loads((p/'seal.json').read_bytes())
        previous='0'*64; count=0
        for i,line in enumerate((p/'events.ndjson').read_bytes().splitlines()):
            row=json.loads(line); recorded=row.pop('event_hash')
            require(row['sequence']==i and row['previous_hash']==previous,'event position differs')
            actual=digest(json.dumps(row,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode())
            require(recorded==actual,'event hash differs')
            previous=actual;count+=1
        require(count==seal['event_count'] and previous==seal['last_event_hash'],'terminal seal differs')
        for path,h in seal['retained_sha256'].items():
            require((p/path).resolve().is_relative_to(p.resolve()),'seal path escape')
            require(digest((p/path).read_bytes())==h,'retained bytes differ')
        event_count+=count;sealed_count+=len(seal['retained_sha256'])
        seed=json.loads((p/'credential-canary.json').read_bytes())['nonce'];canaries.append(credential.derive(seed))
        _,case,_=tests.expected_native(name)
        if case=='host_stale_source':
            require(not (p/'stages/proposal-1').exists(),'host rejection launched transport')
            accounting=json.loads((p/'accounting.json').read_bytes())
            require(accounting['attempts_reserved']==0 and accounting['connection_attempts']==0
                and accounting['bodies_started']==0,'host rejection reserved or transmitted')
            episodes[name]={'events':count,'sealed':len(seal['retained_sha256']),
                'header_sends':0,'body_sends':0,'tls_failure':False,'transport_stage_present':False}
        else:
            http=json.loads((p/'stages/proposal-1/output/http.json').read_bytes())
            episodes[name]={'events':count,'sealed':len(seal['retained_sha256']),
                'header_sends':http['header_sends_started'],'body_sends':http['body_sends_started'],
                'tls_failure':http['failure_category']=='tls_certificate_verification','transport_stage_present':True}
    require(public['event_count']==event_count and public['sealed_entries']==sealed_count,'public recount differs')
    suites={}
    for filename,names in tests.SUITES.items():
        v=json.loads((root/filename).read_bytes());actual_names=[x['name'] for x in v['checks']]
        require(len(actual_names)==len(set(actual_names)) and set(actual_names)==set(names),'frozen case set differs')
        require(v['passed'] is True and all(x['passed'] is True for x in v['checks']),'suite has a failure')
        require(index['suites'][filename]=={'sha256':digest((root/filename).read_bytes()),'count':len(names)},'suite binding differs')
        suites[filename]=len(names)
    preservation=tests.check_preservation()
    require(index['preservation']==public['preservation']==preservation,'preservation declaration differs')
    require(public['content_checks']==sum(suites.values()) and public['gate_checks']==len(module.CASES)
        and public['total_checks']==sum(suites.values())+len(module.CASES),'public check totals differ')
    baseline=json.loads(tests.PRESERVATION.read_bytes())['files']
    selected=subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','-z','--','experiments/r6'],cwd=REPO).decode().split('\0')
    added=sorted({p for p in selected if p and p not in baseline and (REPO/p).is_file() and (REPO/p).resolve()!=output.resolve()})
    retained={p:digest((REPO/p).read_bytes()) for p in added}
    unique={};apparent=0
    for p,h in retained.items():
        n=(REPO/p).stat().st_size;apparent+=n;unique[h]=n
    require(not any('/pricing-native-' in p for p in retained),'development run selected for publication')
    # Every declared retained episode path must be Git-selected. A file that
    # merely remains available as a build product is not publication coverage.
    selected_set=set(selected)
    for name in tests.NATIVE_CASES:
        seal=json.loads((root/name/'seal.json').read_bytes())
        for path in seal['retained_sha256']:
            require(str((root/name/path).relative_to(REPO)) in selected_set,'required artifact is ignored: '+name+'/'+path)
    review=ROOT/'reviews/2026-09-09'
    scan_roots=[root,*[REPO/p for p in added if not (REPO/p).is_relative_to(root)]]
    seed=json.loads((root/'d1_valid/credential-canary.json').read_bytes())['nonce']
    scan=publication.scan(scan_roots,canaries[0],seed,extra_canaries=canaries[1:])
    require(not scan['incompletely_scanned'] and not scan['unreadable_directories'] and not scan['irregular_entries'],'publication scan incomplete')
    require(len(scan['disclosures'])==2 and all(h['path']=='d1_reflected_canary/stages/proposal-1/output/provider-response.json' for h in scan['disclosures']),
            'unexpected canary disclosure')
    result={'passed':True,'policy_sha256':r6.sha(contract.CONFIG),'source_lock_sha256':r6.sha(contract.LOCK),
        'public_gate_record_sha256':r6.sha(gate_record),'suite_counts':suites,'content_checks':sum(suites.values()),
        'gate_checks':len(module.CASES),'total_checks':sum(suites.values())+len(module.CASES),
        'price_basis':{'model':contract.config()['model']['requested_id'],'nano_usd_per_token':contract.config()['pricing']['nano_usd_per_token'],
            'sources':contract.config()['pricing_admission']['sources'],
            'applicability':contract.config()['pricing_admission']['applicability']},
        'preflight_program_sha256':r6.sha(Path(__file__)),
        'event_hashes_recomputed':event_count,'sealed_hashes_recomputed':sealed_count,'episodes':episodes,
        'preservation':preservation,'retention_inputs':{'files':len(retained),'apparent_bytes':apparent,
            'distinct_blobs':len(unique),'unique_bytes':sum(unique.values()),
            'inventory_sha256':digest(json.dumps(retained,sort_keys=True,separators=(',',':')).encode()),
            'scope':'Git-selected R6-006 v2 additions before this output; record excluded to avoid self-reference'},
        'publication':{'files_scanned':scan['files_scanned'],'canaries':len(canaries),
            'expected_reflection_matches':2,'unexpected_matches':0,'new_non_run_artifacts_scanned':True},
        'live_model_calls':0,'live_model_cost_usd':0,
        'scope':'independent artifact recount and publication scan; no new native execution or inference attestation'}
    r6.write_json(output,result)
    for canary in canaries:
        require(not publication.occurrences(output.read_bytes(),publication.patterns(canary)),'preflight output leaks canary')
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir',type=Path,required=True)
    parser.add_argument('--gate-record',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=verify(args.run_dir.resolve(),args.gate_record.resolve(),args.output.resolve())
    print(json.dumps({k:result[k] for k in ('passed','total_checks','event_hashes_recomputed','sealed_hashes_recomputed','retention_inputs')},indent=2))

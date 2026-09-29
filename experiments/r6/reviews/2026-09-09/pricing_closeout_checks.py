#!/usr/bin/env python3
"""R6-006 approval closeout: compare existing artifacts, execute no native run.

Run on the closeout checkout: the Git-selected input population is deliberately
fixed. New research files in a later checkout are not silently excluded.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
REPO=ROOT.parents[1]
sys.path.insert(0,str(ROOT))
import priced_contract_v2 as contract
import test_pricing_v2 as tests
import run as r6

REVIEW=ROOT/'reviews/2026-09-09'
CLOSEOUT_FILES=('pricing_closeout_checks.py','R6-006-CLOSEOUT.md','R6-006-CLOSEOUT-CHECKS.json',
                'R6-006-CLOSEOUT-PUBLIC-GATE.json','R6-006-CLOSEOUT-PREFLIGHT.json')
APPROVED_RETENTION={'files':4022,'apparent_bytes':103209285,'distinct_blobs':918,'unique_bytes':12391981,
    'inventory_sha256':'e4de23a85e2c76234000f4f55f6a2fbcbfd0f04ace6bb8837f73b6335bf5cc2f'}


def require(ok,message):
    if not ok: raise AssertionError(message)


def checks(output):
    contract.verify_sources()
    preserved=tests.check_preservation()
    prior=r6.read_json(tests.PRESERVATION)['files']
    earlier=r6.read_json(REVIEW/'R6-006-PRESERVATION.json')['files']
    require(len(prior)==19536 and len(earlier)==16292,'preservation populations changed')
    require(all(prior.get(p)==h for p,h in earlier.items()),'v1 preservation is not contained byte-for-byte')
    preflight_path=REVIEW/'R6-006-V2-PREFLIGHT.json'
    preflight=r6.read_json(preflight_path)
    require(preflight['passed'] is True,'approved preflight is not passing')
    require({k:preflight['retention_inputs'][k] for k in APPROVED_RETENTION}==APPROVED_RETENTION,
            'approved retention anchor differs')
    selected=subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','-z','--','experiments/r6'],cwd=REPO).decode().split('\0')
    excluded={str((REVIEW/name).relative_to(REPO)) for name in CLOSEOUT_FILES}
    excluded.add(str(preflight_path.relative_to(REPO)))
    files={p:r6.sha(REPO/p) for p in sorted(set(selected)) if p and p not in prior and p not in excluded and (REPO/p).is_file()}
    sizes={}; apparent=0
    for p,h in files.items():
        n=(REPO/p).stat().st_size;apparent+=n;sizes[h]=n
    observed={'files':len(files),'apparent_bytes':apparent,'distinct_blobs':len(sizes),'unique_bytes':sum(sizes.values()),
        'inventory_sha256':hashlib.sha256(json.dumps(files,sort_keys=True,separators=(',',':')).encode()).hexdigest()}
    require(observed==APPROVED_RETENTION,'approved v2 input population or bytes changed')
    public_path=REVIEW/'R6-006-CLOSEOUT-PUBLIC-GATE.json';public=r6.read_json(public_path)
    require(public['passed'] is True and public['preservation']==preserved,'fresh public recount differs')
    require(public['total_checks']==120 and public['content_checks']==105 and public['gate_checks']==15
        and public['event_count']==431 and public['sealed_entries']==3951,'fresh recount figures differ')
    require(public['policy_sha256']==r6.sha(contract.CONFIG) and public['source_lock_sha256']==r6.sha(contract.LOCK),
            'fresh recount policy/source declaration differs')
    require(public['gate_file_sha256']==r6.sha(REVIEW/'R6-006-V2-GATES.json')
        and public['gate_program_sha256']==r6.sha(REVIEW/'pricing_gates_v2.py'),'fresh outer-gate binding differs')
    subjects=[ROOT/'R6-006.md',ROOT/'R6-006-V2.md',contract.CONFIG,contract.LOCK,tests.PRESERVATION,
        ROOT/'pricing-v2-runs/checkpoint-v2/checkpoint.json',REVIEW/'R6-006-V2-GATES.json',
        REVIEW/'R6-006-V2-PUBLIC-GATE.json',REVIEW/'R6-006-V2-MEASUREMENTS.json',preflight_path,
        public_path,REVIEW/'R6-006-CLOSEOUT.md',Path(__file__)]
    result={'schema_version':'r6-006-closeout-1','passed':True,'approval':{'status':'approved','date':'2026-09-10',
        'source':'author review in conversation','findings_outstanding':0,
        'scope':'local canned HTTPS pricing and applicability admission; no live-model selection or spending approval'},
        'preservation':preserved,'earlier_inventory_contained':{'files':len(earlier),'matching_entries':len(earlier)},
        'approved_v2_retention_recomputed':observed,
        'distinct_prior_paths_compared':len(prior)+len(files),
        'prior_preflight_record':{'sha256':r6.sha(preflight_path),
            'scope':'bound at closeout; excluded from its own historical retention inventory'},
        'evidence_sha256':{str(p.relative_to(REPO)):r6.sha(p) for p in subjects},
        'suite_counts':[46,20,39,15],'total_checks':120,'events':431,'sealed_entries':3951,
        'native_episodes_rerun':0,'lean_replays_rerun':0,'outer_mutations_rerun':0,
        'sources_refetched_during_closeout':False,'live_model_calls':0,'live_model_cost_usd':0,
        'live_model_selection':'pending','spending_authorization':'pending',
        'scope':'artifact comparison and author approval record; no new native execution, provider observation or inference attestation'}
    with output.open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();result=checks(args.output.resolve())
    print(json.dumps({k:result[k] for k in ('passed','total_checks','distinct_prior_paths_compared','earlier_inventory_contained')},indent=2))

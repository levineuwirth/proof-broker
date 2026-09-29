#!/usr/bin/env python3
"""Non-locked R6-006 outer-gate review. One changed relationship per probe.

Gate controls validate the finished content checkpoint. Their own exact case
set and source digest are checked by publish(), avoiding a self-referential
requirement to validate probe results before those probes have run.
"""
import argparse
import copy
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
import credential
import events
import priced_contract_v2 as contract
import run as r6
import test_pricing_v2 as tests
from test_proposals import Suite,require,rejected,assert_complete

CASES='''incomplete_checkpoint wrong_policy_declaration wrong_source_lock_declaration
missing_frozen_case substituted_frozen_case duplicated_frozen_case wrong_suite_digest
missing_episode wrong_native_seal wrong_native_log_digest wrong_native_disclosures
wrong_native_coverage wrong_native_task wrong_preservation_summary unexpected_outer_log_disclosure'''.split()


def controls(root,output):
    original=tests.recount(root)
    require(original['passed'] is True)
    suite=Suite(output,CASES)
    def rebind(copied,file):
        index=r6.read_json(copied/'checkpoint.json')
        index['suites'][file]['sha256']=r6.sha(copied/file)
        r6.write_json(copied/'checkpoint.json',index)
    def native_change(copied,change):
        file=copied/'native.json'; value=r6.read_json(file)
        rows=[r for r in value['checks'] if r['name']=='d1_valid']; require(len(rows)==1)
        before=events.canonical(rows[0]['detail']); change(rows[0]['detail'])
        require(events.canonical(rows[0]['detail'])!=before,'mutation did not change a native relationship')
        r6.write_json(file,value); rebind(copied,'native.json')
    def mutate(copied,name):
        if name in ('incomplete_checkpoint','wrong_policy_declaration','wrong_source_lock_declaration','wrong_suite_digest','wrong_preservation_summary'):
            def change(v):
                if name=='incomplete_checkpoint': v['passed']=False
                elif name=='wrong_policy_declaration': v['policy_sha256']='0'*64
                elif name=='wrong_source_lock_declaration': v['source_lock_sha256']='0'*64
                elif name=='wrong_suite_digest': v['suites']['focused.json']['sha256']='0'*64
                else: v['preservation']['checked_files']=0
            tests.edit(copied/'checkpoint.json',change)
        elif name in ('missing_frozen_case','substituted_frozen_case','duplicated_frozen_case'):
            v=r6.read_json(copied/'focused.json')
            if name=='missing_frozen_case':
                v['checks'].pop();v['expected_cases'].pop();v['check_count']-=1
            elif name=='substituted_frozen_case': v['checks'][-1]['name']='undeclared_check'
            else: v['checks'][-1]=copy.deepcopy(v['checks'][0])
            r6.write_json(copied/'focused.json',v);rebind(copied,'focused.json')
            if name=='missing_frozen_case':
                tests.edit(copied/'checkpoint.json',lambda x:x['suites']['focused.json'].update(count=v['check_count']))
        elif name=='missing_episode': shutil.rmtree(copied/'d1_http503')
        elif name=='wrong_native_seal': native_change(copied,lambda v:v.update(seal_sha256='0'*64))
        elif name=='wrong_native_log_digest': native_change(copied,lambda v:v.update(process_log_sha256='0'*64))
        elif name=='wrong_native_disclosures': native_change(copied,lambda v:v['observations'].update(disclosures=9))
        elif name=='wrong_native_coverage': native_change(copied,lambda v:v['observations']['coverage'].update(recomputed=0))
        elif name=='wrong_native_task': native_change(copied,lambda v:v.update(task_id='c1-c8-2p18'))
        elif name=='unexpected_outer_log_disclosure':
            seed=r6.read_json(copied/'d1_valid/credential-canary.json')['nonce']
            canary=credential.derive(seed)
            log=copied/'d1_valid.log'
            require(canary.encode() not in log.read_bytes(),'leak precondition already present')
            with log.open('ab') as f: f.write(canary.encode())
            require(canary.encode() in log.read_bytes(),'leak injection missed')
            native_change(copied,lambda v:v.update(process_log_sha256=r6.sha(log)))
        else: raise AssertionError(name)
    errors={'incomplete_checkpoint':'checkpoint is incomplete','wrong_policy_declaration':'checkpoint policy differs',
        'wrong_source_lock_declaration':'checkpoint source lock differs','missing_frozen_case':'suite hash/count binding differs',
        'substituted_frozen_case':'missing/extra cases','duplicated_frozen_case':'duplicate case',
        'wrong_suite_digest':'suite hash/count binding differs','missing_episode':'episode population differs',
        'wrong_preservation_summary':'checkpoint preservation differs','unexpected_outer_log_disclosure':'unexpected checkpoint disclosure'}
    for name in CASES:
        def probe(name=name):
            with tempfile.TemporaryDirectory(prefix='r6-006-gate-') as tmp:
                copied=Path(tmp)/'checkpoint';shutil.copytree(root,copied)
                require(tests.recount(copied)['passed'] is True,'unmutated complete checkpoint failed')
                mutate(copied,name)
                result=rejected(lambda:tests.recount(copied),errors.get(name,'native suite record differs'))
                return {**result,'unmutated_copy_passes':True,'changed_relationships':1}
        suite.case(name,probe)
    suite.finish()


def publish(root,gate_file,output):
    content=tests.recount(root)
    gates=r6.read_json(gate_file)
    assert_complete([r['name'] for r in gates['checks']],CASES)
    require(gates['passed'] is True and gates['check_count']==len(CASES)
        and gates['expected_cases']==CASES,'gate suite incomplete')
    require(all(r['passed'] is True and r['detail']['unmutated_copy_passes'] is True
        and r['detail']['changed_relationships']==1 for r in gates['checks']),'gate control lacks a baseline or isolates multiple changes')
    result={**content,'content_checks':content['total_checks'],'gate_checks':len(CASES),
        'total_checks':content['total_checks']+len(CASES),
        'gate_file_sha256':r6.sha(gate_file),'gate_program_sha256':r6.sha(Path(__file__)),
        'scope':'complete original-tree content recount plus separately validated outer-gate probes; no live inference'}
    r6.write_json(output,result)
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir',type=Path,required=True)
    parser.add_argument('--gate-file',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--controls',action='store_true')
    parser.add_argument('--development-policy-dir',type=Path)
    args=parser.parse_args()
    if args.development_policy_dir:
        contract.CONFIG=args.development_policy_dir.resolve()/contract.CONFIG.name
        contract.LOCK=args.development_policy_dir.resolve()/contract.LOCK.name
    if args.controls: controls(args.run_dir.resolve(),args.gate_file.resolve())
    result=publish(args.run_dir.resolve(),args.gate_file.resolve(),args.output.resolve())
    print('R6-006 public gate passed:',result['total_checks'])

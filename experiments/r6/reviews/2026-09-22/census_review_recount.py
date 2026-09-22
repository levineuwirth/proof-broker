#!/usr/bin/env python3
"""Independent retained-evidence checks of the R6-010 freeze at 51dd7ab.

This is a review recount of the original population, not a replacement
production admission auditor or a fresh execution of the 34 kernel replays.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]; REPO=ROOT.parents[1]
sys.path.insert(0,str(ROOT))
import census
import site_freeze as freeze
import run as r6
import test_census

J=lambda p:json.loads(Path(p).read_bytes())
SHA=lambda b:hashlib.sha256(b).hexdigest()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--before',type=Path,required=True);p.add_argument('--controls',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();assert not args.output.exists()
    census.verify_lock(); directory=freeze.CENSUS_DIR; frozen=J(directory/'census.json'); pristine=census.pristine()
    upstream=subprocess.check_output(['git','-C','/home/jeans/Repos/research/verinf','show',census.UPSTREAM['commit']+':'+census.UPSTREAM['source_file']])
    assert upstream==pristine==(directory/'Pristine.lean').read_bytes()
    assert census.census()['sites']==frozen['sites'] and len(frozen['sites'])==15 and len(frozen['families'])==4
    run=ROOT/'census-runs/freeze-v1'; reports={}; processes=[]; bindings=0
    expected_reports={f'baseline-{family}/baseline-validation/verdict.raw.json.gz' for family in frozen['families']}
    expected_reports|={s['site_id']+'/'+kind+'/verdict.raw.json.gz' for s in frozen['sites'] for kind in ('source-binding-validation','challenge-validation')}
    present={str(p.relative_to(run)) for p in run.rglob('verdict.raw.json.gz')};assert present==expected_reports
    for relative in sorted(present):
        path=run/relative; raw=J_gzip(path); normalized=J(path.with_name('verdict.json'))
        assert raw['accepted'] is True and raw['stage']=='complete' and raw['kernel_version']=='4.32.2'
        for t in raw['targets']:
            assert t['declaration_exists'] is True and t['kernel_accepted'] is True and t['statement_and_dependencies_match'] is True
            assert set(t['axioms'])<=set(r6.AXIOMS)
            t['type_sha256']=SHA(t.pop('type_repr').encode());t['type_hash_format']='Lean-4.32.2-reprStr-Expr-UTF8'
        assert raw==normalized,relative
        assert J(path.with_name('replay.process.json'))['exit_code']==0
        reports[relative]=normalized;bindings+=int(raw['local_proof_binding_checked'])
    assert len(reports)==34 and bindings==15
    for path in run.rglob('*.process.json'):
        record=J(path);assert record['exit_code']==0,str(path);processes.append(str(path.relative_to(run)))
    sites={}
    for entry in frozen['sites']:
        name=entry['site_id'];d=directory/name;m=J(d/'manifest.json');ex=J(d/'expected.json');site=freeze.Site(entry)
        assert set(m['artifacts_sha256'])==set(freeze.SITE_FILES)
        assert set(m['shared_artifacts_sha256'])==set(freeze.SHARED)|{f'baseline-{site.whole}.ndjson.gz'}
        for f,h in m['artifacts_sha256'].items():assert r6.sha(d/f)==h
        for f,h in m['shared_artifacts_sha256'].items():assert r6.sha(directory/f)==h
        challenge=SHA(gzip.decompress((d/'challenge.ndjson.gz').read_bytes()))
        baseline=SHA(gzip.decompress((directory/f'baseline-{site.whole}.ndjson.gz').read_bytes()))
        result=next(x for x in frozen['results'] if x['site_id']==name)
        assert challenge==ex['challenge_sha256']==result['challenge_sha256']
        assert baseline==ex['baseline_sha256']==frozen['baseline_exports_sha256'][site.whole]
        assert (run/name/'challenge/input/Frozen.lean').read_bytes()==freeze.instrument(pristine,site)
        assert (run/name/'challenge/input/Capture.lean').read_bytes()==freeze.CAPTURE.read_bytes()
        assert (run/name/'challenge/output/context.json').read_bytes()==(d/'context/local-context.json').read_bytes()
        validated=reports[name+'/challenge-validation/verdict.raw.json.gz']
        assert ex['targets']==validated['targets'] and ex['policy']==r6.policy([site.local,site.whole],True,task=site)
        assert validated['local_proof_binding_checked'] is True
        assert result['local_type_sha256']==ex['targets'][0]['type_sha256']
        assert ex['baseline_whole_declaration']==reports['baseline-'+site.whole+'/baseline-validation/verdict.raw.json.gz']['targets'][0]
        assert ex['source_binding_validated'] is True and reports[name+'/source-binding-validation/verdict.raw.json.gz']['accepted'] is True
        assert m['baseline_axioms']=={t['name']:t['axioms'] for t in ex['targets']}
        sites[name]={'challenge_sha256':challenge,'local_type_sha256':result['local_type_sha256'],'target':m['captured_target'],
                     'declarations':validated['checked_declarations'],'manifest_sha256':r6.sha(d/'manifest.json')}
    for family in frozen['families']:
        assert (run/('baseline-'+family)/'baseline/input/Frozen.lean').read_bytes()==pristine
    exposure={}
    for relative in ('pilot-runs/live-2','campaign-runs-v7/live-1'):
        d=ROOT/relative;request=(d/'transport-request.json').read_bytes();obj=json.loads(request)
        body=J(d/'stages/proposal-1/output/outbound-body.json')
        assert body['input'][1]['content'].endswith(request.decode())
        row=next(r for r in obj['problem']['rows'] if r['name']=='hzsum')
        assert row=={'constant':'-16777215','name':'hzsum','relation':'le','terms':[{'coefficient':'-2','variable':'Zmax'},
          {'coefficient':'1','variable':'_pb_atom_0'},{'coefficient':'1','variable':'_pb_atom_1'}]}
        exposure[relative]={'outbound_sha256':r6.sha(d/'stages/proposal-1/output/outbound-body.json'),
          'request_sha256':SHA(request),'direct_task':obj['binding']['task_id'],'l069_as_premise':row,
          'returned_witness':J(d/'validated-response.json')['witness']}
    controls=J(args.controls);names=[x['name'] for x in controls['checks']]
    assert controls['passed'] is True and all(x['passed'] is True for x in controls['checks'])
    assert len(names)==len(set(names))==controls['check_count']==12 and set(names)==set(test_census.CASES)
    before=J(args.before);missing=[];changed=[]
    for name,v in before.items():
        path=REPO/name
        if not path.is_file():missing.append(name)
        elif path.stat().st_size!=v['bytes'] or r6.sha(path)!=v['sha256']:changed.append(name)
    assert not missing and not changed
    result={'complete':True,'reviewed_commit':'51dd7ab','census_lock_sha256':r6.sha(census.LOCK),'source_verified_from_git_object':True,
      'source_sha256':SHA(upstream),'sites':sites,'replays':len(reports),'local_binding_replays':bindings,'successful_process_records':len(processes),
      'site_seconds_recorded':sum(r['seconds'] for r in frozen['results']),'controls_sha256':r6.sha(args.controls),'controls':12,
      'exposure':exposure,'four_freeze_determinism_independently_verified':False,
      'preservation':{'checked_files':len(before),'missing':missing,'changed':changed,'inventory_path':str(args.before),'inventory_sha256':r6.sha(args.before)},
      'scope':'retained records and exports; fresh full 12-control suite including native exclusion, not 34 fresh kernel replays',
      'program_sha256':r6.sha(Path(__file__)),'live_model_calls':0,'real_credentials_read':0}
    r6.write_json(args.output,result); print(json.dumps({k:result[k] for k in ('complete','replays','local_binding_replays','successful_process_records','controls','preservation')},indent=2))


def J_gzip(path):return json.loads(gzip.decompress(Path(path).read_bytes()))


if __name__=='__main__':main()

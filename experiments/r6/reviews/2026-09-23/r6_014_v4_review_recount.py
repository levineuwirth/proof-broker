import sys,json,hashlib,importlib.util,argparse
from pathlib import Path
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parents[2];sys.path.insert(0,str(root))
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();assert not args.output.exists()
import events,cohort_contract,site_broker,analysis_r6,test_cohort,test_site_broker,test_analysis_r6
out={'locks':{},'suites':{},'artifacts':{}}
for name,path in [('cohort',cohort_contract.LOCK),('deterministic',site_broker.LOCK),('analysis',analysis_r6.LOCK)]:
 d=json.loads(path.read_bytes());bad=[p for p,h in d.items() if hashlib.sha256((root/p).read_bytes()).hexdigest()!=h]
 assert not bad,(name,bad);out['locks'][name]={'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'files':len(d),'mismatches':bad}
for name,mod,file in [('cohort',test_cohort,'R6-014-V3-COHORT-V9-CONTROLS.json'),('deterministic',test_site_broker,'R6-014-DETERMINISTIC-CONTROLS.json'),('analysis',test_analysis_r6,'R6-014-V3-ANALYSIS-CONTROLS.json')]:
 p=root/'reviews/2026-09-23'/file;d=json.loads(p.read_bytes());names=[c['name'] for c in d['checks']]
 assert len(names)==len(set(names))==len(mod.CASES)==d['check_count'] and set(names)==set(mod.CASES)==set(d['expected_cases']) and d['passed'] and all(c['passed'] for c in d['checks'])
 out['suites'][name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'checks':len(names),'exact_case_set':True,'all_passed':True}
for name,pop in [('cohort',sorted((root/'cohort-runs-v9').glob('*/seal.json'))),('deterministic',sorted((root/'census-runs/deterministic-v1').glob('*/*/seal.json'))),('live_fixture',sorted((root/'fixtures/r6-014-v3-live-revisions/runs').glob('*/seal.json')))]:
 nfiles=nev=0
 for p in pop:
  seal=json.loads(p.read_bytes());run=p.parent;rows=events.read(run/'events.ndjson');assert seal['last_event_hash']==rows[-1]['event_hash'] and seal['event_count']==len(rows)
  for k,v in seal['retained_sha256'].items():assert hashlib.sha256((run/k).read_bytes()).hexdigest()==v,(p,k)
  nev+=len(rows);nfiles+=len(seal['retained_sha256'])
 out['artifacts'][name]={'runs':len(pop),'events':nev,'sealed_entries':nfiles,'mismatches':0}
assert [out['artifacts'][n]['runs'] for n in ['cohort','deterministic','live_fixture']]==[16,30,11]
p=root/'reviews/2026-09-23/R6-014-V4-AUDIT-CONTROLS.json';d=json.loads(p.read_bytes())
assert d['passed'] and len(d['rehearsal'])==101 and len(d['live'])==51
spec=importlib.util.spec_from_file_location('review_control_names',root/'reviews/2026-09-23/cohort_v9_audit_controls.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
assert set(d['live'])=={'baseline',*mod.LIVE_EXPECTED,*mod.ACCEPTED_PROBES} and set(d['rehearsal'])==set(mod.base.CONTROLS)
for mode in ['rehearsal','live']:
 for k,v in d[mode].items(): assert v.get('accepted') is True or v.get('rejected') is True or v.get('characterized') is True,(mode,k,v)
out['recorded_audit_controls']={'rehearsal':101,'live':51,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
dp=root/'reviews/2026-09-23/R6-014-V4-DETERMINISTIC-AUDIT-CONTROLS.json'
det=json.loads(dp.read_bytes())
spec=importlib.util.spec_from_file_location('review_det_names',root/'reviews/2026-09-23/deterministic_audit_controls.py');dm=importlib.util.module_from_spec(spec);spec.loader.exec_module(dm)
assert det['passed'] and det['controls']==len((*dm.CONTROLS,*dm.ACCEPTED))==34 and set(det['results'])==set((*dm.CONTROLS,*dm.ACCEPTED))
assert det['results']['baseline']['accepted'] and all(det['results'][k]['accepted'] is False and det['results'][k]['rejected_case']==dm.EXPECTED[k] for k in dm.EXPECTED)
out['deterministic_controls_record']={'sha256':hashlib.sha256(dp.read_bytes()).hexdigest(),'controls':34,'exact_case_set':True}
out['production']={'live_enabled':cohort_contract.config()['live_enabled'],'checkpoint_exists':cohort_contract.CHECKPOINT.exists(),'activation_receipt_exists':cohort_contract.activation_receipt().exists(),'progress_floor_exists':cohort_contract.progress_floor().exists(),'live_ledger_exists':cohort_contract.campaign_ledger(True).path.exists()}
review=root/'reviews/2026-09-23'
for record,source in [('R6-014-V4-AUDIT-CONTROLS.json','cohort_v9_audit'),('R6-014-V4-DETERMINISTIC-AUDIT-CONTROLS.json','deterministic_audit')]:
 d=json.loads((review/record).read_bytes())
 assert d['auditor_sha256']==hashlib.sha256((review/(source+'.py')).read_bytes()).hexdigest()
 assert d['program_sha256']==hashlib.sha256((review/(source+'_controls.py')).read_bytes()).hexdigest()
data=json.loads((review/'R6-014-V4-REVIEW-LIVE.json').read_bytes())['analysis_input']
j=lambda p:json.loads(p.read_bytes())
assert data==j(review/'R6-014-V4-LIVE-FIXTURE-ANALYSIS-INPUT.json')
analysis=analysis_r6.analyse(data,j(root/'census-runs/deterministic-v1/deterministic.json'),j(root/'census-runs/representability-v4/representability.json'),j(root/'fixtures/r6-014-v3-live-revisions/policies/farkas-cohort-v9.json')['pricing']['nano_usd_per_token'])
recorded=j(review/'R6-014-V4-LIVE-FIXTURE-ANALYSIS.json')
assert analysis=={k:v for k,v in recorded.items() if k not in ('program_sha256','input_sha256')}
out['analysis_recomputed']={'input_exact':True,'result_exact':True,'denominators':analysis['denominators'],'integrity_stop':analysis['integrity_stop'],'operational_pause':analysis['operational_pause']}
out['fresh_baselines']={}
for name,count in [('LIVE',550),('REHEARSAL',665),('DETERMINISTIC',539)]:
 p=review/('R6-014-V4-REVIEW-'+name+'.json');d=j(p)
 assert d['accepted'] and d['case_count']==count
 out['fresh_baselines'][name]={'case_count':count,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

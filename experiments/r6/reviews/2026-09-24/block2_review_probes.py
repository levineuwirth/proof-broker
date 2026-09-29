import importlib.util,json,sys,tempfile,shutil,contextlib,io,time,hashlib
from pathlib import Path
from unittest.mock import patch
from types import SimpleNamespace
R=Path(__file__).resolve().parents[2];sys.path.insert(0,str(R))
P=R/'reviews/2026-09-24'
import argparse
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();assert not args.output.exists()
spec=importlib.util.spec_from_file_location('runner_review',P/'run_block2.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
c=m.contract;j=lambda p:json.loads(p.read_bytes()); results={}
class NextLaunch(Exception):pass

def probe(name,existing=False,failure=None,negative=False):
 with tempfile.TemporaryDirectory(prefix='block2-review-') as tmp:
  runs=Path(tmp)/'runs';runs.mkdir();order=('l170','l069') if negative else ('l069','l070');launches=[]
  first=runs/(order[0]+'-draw2')
  def records(run,release=False):
   run.mkdir(exist_ok=True)
   (run/'seal.json').write_text('{}')
   (run/'campaign-reconciliation.json').write_text(json.dumps({'kind':'release' if release else 'send_grant','send_outcome':None if release else 'returned'}))
   (run/'credential-summary.json').write_text(json.dumps({'failure_category':failure}))
   if negative:(run/'certificate-verdict.json').write_text(json.dumps({'accepted':True}))
  if existing:records(first,True)
  def state(task,draw):
   return {'open_reservations':[],'transmissions_consumed':11+len(launches),'committed_micro_usd':1126400+102400*len(launches)}, {'consumed':not(existing and task=='bracket-'+order[0])}
  def fake_run(argv,**kw):
   run=Path(argv[argv.index('--run-dir')+1]);launches.append(run.name)
   if run.name!=first.name:raise NextLaunch()
   records(run);return SimpleNamespace(returncode=1 if failure else 0)
  output=io.StringIO()
  with patch.object(m,'RUNS',runs),patch.object(m,'ORDER',order),patch.object(m,'DRAWS',(2,)),patch.object(m,'slot_state',state),patch.object(m.subprocess,'run',fake_run),patch.object(sys,'argv',['run_block2.py','--credential-file',str(Path(tmp)/'never-created')]),contextlib.redirect_stdout(output):
   try:m.main();status='completed'
   except NextLaunch:status='next_launch_attempted'
   except SystemExit as e:status=str(e)
  return {'status':status,'launches':launches,'stdout':output.getvalue(),'scope':'production runner with synthetic records and mocked sender/ledger; no subprocess or credential read'}
results['resume_sealed_release']=probe('resume',existing=True)
results['returned_binding_failure']=probe('binding',failure='transport_binding_failure')
results['negative_control_acceptance']=probe('negative',negative=True)
assert all(x['status']=='next_launch_attempted' for x in results.values())
# Run authorization only against copies of the complete policy authority and campaign ledgers.
original=c.config();campaign=original['campaign']['id'];authority=[*c.CONFIG.parent.glob(c.CONFIG.stem+'.*'),* (c.LEDGERS/campaign).rglob('*')];authority=[p for p in authority if p.is_file()]
before={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in authority}
with tempfile.TemporaryDirectory(prefix='block2-authorize-review-') as tmp:
 t=Path(tmp);pol=t/'policies';pol.mkdir()
 for p in c.CONFIG.parent.glob(c.CONFIG.stem+'.*'):shutil.copyfile(p,pol/p.name)
 shutil.copytree(c.LEDGERS/campaign,t/'ledgers'/campaign)
 with patch.object(c,'CONFIG',pol/c.CONFIG.name),patch.object(c,'CHECKPOINT',pol/c.CHECKPOINT.name),patch.object(c,'LEDGERS',t/'ledgers'):
  now=time.time()
  digest=c.authorize('Levi Neuwirth','2026-09-24T12:55:26Z',{s:8 for s in c.POSABLE},R/'sources/pricing-approved-campaign-4',
   'R6-014 block 2: eleven posable sites x draws 2-8 under contract v2 (cohort v9); cumulative reservation 9,011,200 micro-USD; every outcome retained',
   'block 2 of the planned cohort (draws 2-8), approved after block 1 was audited and analysed',now=now)
  cfg=c.config();rows,s=c.campaign_ledger(True).snapshot()
  assert cfg['revision']==2 and s['maximum_transmissions']==88 and s['maximum_micro_usd']==9011200 and s['transmissions_consumed']==11 and s['committed_micro_usd']==1126400 and not s['open_reservations']
  results['authorization_copy']={'accepted':True,'evaluated_at_unix':now,'revision':cfg['revision'],'transmission_limit':s['maximum_transmissions'],'money_limit':s['maximum_micro_usd'],'consumed':s['transmissions_consumed'],'committed':s['committed_micro_usd'],'revision_sha256':digest}
assert before=={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in authority}
assert c.config()['revision']==1
results['production_authority_unchanged']=True
with args.output.open('x') as out:json.dump(results,out,indent=2);out.write('\n')
print(json.dumps(results,indent=2))

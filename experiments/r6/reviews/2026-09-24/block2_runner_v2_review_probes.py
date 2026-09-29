import importlib.util,json,sys,contextlib,io,tempfile,shutil
from pathlib import Path
from unittest.mock import patch
R=Path(__file__).resolve().parents[2];P=R/'reviews/2026-09-24';sys.path.insert(0,str(R))
import argparse
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();assert not args.output.exists()
spec=importlib.util.spec_from_file_location('review_controls',P/'block2_runner_controls.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
orig=c.build; out={}
def change_event(p,fn):
 rows=c.m.events.read(p/'events.ndjson');fn(rows);previous='0'*64
 for i,r in enumerate(rows):
  r.pop('event_hash');r['sequence']=i;r['previous_hash']=previous;r['event_hash']=c.m.events.digest(r);previous=r['event_hash']
 (p/'events.ndjson').write_text(''.join(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n' for r in rows))
def mutate(name,site,p):
 view=orig('negative_control_rejected_continues' if site=='l170' else 'proof_continues',site,p)
 if name=='negative_raw_verifier_acceptance':
  def f(rows):
   hits=[r for r in rows if r['event']=='independent_certificate_verdict'];assert len(hits)==1;hits[0]['payload']['accepted']=True
  change_event(p,f)
 elif name=='proof_raw_verifier_rejection':
  def f(rows):
   hits=[r for r in rows if r['event']=='independent_certificate_verdict'];assert len(hits)==1;hits[0]['payload']['accepted']=False
  change_event(p,f)
 elif name=='negative_summary_acceptance':
  v=c.J(p/'credential-summary.json');v['proof_accepted']=True;c.W(p/'credential-summary.json',v)
 elif name=='missing_consumption_receipt':
  def f(rows):
   before=len(rows);rows[:]=[r for r in rows if r['event']!='reconstruction_finished'];assert len(rows)==before-1
  change_event(p,f)
 elif name=='foreign_ledger_task':
  v=c.J(p/'campaign-reconciliation.json');v['task_id']='bracket-l099';c.W(p/'campaign-reconciliation.json',v)
  rows,state=view
  for i,r in enumerate(rows):
   if r['kind'] in c.ledger.TERMINAL and r['reservation_id']==v['reservation_id']:rows[i]=dict(v)
 elif name=='empty_seal_inventory':pass
 else:raise AssertionError(name)
 c.site_network.seal(p,c.J(p/'seal.json')['accepted'])
 if name=='empty_seal_inventory':
  s=c.J(p/'seal.json');s['retained_sha256']={};c.W(p/'seal.json',s)
 return view
for name,site in [('negative_raw_verifier_acceptance','l170'),('proof_raw_verifier_rejection','l069'),('negative_summary_acceptance','l170'),('missing_consumption_receipt','l069'),('foreign_ledger_task','l069'),('empty_seal_inventory','l069')]:
 out[name]={}
 for mode in ('fresh','restart'):
  with patch.object(c,'build',lambda n,s,p:mutate(name,s,p)):
   out[name][mode]=c.exercise(name,site,mode)
  assert out[name][mode]['observed']=='continued',(name,mode,out[name][mode])
# Real ledger rows/state: all eleven baseline runs, and a foreign reconciliation.
raw=(R/'cohort-live-v9/l099-draw1/ledger-after.ndjson').read_bytes()
rows=c.ledger.parse(raw);state=c.ledger.state(rows,rows[0]['campaign_id']);view=rows,state
out['authentic_ledger']={'rows':len(rows),'baselines':{},'foreign_reconciliation':{}}
with patch.object(c.m,'ledger_snapshot',lambda:view):
 for site in c.m.ORDER:
  result=c.m.gate(R/'cohort-live-v9'/f'{site}-draw1',f'bracket-{site}',1)
  assert result[0]=='continue',result;out['authentic_ledger']['baselines'][site]=result
for mode in ('fresh','restart'):
 with tempfile.TemporaryDirectory(prefix='block2-foreign-review-') as t:
  t=Path(t);stage=t/'staged';shutil.copytree(R/'cohort-live-v9/l069-draw1',stage)
  shutil.copyfile(R/'cohort-live-v9/l099-draw1/campaign-reconciliation.json',stage/'campaign-reconciliation.json')
  c.site_network.seal(stage,c.J(stage/'seal.json')['accepted'])
  runs=t/'runs';runs.mkdir();target=runs/'l069-draw1';launches=[]
  if mode=='restart':shutil.copytree(stage,target)
  def sender(argv,**kw):
   run=Path(argv[argv.index('--run-dir')+1]);launches.append(run.name)
   if mode=='fresh' and run==target:
    shutil.copytree(stage,target)
    from types import SimpleNamespace
    return SimpleNamespace(returncode=0)
   raise c.NextLaunch()
  from types import SimpleNamespace
  log=io.StringIO()
  with patch.object(c.m,'ledger_snapshot',lambda:view),patch.object(c.m,'RUNS',runs),patch.object(c.m,'ORDER',('l069','l070')),patch.object(c.m,'DRAWS',(1,)),patch.object(c.m,'subprocess',SimpleNamespace(run=sender)),patch.object(sys,'argv',['runner','--credential-file',str(t/'never-created')]),contextlib.redirect_stdout(log):
   try:c.m.main();result='completed'
   except c.NextLaunch:result='continued'
  assert result=='continued'
  out['authentic_ledger']['foreign_reconciliation'][mode]={'result':result,'launches':launches,'decision':json.loads(log.getvalue().splitlines()[0])}
with args.output.open('x') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'unexpected_continuations':14,'block1_baselines':11,'transmissions':0,'credentials_read':0}))

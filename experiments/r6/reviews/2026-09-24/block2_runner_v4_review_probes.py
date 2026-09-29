import importlib.util,json,sys
from pathlib import Path
from unittest.mock import patch
R=Path(__file__).resolve().parents[2];P=R/'reviews/2026-09-24';sys.path.insert(0,str(R))
import argparse
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();assert not args.output.exists()
spec=importlib.util.spec_from_file_location('review_controls',P/'block2_runner_controls.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
orig=c.build;results={}
def build(name,site,p):
 view=orig('proof_continues',site,p)
 if name=='export_process_missing':
  paths=list((p/'stages/export').glob('*.process.json'));assert len(paths)==1
  chain=c.events.read(p/'events.ndjson');assert len([r for r in chain if r['source']=='supervisor' and r['stage']=='export' and r['event']=='stage_finished'])==1
  paths[0].unlink()
 elif name=='unmatched_stage_receipt':
  chain=c.events.read(p/'events.ndjson');item=next(r for r in chain if r['source']=='supervisor' and r['stage']=='export' and r['event']=='stage_finished')
  chain.insert(-1,{**chain[-2],'source':'supervisor','stage':'unexpected-stage','event':'stage_finished','payload':item['payload']})
  for i,r in enumerate(chain):r['sequence']=i
  c.rechain(p,chain)
 else:raise AssertionError(name)
 c.site_network.seal(p,c.J(p/'seal.json')['accepted']);return view
for name in ('export_process_missing','unmatched_stage_receipt'):
 results[name]={}
 for mode in ('fresh','restart'):
  with patch.object(c,'build',build):results[name][mode]=c.exercise(name,'l069',mode)
  assert results[name][mode]['observed']=='continued',(name,mode,results[name][mode])
with args.output.open('x') as f:json.dump(results,f,indent=2);f.write('\n')
print(json.dumps(results,indent=2))

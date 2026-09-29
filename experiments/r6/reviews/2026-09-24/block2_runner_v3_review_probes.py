import importlib.util,json,sys,argparse
from pathlib import Path
from unittest.mock import patch
R=Path(__file__).resolve().parents[2];P=R/'reviews/2026-09-24';sys.path.insert(0,str(R))
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();assert not args.output.exists()
spec=importlib.util.spec_from_file_location('controls_review',P/'block2_runner_controls.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
orig=c.build;out={}
def build(name,site,p):
 view=orig('proof_continues',site,p);chain=c.events.read(p/'events.ndjson')
 if name=='transport_receipt_binding_false':
  hits=[r for r in chain if r['source']=='supervisor' and r['event']=='transport_validated'];assert len(hits)==1
  assert hits[0]['payload']['response_request_binding']['accepted'] is True
  hits[0]['payload']['response_request_binding']['accepted']=False
 elif name=='terminal_publication_false':
  assert chain[-1]['payload']['publication_accepted'] is None
  chain[-1]['payload']['publication_accepted']=False
 else:raise AssertionError(name)
 c.rechain(p,chain);c.site_network.seal(p,c.J(p/'seal.json')['accepted']);return view
for name in ('transport_receipt_binding_false','terminal_publication_false'):
 out[name]={}
 for mode in ('fresh','restart'):
  with patch.object(c,'build',build):out[name][mode]=c.exercise(name,'l069',mode)
  assert out[name][mode]['observed']=='continued'
print(json.dumps(out,indent=2))
with args.output.open('x') as f:json.dump(out,f,indent=2);f.write('\n')

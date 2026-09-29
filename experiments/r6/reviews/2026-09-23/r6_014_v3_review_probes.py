#!/usr/bin/env python3
"""R6-014 v3 review: retained-only evidence, scoped inventory reads, and prior repairs. No provider or real credential."""
import argparse,copy,importlib.util,json,shutil,sys,tempfile,hashlib
from pathlib import Path
from unittest.mock import patch
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
import cohort_contract as contract,cohort_ledger as ledger
import run as r6

def module(name,file):
 spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def repairs():
 old=module('v2_review_probe','r6_014_v2_review_probes.py');result={}
 try:old.authority();raise AssertionError('rollback accepted')
 except ledger.Failure as e:assert e.code=='cohort_ledger_rolled_back';result['same_activation_rollback']={'rejected':True,'code':e.code}
 try:old.analysis();raise AssertionError('family mutation accepted')
 except ValueError as e:assert 'reviewed declaration map' in str(e);result['family_relabel']={'rejected':True,'detail':str(e)}
 return result

def floor_recovery():
 import test_cohort as tc
 capture=ROOT/'sources/pricing-approved-campaign-3';now=max(v['finished_unix'] for v in tc.v2.source_evidence(capture).values())+3600
 with tempfile.TemporaryDirectory(prefix='r6-014-v3-floor-') as tmp:
  p=Path(tmp)
  with patch.object(contract,'CONFIG',p/'policy.json'),patch.object(contract,'LOCK',p/'lock.json'),patch.object(contract,'CHECKPOINT',p/'checkpoint.json'),patch.object(contract,'LEDGERS',p/'ledgers'):
   contract.freeze(capture);contract.sign('review-synthetic','2026-09-22T21:00:00Z',{s:1 for s in contract.POSABLE},capture,'isolated floor recovery; no transmission',now=now)
   c=contract.config();book=contract.campaign_ledger(True,c)
   with patch.object(book,'_write_floor',side_effect=OSError('synthetic floor persistence fault')):
    try:tc.reserve(book,c,tc.D1,1);raise AssertionError('no injected failure')
    except OSError:pass
   rows=ledger.parse(book.path.read_bytes());assert len(rows)==2
   before=json.loads(book.floor.read_bytes());assert before['rows']==1
   permit=book.find_open(rows[-1]['attempt_id']);after=json.loads(book.floor.read_bytes());assert after['rows']==2
   tc.with_grant(book,permit)
   with patch.object(book,'_write_floor',side_effect=OSError('synthetic terminal floor persistence fault')):
    try:book.reconcile(permit,tc.TERMINATED,tc.SENT,{});raise AssertionError('no injected failure')
    except OSError:pass
   assert json.loads(book.floor.read_bytes())['rows']==2
   terminal=book.find_terminal(permit['reservation_id']);assert terminal['kind']=='send_grant'
   final=json.loads(book.floor.read_bytes());_,state=book.snapshot();assert final['rows']==3 and state['transmissions_consumed']==1 and not state['open_reservations']
   return {'reservation_floor_recovered':[before['rows'],after['rows']],'terminal_floor_recovered':final['rows'],'consumed':1,'open_reservations':0}

def live():
 m=module('v3_live_controls','cohort_v9_audit_controls.py');result={}
 with tempfile.TemporaryDirectory(prefix='r6-014-v3-scan-') as tmp:
  temp=Path(tmp);f=m.live_paths(temp);result['baseline']=m.run_live(f);assert result['baseline']['accepted']
  report_path=f/'operator-disclosure-scan.json';original=m.J(report_path)
  outside=temp/'outside-scan.txt';outside.write_bytes(b'outside declared scan root: synthetic review sentinel\n')
  for name,path in [('absolute',str(outside)),('parent_traversal','../outside-scan.txt')]:
   report=copy.deepcopy(original);raw=outside.read_bytes()
   report['inventory'].append({'path':path,'path_sha256':hashlib.sha256(path.encode()).hexdigest(),'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),'streams':['raw'],'scanned':True,'error':None,'findings':[],'root_index':0})
   report['files_scanned']+=1;m.W(report_path,report)
   reads=[];read=Path.read_bytes
   def observe(p):
    if p.resolve()==outside:reads.append(str(p))
    return read(p)
   with patch.object(Path,'read_bytes',observe):result[name]=m.run_live(f)
   result[name]['outside_file_read']=bool(reads)
  m.W(report_path,original)
 return result

def coverage():
 m=module('v3_coverage_controls','cohort_v9_audit_controls.py');result={}
 for name in ['compressed_disclosure_bin_reported_raw','inventory_file_changed_after_scan','gzip_stream_total_miscounted']:
  assert name in m.LIVE_EXPECTED
  with tempfile.TemporaryDirectory(prefix='r6-014-v3-coverage-') as tmp:
   f=m.live_paths(Path(tmp))
   if not result:
    result['baseline']=m.run_live(f);assert result['baseline']['accepted']
   m.mutate_live(name,f);result[name]=m.run_live(f)
   assert result[name]['accepted'] is False and result[name]['rejected_case']==m.LIVE_EXPECTED[name]
 result['preconditions']=m.PRECONDITIONS
 return result

def deterministic():
 m=module('v3_det_controls','deterministic_audit_controls.py');a=m.audit;result={}
 m.TOOLS.append(a.broker.tools_for(ROOT.parents[1]/'lean-bridge/.lake/packages'))
 def observe(root):
  try:return a.audit(root)
  except a.Rejection as e:return {'accepted':False,'rejected_case':e.case,'detail':str(e)}
 with tempfile.TemporaryDirectory(prefix='r6-014-v3-retained-') as tmp:
  p=Path(tmp);root=p/'runs';shutil.copytree(a.broker.RUNS,root);result['baseline']=observe(root);assert result['baseline']['accepted']
  # These stdout bytes are ignored and listed only as ephemeral in the existing seal.
  run=root/m.PROOF;stdout=run/'stages/export/export.stdout';seal=m.J(run/'seal.json');relative=str(stdout.relative_to(run))
  assert relative in seal['ephemeral_sha256'] and relative not in seal['retained_sha256']
  stdout.rename(p/'preserved-export.stdout')
  result['ephemeral_stdout_absent']=observe(root)
  result['ephemeral_stdout_absent']['retained_solution_present']=(run/'solution.ndjson.gz').exists()
  (p/'preserved-export.stdout').rename(stdout)
  for name in ['local_type_zeroed_resealed','refused_zero_witness_resealed','refused_closer_relabelled_resealed','verification_observation_certificate_altered_resealed','search_workload_not_emptied_resealed','solution_from_other_site_resealed']:
   assert name in m.EXPECTED
   copied=p/name;shutil.copytree(a.broker.RUNS,copied);m.mutate(name,copied);result[name]=observe(copied)
 return result

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('mode',choices=['repairs','floor_recovery','live','coverage','deterministic']);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();assert not args.output.exists()
 result=globals()[args.mode]();args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'mode':args.mode,'output':str(args.output)}))

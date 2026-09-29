import ast, copy, hashlib, importlib.util, json, re, subprocess, sys, tempfile
from pathlib import Path
sys.dont_write_bytecode=True
R=Path('/home/jeans/Repos/research/proof-broker/experiments/r6')
def mod(n,p):
 s=importlib.util.spec_from_file_location(n,p); m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
C=mod('v2_review_runner_controls',R/'reviews/2026-09-24/block2_runner_controls.py')
A=mod('v2_review_audit_controls',R/'reviews/2026-09-28/cohort_v9_audit_amended_2_controls.py')
J=lambda p:json.loads(p.read_bytes())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out={}
record=J(R/'reviews/2026-09-29/R6-014-BLOCK2-RUNNER-V7-CONTROLS.json')
assert record['passed'] and set(record['results'])=={n+':'+mode for n in C.CASES for mode in ('fresh','restart')}
assert record['runner_sha256']==sha(R/'reviews/2026-09-24/run_block2.py')
assert record['program_sha256']==sha(R/'reviews/2026-09-24/block2_runner_controls.py')
results={}
def normalized(value):
 return re.sub(r"/[^'\" ]*/block2-runner-[^/'\" ]+", '<temporary>', json.dumps(value,sort_keys=True))
for name,(site,expected) in C.CASES.items():
 for mode in ('fresh','restart'):
  got=C.exercise(name,site,mode); assert normalized(got)==normalized(record['results'][name+':'+mode]),(name,mode,got)
  results[name+':'+mode]=got
assert set(record['populations'])==set(C.POPULATION)
pop={n:C.population(n) for n in C.POPULATION}
assert pop==record['populations']
out['runner']={'records':len(results),'populations':len(pop),'match_committed_except_temporary_paths':True}
print('runner',out['runner'],flush=True)
def body(p):
 t=ast.parse(p.read_text());f=next(n for n in t.body if isinstance(n,ast.FunctionDef) and n.name=='pre_grant_state');f.body=f.body[1:];return ast.dump(f,include_attributes=False)
assert body(R/'reviews/2026-09-24/run_block2.py')==body(R/'reviews/2026-09-28/cohort_v9_audit_amended_2.py')
assert C.m.PRE_GRANT==A.amended2.PRE_GRANT and C.m.REACHED==A.amended2.REACHED and C.m.CONNECT_PHASE==A.amended2.CONNECT_PHASE
out['predicate_copies_equal']=True
http=J(A.FIXTURE_V4/'runs/l096-draw2/stages/proposal-1/output/http.json')
field_tests={}
with tempfile.TemporaryDirectory() as t:
 stage=Path(t);(stage/'output').mkdir()
 assert A.amended2.pre_grant_state(http,stage) and C.m.pre_grant_state(http,stage)
 fields=set(A.amended2.PRE_GRANT)|set(A.amended2.REACHED)|{'elapsed_ns','connection_attempts','tls_verify_code','failure_category'}
 for field in sorted(fields):
  missing=copy.deepcopy(http);missing.pop(field)
  malformed=copy.deepcopy(http);malformed[field]=[]
  for kind,h in [('missing',missing),('malformed',malformed)]:
   answers=[fn(h,stage) for fn in (A.amended2.pre_grant_state,C.m.pre_grant_state)]
   assert answers==[False,False],(field,kind,answers)
   field_tests[field+':'+kind]=answers
out['required_field_tests']=len(field_tests)
out['direct_pregrant']=A.pre_grant_probe()
record=J(R/'reviews/2026-09-29/R6-014-AMENDMENT-2-V2-AUDIT-CONTROLS.json')
assert record['passed'] and set(record['release'])=={'precondition_amendment_1','baseline',*A.ON_FIXTURE,*A.REGENERATED}
for key,p in {'amended_auditor_sha256':R/'reviews/2026-09-28/cohort_v9_audit_amended_2.py','amendment_1_auditor_sha256':R/'reviews/2026-09-24/cohort_v9_audit_amended.py','program_sha256':R/'reviews/2026-09-28/cohort_v9_audit_amended_2_controls.py','fixture_sha256':A.FIXTURE_V4/'FIXTURE.json'}.items(): assert record[key]==sha(p),key
assert record['pre_grant_probe']==out['direct_pregrant']
prior=J(R/'reviews/2026-09-28/R6-014-AMENDMENT-2-AUDIT-CONTROLS.json')
for group in ('release','shared','live'):
 for name,value in prior[group].items():
  stable=lambda d:{k:v for k,v in d.items() if k!='detail'}
  assert stable(record[group][name])==stable(value),(group,name)
new={n:record['release']['release_pregrant_'+n] for n in (*A.PRE_GRANT_CHANGES,*A.PRE_GRANT_FILES)}
assert all(not r['accepted'] and r['ledger_reconciled_release_as']=='release' for r in new.values())
assert sum(r['rejected_case']=='l096-draw2:failure:classified_and_finalized' for r in new.values())==23
out['retained_audit_controls']={'release':len(record['release']),'shared':len(record['shared']),'live':len(record['live']),'new_negatives':len(new),'hashes_and_names_bound':True,'old_outcomes_identical':True,'full_suite_rerun':False}
print('record bindings verified',flush=True)
with tempfile.TemporaryDirectory() as t:
 f=A.copy_fixture(Path(t),A.amended2); fresh=A.amended2.audit(f/'runs',f/'ledgers/campaigns')
 frozen=J(R/'reviews/2026-09-29/R6-014-AMENDMENT-2-V2-RELEASE-FIXTURE-AUDIT.json')
 assert fresh['accepted'] and fresh['cases']==frozen['cases'] and fresh['case_count']==639
 assert fresh['analysis_input']==J(R/'reviews/2026-09-29/R6-014-AMENDMENT-2-V2-RELEASE-FIXTURE-ANALYSIS-INPUT.json')
 out['fresh_fixture']={'accepted':True,'case_count':639,'exact_case_set':True,'analysis_input_identical':True}
out['analysis_bytes_identical']=((R/'reviews/2026-09-29/R6-014-AMENDMENT-2-V2-RELEASE-FIXTURE-ANALYSIS.json').read_bytes()==(R/'reviews/2026-09-28/R6-014-AMENDMENT-2-RELEASE-FIXTURE-ANALYSIS.json').read_bytes())
assert out['analysis_bytes_identical']
out['passed']=True
Path('/tmp/r6-a2-v2-review-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('passed',flush=True)

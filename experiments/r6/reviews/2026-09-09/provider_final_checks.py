"""Read-only R6-003 recount; writes one new report, never reruns an episode."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
import provider_audit as auditor
import provider_contract as contract
import test_provider as tests
import instrument
import run as r6


def require(condition,detail):
    if not condition:raise ValueError(detail)
def sha(data):return hashlib.sha256(data).hexdigest()
def read(path):return json.loads(path.read_bytes())
def canonical(value):return json.dumps(value,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir',type=Path,default=ROOT/'runs/provider-checkpoint-v1')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();root=args.run_dir.resolve();output=args.output or root/'final-checks.json'
    with output.open('x') as f:json.dump({'passed':False,'status':'recount_started'},f)
    checkpoint=read(root/'checkpoint.json');require(checkpoint['passed'] is True,'checkpoint not complete')
    contract.verify_sources();runtime=contract.verify_runtime()
    suites={}
    for name,names in [('provider-units.json',tests.UNIT_CASES),('provider-native.json',tests.NATIVE_CASES),('provider-audits.json',tests.AUDIT_CASES)]:
        value=read(root/name);counts=Counter(row['name'] for row in value['checks'])
        require(value['passed'] is True and set(counts)==set(names)==set(value['expected_cases']),'suite names/status: '+name)
        require(all(n==1 for n in counts.values()) and all(row['passed'] is True for row in value['checks']),'duplicate/failed check')
        require(value['check_count']==len(names) and checkpoint['suites'][name]=={'sha256':r6.sha(root/name),'count':len(names)},'suite hash/count')
        suites[name]={**checkpoint['suites'][name],'exact_case_set':True,'duplicates':0}
    preserved=read(root/'prior-artifacts.sha256.json')
    bad=[p for p,h in preserved.items() if not (instrument.REPO/p).is_file() or r6.sha(instrument.REPO/p)!=h]
    require(not bad,'prior files changed: '+str(bad))
    positives,negatives,required,binaries={},{},set(),{}
    total_events=total_files=0;relations=Counter();source_count=None
    for name in tests.NATIVE_CASES:
        run=root/name;positive=name in {'d1_valid','c8_valid','d1_alternate_encoding'}
        task=r6.D1 if name.startswith('d1_') else r6.C8
        seal_name='seal.json' if positive else 'failure-seal.json';seal=read(run/seal_name)
        required.add(str((run/seal_name).relative_to(instrument.REPO)))
        for path,digest in seal['retained_sha256'].items():
            actual=run/path;require(actual.resolve().is_relative_to(run),'sealed path escapes run')
            require(r6.sha(actual)==digest,'sealed hash: '+str(actual));required.add(str(actual.relative_to(instrument.REPO)))
        previous='0'*64;events=[]
        for line in (run/'events.ndjson').read_bytes().splitlines():
            row=json.loads(line);digest=row.pop('event_hash')
            require(row['sequence']==len(events) and row['previous_hash']==previous and sha(canonical(row))==digest,'event chain')
            require(row['task_id']==task.id,'event task identity')
            previous=digest;events.append(row)
        require(len(events)==seal['event_count'] and previous==seal['last_event_hash'],'terminal seal')
        total_events+=len(events);total_files+=len(seal['retained_sha256'])
        found=read(run/'provenance/binaries.json')
        for p,h in found.items():
            require(p not in binaries or binaries[p]==h,'binary identity differs across runs');binaries[p]=h
        sources=read(run/'provenance/sources.json')
        if source_count is None:
            for p,v in sources.items():
                blob=subprocess.check_output(['git','-C',str(instrument.REPO),'show',instrument.BASE+':'+p])
                require(sha(blob)==v['base_sha256'],'source differs from SDK base: '+p)
            source_count=len(sources);base_sources=sources
        else:require(sources==base_sources,'SDK source inventories differ across episodes')
        req=read(run/'request.json');relations.update(r['relation'] for r in req['problem']['rows'])
        if positive:
            verdict=auditor.audit(run,task)
            rows={r['name']:r for r in req['problem']['rows']};variables=Counter();constant=0
            witness=read(run/'validated-response.json')['witness']['coefficients']
            for item in witness:
                row=rows[item['hypothesis']];weight=int(item['coefficient']);constant+=weight*int(row['constant'])
                for term in row['terms']:variables[term['variable']]+=weight*int(term['coefficient'])
            require(all(v==0 for v in variables.values()) and constant>0,'positive witness arithmetic')
            if task==r6.D1:require(constant==4,'decisive integer-tightening constant')
            require(all(not d['added'] and not d['removed'] for d in verdict['axiom_delta'].values()),'axiom change')
            positives[name]={'events':len(events),'sealed_files':len(seal['retained_sha256']),
                'seal_sha256':r6.sha(run/seal_name),'request_sha256':verdict['request_sha256'],'solution_sha256':verdict['solution_sha256'],
                'witness':witness,'weighted_constant':str(constant),'weighted_variables':dict(variables),
                'declarations':{k:v['checked_declarations'] for k,v in verdict['final_validation'].items()},'axiom_delta':verdict['axiom_delta'],
                'wrapper_scope':'real VerInf containing context' if task==r6.D1 else 'statement-identical wrapper; local-proof binding only'}
        else:
            checked=auditor.audit_failure(run,task)
            require(checked['audit_accepted'] is True,'negative audit')
            negatives[name]={k:checked[k] for k in ['failure_category','failure_stage','failure_phase','accounting']}
    for p,h in binaries.items():require(r6.sha(Path(p))==h,'recorded binary differs on disk: '+p)
    a,b=positives['d1_valid'],positives['d1_alternate_encoding']
    require(a['request_sha256']==b['request_sha256'] and a['solution_sha256']==b['solution_sha256'],'alternate task/proof disagreement')
    paths=[root/n/'stages/proposal-1/output/outbound-body.json' for n in ['d1_valid','d1_alternate_encoding']]
    require(paths[0].read_bytes()!=paths[1].read_bytes() and read(paths[0])==read(paths[1]),'alternate wire control')
    selected=subprocess.check_output(['git','-C',str(instrument.REPO),'ls-files','-z','--cached','--others','--exclude-standard','--',str(root.relative_to(instrument.REPO))]).split(b'\0')
    excluded={root/'final-checks.json',output}
    selected=sorted({instrument.REPO/p.decode() for p in selected if p}-excluded)
    selection={str(p.relative_to(instrument.REPO)) for p in selected}
    require(required<=selection,'sealed files excluded from publication: '+str(required-selection))
    unique={r6.sha(p):p.stat().st_size for p in selected}
    whitespace=[]
    for path in selected:
        try:text=path.read_bytes().decode('utf-8')
        except UnicodeDecodeError:continue
        for line_number,line in enumerate(text.splitlines(),1):
            if not re.search(r'[ \t]+$',line):continue
            relative=str(path.relative_to(root))
            context=line==' ' and path.suffix=='.patch'
            oversized=relative=='d1_oversized_response/stages/proposal-1/output/provider-response.json' and line==' '*(contract.config()['maximum_provider_response_bytes']+1)
            require(context or oversized,'unqualified trailing whitespace: '+relative+':'+str(line_number))
            whitespace.append({'path':relative,'line':line_number,'bytes':len(line.encode()),'sha256':sha(line.encode()),
                'kind':'unified_diff_context' if context else 'deliberate_oversized_provider_body'})
    syntax=[]
    for name in contract.FILES:
        if name.endswith('.py'):compile((ROOT/name).read_bytes(),str(ROOT/name),'exec');syntax.append(name)
    for doc in [ROOT/'R6-003.md',ROOT/'PROTOCOL.md',ROOT/'LIVE-POLICY-REQUIREMENTS.md']:
        for link in re.findall(r'\]\(([^)]+)\)',doc.read_text()):
            if '://' not in link and not link.startswith('#'):
                target=(doc.parent/link.split('#')[0]).resolve();require(target.exists(),'broken link: '+str(doc)+' -> '+link)
    subprocess.run(['git','-C',str(instrument.REPO),'diff','--check'],check=True)
    result={'passed':True,'recount_utc':datetime.now(timezone.utc).isoformat(),'base_commit':'13baa73',
        'scope':'artifact recomputation only; native suite performed the recorded executions; no remote receipt, compilation or inference attestation',
        'reporter_sha256':r6.sha(Path(__file__)),'checkpoint_sha256':r6.sha(root/'checkpoint.json'),'suites':suites,
        'total_checks':sum(s['count'] for s in suites.values()),'positive_episodes':positives,'negative_episodes':negatives,
        'event_hashes_recomputed':total_events,'sealed_files_checked':total_files,
        'preserved_files':len(preserved),'preserved_changed_or_missing':bad,'preservation_snapshot_sha256':r6.sha(root/'prior-artifacts.sha256.json'),
        'sdk_base_commit':instrument.BASE,'sdk_base_files_checked':source_count,'recorded_binaries_checked_on_disk':len(binaries),
        'runtime_files_checked':len(runtime['stdlib_files']),'runtime_libraries_checked':len(runtime['libraries']),
        'source_lock_sha256':r6.sha(contract.LOCK),'runtime_lock_sha256':r6.sha(contract.RUNTIME),'prompt_sha256':r6.sha(contract.PROMPT),
        'row_instances':{k:relations[k] for k in ['le','eq','lt']},'row_count_scope':str(len(tests.NATIVE_CASES))+' repeated task instances, not distinct obligations',
        'required_publication_paths':len(required),'ignored_required_paths':[],
        'retention':{'files':len(selected),'apparent_bytes':sum(p.stat().st_size for p in selected),'unique_contents':len(unique),
            'unique_content_bytes':sum(unique.values()),'excludes':sorted(str(p.relative_to(root)) for p in excluded if p.is_relative_to(root)),
            'scope':'Git-visible checkpoint directory only; uncompressed content bytes, not Git pack/disk/transfer size'},
        'whitespace_observations':whitespace,'whitespace_scope':'UTF-8 trailing-space scan of selected files; preserved evidence bytes are qualified, not suppressed',
        'python_compile':syntax,'documentation_links':'passed','tracked_diff_check':'passed','additional_native_runs':0,
        'live_model_calls':0,'live_model_cost_usd':0}
    r6.write_json(output,result)
    print(json.dumps({k:result[k] for k in ['passed','total_checks','sealed_files_checked','preserved_files','retention']},indent=2))


if __name__=='__main__':main()

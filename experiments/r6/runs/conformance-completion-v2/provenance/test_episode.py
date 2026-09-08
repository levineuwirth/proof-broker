"""Boundary tests on disposable copies of a real deterministic episode."""
import copy
from collections import Counter
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

import episode
import events
import run as r6
from test_validation import Export


SUITE_VERSION = 'r6-conformance-2'
# This list is intentionally independent of the code that runs the cases.
# Removing a call to record() must not silently shrink a passing suite.
EXPECTED_CASES = frozenset({
    'valid_certificate', 'malformed_certificate', 'invalid_witness',
    'valid_positive_rescaling', 'valid_other_goal_certificate',
    'certificate_for_another_goal', 'changed_dispatch_input',
    'broker_proof_local', 'human_proof_lacks_farkas_reference', 'broker_proof_whole',
    'wrong_target', 'wrong_container', 'missing_declaration', 'forbidden_axiom',
    'sorry', 'native_escape_axiom', 'invalid_proof', 'missing_local_reference',
    'changed_source', 'dropped_event', 'reordered_events', 'duplicated_event',
    'consumed_certificate_substitution', 'truncated_sealed_episode',
    'existing_run_directory', 'append_to_closed_episode',
    'resource_normal_completion',
    'resource_cpu', 'resource_cpu_descendants_reaped',
    'resource_wall', 'resource_wall_descendants_reaped',
    'resource_memory', 'resource_memory_descendants_reaped',
    'resource_output', 'resource_output_descendants_reaped',
})


def require_complete_suite(results):
    counts = Counter(row['case'] for row in results)
    missing = sorted(EXPECTED_CASES - counts.keys())
    unexpected = sorted(counts.keys() - EXPECTED_CASES)
    duplicates = sorted(name for name, count in counts.items() if count != 1)
    failed = sorted(row['case'] for row in results if row.get('passed') is not True)
    if missing or unexpected or duplicates or failed:
        raise AssertionError(f'Incomplete conformance suite: missing={missing}, '
                             f'unexpected={unexpected}, duplicates={duplicates}, failed={failed}')


def finish_suite(out, saved, results):
    # Check completeness before any terminal success or completion event.
    require_complete_suite(results)
    episode.audit(saved)
    provenance=out/'provenance'
    provenance.mkdir()
    for name in ['test_episode.py','test_validation.py','episode.py','supervise.py','events.py','validate/resource_fixture.c']:
        target=provenance/name
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(r6.ROOT/name,target)
    r6.write_json(out/'tests.json',{'suite_version':SUITE_VERSION,
        'expected_cases':sorted(EXPECTED_CASES),
        'source_episode':str(saved),'source_seal_sha256':r6.sha(saved/'seal.json'),
        'passed':True,'checks':results,
        'artifact_sha256':{str(p.relative_to(out)):r6.sha(p) for p in sorted(out.rglob('*'))
            if p.is_file() and p.name not in {'tests.json','events.ndjson','proof.ndjson','verdict.json','resource-fixture'}}})
    events.append(out,'tests','tests_finished',{'passed':True,'checks':len(results),
        'tests_sha256':r6.sha(out/'tests.json')})
    print(f'{len(results)} boundary checks passed: {out}/tests.json',flush=True)


def integration_tests(out, saved):
    saved = (saved or r6.ROOT/'runs/golden-broker-v1').resolve()
    episode.audit(saved)
    _, _, checker = r6.build_tools(only_checker=True)
    verifier = r6.ROOT/'.cache/instrumented/sdk/_build/default/validate/verify_certificate.exe'
    recorded = r6.read_json(saved/'provenance/binaries.json')
    if r6.sha(verifier) != recorded[str(verifier)] or r6.sha(checker) != recorded[str(checker)]:
        raise ValueError('Test checker binaries differ from the golden episode')
    results = []

    def record(name, expected, observed):
        if expected != observed:
            raise AssertionError(f'{name}: expected {expected}, observed {observed}')
        results.append({'case':name,'expected':expected,'observed':observed,'passed':True})
        r6.write_json(out/'tests.json',{'suite_version':SUITE_VERSION,
            'expected_cases':sorted(EXPECTED_CASES),
            'source_episode':str(saved),'passed':False,'checks':results})
        print(f'PASS {name}: {observed}',flush=True)

    def cert_case(name, packet, stage, accepted=False):
        inp=out/'inputs'/name
        inp.mkdir(parents=True)
        r6.write_json(inp/'evidence.json',packet)
        try:
            episode.stage(out,name,verifier,['/evidence.json','/out/verdict.json'],[(inp/'evidence.json','/evidence.json')])
        except RuntimeError:
            pass
        report=r6.read_json(out/f'stages/{name}/output/verdict.json')
        proc=r6.read_json(out/f'stages/{name}/{name}.process.json')
        record(name,{'accepted':accepted,'stage':stage,'process_success':accepted},
               {'accepted':report['accepted'],'stage':report['stage'],'process_success':proc['exit_code']==0})

    packet=r6.read_json(saved/'evidence.json')
    cert_case('valid_certificate',packet,'certificate_verification',True)
    bad=copy.deepcopy(packet)
    del bad['certificate']['payload']
    cert_case('malformed_certificate',bad,'certificate_decode')
    bad=copy.deepcopy(packet)
    for coefficient in bad['certificate']['payload']['witness_data']['coefficients']:
        coefficient['coefficient']='0'
    cert_case('invalid_witness',bad,'certificate_verification')
    valid=copy.deepcopy(packet)
    for coefficient in valid['certificate']['payload']['witness_data']['coefficients']:
        coefficient['coefficient']=str(2*int(coefficient['coefficient']))
    cert_case('valid_positive_rescaling',valid,'certificate_verification',True)

    # A genuinely valid certificate for a distinct, weaker arithmetic target.
    other=copy.deepcopy(packet)
    def weaken(node):
        if isinstance(node,dict):
            if node.get('node')=='NumLit' and node.get('value')=='16777216':
                node['value']='16777215'
                return 1
            return sum(weaken(v) for v in node.values())
        if isinstance(node,list): return sum(map(weaken,node))
        return 0
    assert weaken(other['final_ir']['goal']['shell'])==1
    other['input_ir']=copy.deepcopy(other['final_ir'])
    hash_ir='sha256:'+events.digest(other['final_ir'])
    other['trace']={'trace_version':packet['trace']['trace_version'],
                    'initial_ir_hash':hash_ir,'final_ir_hash':hash_ir,'entries':[]}
    other['certificate']['goal']=copy.deepcopy(other['final_ir']['goal'])
    other['certificate']['dispatch_context_hash']=hash_ir
    other['certificate']['rewrite_trace_hash']='sha256:'+events.digest(other['trace'])
    cert_case('valid_other_goal_certificate',other,'certificate_verification',True)
    wrong=copy.deepcopy(packet)
    wrong['certificate']=other['certificate']
    cert_case('certificate_for_another_goal',wrong,'certificate_verification')
    bad=copy.deepcopy(packet)
    bad['input_ir']['goal']=other['input_ir']['goal']
    cert_case('changed_dispatch_input',bad,'input_trace_binding')

    with tempfile.TemporaryDirectory(prefix='r6-proof-corruptions-') as temp:
        temp=Path(temp)
        challenge,solution=temp/'challenge.ndjson',temp/'solution.ndjson'
        r6.unpack(r6.TASK/'challenge.ndjson.gz',challenge)
        r6.unpack(saved/'solution.ndjson.gz',solution)
        original=Export(solution)
        human=Export(challenge)
        def proof_case(name,edit,config,expected_stage,accepted=False):
            data=copy.deepcopy(original)
            edit(data)
            path=out/'inputs'/name/'proof.ndjson'
            path.parent.mkdir(parents=True)
            data.write(path)
            config_path=path.parent/'policy.json'
            r6.write_json(config_path,config)
            try:
                episode.stage(out,name,checker,['/challenge.ndjson','/solution.ndjson','/policy.json','/out/verdict.json'],
                    [(challenge,'/challenge.ndjson'),(path,'/solution.ndjson'),(config_path,'/policy.json')])
            except RuntimeError:
                pass
            report_path=out/f'stages/{name}/output/verdict.json'
            report=r6.read_json(report_path)
            r6.pack(path,path.with_suffix('.ndjson.gz'))
            r6.pack(report_path,report_path.with_suffix('.raw.json.gz'))
            record(name,{'accepted':accepted,'stage':expected_stage},
                   {'accepted':report['accepted'],'stage':report['stage']})
        proof_case('broker_proof_local',lambda _:None,episode.local_policy(),'complete',True)
        proof_case('human_proof_lacks_farkas_reference',lambda d:setattr(d,'rows',human.rows),
                   episode.local_policy(),'local_proof_binding')
        proof_case('broker_proof_whole',lambda _:None,r6.policy([r6.WHOLE],True),'complete',True)
        proof_case('wrong_target',lambda d:d.make_trivial(r6.LOCAL),r6.policy([r6.LOCAL]),'challenge_match')
        proof_case('wrong_container',lambda d:d.make_trivial(r6.WHOLE),r6.policy([r6.WHOLE],True),'challenge_match')
        proof_case('missing_declaration',lambda d:d.rows.remove(d.declarations[r6.LOCAL][0]),r6.policy([r6.LOCAL]),'challenge_match')
        proof_case('forbidden_axiom',lambda d:d.axiom_proof('R6_forbidden'),r6.policy([r6.LOCAL]),'axiom_policy')
        proof_case('sorry',lambda d:d.axiom_proof('sorryAx'),r6.policy([r6.LOCAL]),'axiom_policy')
        proof_case('native_escape_axiom',lambda d:d.axiom_proof('R6_native_decide_fresh_axiom'),r6.policy([r6.LOCAL]),'axiom_policy')
        proof_case('invalid_proof',lambda d:d.theorem(r6.LOCAL).update(value=d.const_expr('True.intro')),r6.policy([r6.LOCAL]),'kernel_replay')
        proof_case('missing_local_reference',lambda d:d.inline_local(),r6.policy([r6.WHOLE],True),'local_proof_binding')

    def rejected(name,fn):
        try: fn()
        except (ValueError,AssertionError,OSError): record(name,'rejected','rejected')
        else: raise AssertionError(f'{name} was accepted')

    rejected('changed_source',lambda:r6.instrument((r6.TASK/'Pristine.lean').read_text().replace('(2:ℕ)^24 + 2 * Zmax ≤ P','(2:ℕ)^23 + 2 * Zmax ≤ P',1)))
    with tempfile.TemporaryDirectory(prefix='r6-event-corruptions-') as temp:
        temp=Path(temp)
        rows=events.read(saved/'events.ndjson')
        path=temp/'events.ndjson'
        for name,mutant in [('dropped_event',rows[:4]+rows[5:]),
                            ('reordered_events',rows[:4]+[rows[5],rows[4]]+rows[6:]),
                            ('duplicated_event',rows[:5]+[rows[4]]+rows[5:])]:
            path.write_bytes(b''.join(events.canonical(r)+b'\n' for r in mutant))
            rejected(name,lambda:events.read(path))
        # Recompute hashes to exercise cross-stage certificate binding itself.
        changed=copy.deepcopy(rows)
        for row in changed:
            if row['event']=='reconstruction_finished':
                row['payload']['data']['certificate']['backend']['version']='substituted'
        previous=events.ZERO
        for row in changed:
            row.pop('event_hash')
            row['previous_hash']=previous
            previous=events.digest(row)
            row['event_hash']=previous
        path.write_bytes(b''.join(events.canonical(r)+b'\n' for r in changed))
        rejected('consumed_certificate_substitution',lambda:episode.evidence(temp))
        seal=r6.read_json(saved/'seal.json')
        for name in seal['retained_sha256']:
            target=temp/name
            target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(saved/name,target)
        shutil.copyfile(saved/'seal.json',temp/'seal.json')
        lines=(temp/'events.ndjson').read_bytes().splitlines(True)
        (temp/'events.ndjson').write_bytes(b''.join(lines[:-1]))
        rejected('truncated_sealed_episode',lambda:episode.audit(temp))
    rejected('existing_run_directory',lambda:saved.mkdir(exist_ok=False))
    rejected('append_to_closed_episode',lambda:events.append(saved,'test','unexpected',{}))

    fixture=out/'resource-fixture'
    subprocess.run(['cc','-O0',str(r6.ROOT/'validate/resource_fixture.c'),'-o',str(fixture)],check=True)
    name='resource_normal_completion'
    episode.stage(out,name,fixture,['normal'],[],wall=8,cpu=10,
                  memory=192*1024**2,output_limit=128*1024)
    stats=r6.read_json(out/f'stages/{name}/{name}.process.json')
    limit_events=[row for row in events.read(out/'events.ndjson')
                  if row['stage']==name and row['event']=='resource_limit']
    record(name,{'exit_code':0,'resource_exhausted':None,'monitor_error':None,
                 'workload_empty_after_cleanup':True,'resource_limit_events':0,
                 'stdout':'normal completion\n'},
                {**{key:stats[key] for key in ['exit_code','resource_exhausted',
                    'monitor_error','workload_empty_after_cleanup']},
                 'resource_limit_events':len(limit_events),
                 'stdout':(out/f'stages/{name}/{name}.stdout').read_text()})
    for mode,expected in [('cpu','cpu_time'),('wall','wall_time'),('memory','memory'),('output','output_bytes')]:
        name='resource_'+mode
        try:
            episode.stage(out,name,fixture,[mode],[],wall=2 if mode=='wall' else 8,
                          cpu=1 if mode=='cpu' else 10,memory=192*1024**2,output_limit=128*1024)
        except RuntimeError:
            pass
        stats=r6.read_json(out/f'stages/{name}/{name}.process.json')
        record(name,expected,stats['resource_exhausted'])
        record(name+'_descendants_reaped',True,stats['workload_empty_after_cleanup'])
    finish_suite(out, saved, results)

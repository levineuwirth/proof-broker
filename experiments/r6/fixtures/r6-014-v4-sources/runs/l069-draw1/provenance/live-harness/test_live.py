#!/usr/bin/env python3
"""R6-005 exact-name-gated units, native HTTPS episodes and audit mutations."""
import argparse
import copy
from contextlib import redirect_stdout,redirect_stderr
import json
from pathlib import Path
import shutil
import ssl
import sys
import tempfile
from unittest import mock

sys.dont_write_bytecode=True
import credential
import credential_audit
import credential_contract
import envelope_audit
import episode
import events
import live_audit as auditor
import live_budget
import live_contract as contract
import live_episode as harness
import live_https
import live_payload as wire
import payload
import provider_audit
import publication
import run as r6
import test_credentials as prior_tests
from test_proposals import Suite,require,rejected,assert_complete
from test_task_identity import rehash

UNIT_CASES='''sources_locked credential_file_format credential_header_injection input_semantics_preserved response_echo_only
http_endpoint_rejected verification_disabled_rejected hostname_disabled_rejected tls_floor_rejected
money_exhausted input_bytes_exhausted request_exhausted durable_attempts campaign_attempts
unknown_usage_not_zero truncated_ledger_rejected ledger_policy_rejected ledger_amount_rejected
model_not_attested sampling_explicit no_live_cli no_proxy_environment
source_binding_changed missing_case duplicate_case'''.split()
NATIVE_CASES=['d1_valid','c8_valid','c8_invalid_witness']+['d1_'+c for c in harness.CASES if c!='valid']
AUDIT_MUTATIONS={
    'wrong_policy':'frozen policy binding','wrong_source_lock':'frozen policy binding',
    'wrong_reservation':'reservation differs','wrong_ledger':'durable reservation differs',
    'wrong_tls_peer':'TLS observation binding','wrong_ca':'trust root binding',
    'headers_before_tls':'headers precede TLS validation','hidden_retry':'extra transport attempt',
    'wrong_receipt':'credential receipt differs','wrong_usage':'accounting differs',
    'wrong_model_metadata':'provider metadata differs','wrong_component':'transport report differs',
    'wrong_mount':'HTTPS command permits','wrong_budget':'HTTPS resource limit changed',
    'wrong_reconstruction_context':'reconstruction context differs',
    'wrong_certificate':'assembled witness differs','wrong_type':'frozen type/axiom policy',
    'wrong_axiom':'frozen type/axiom policy','missing_declaration':'missing expected declaration',
    'wrong_proposer':'verdict differs: witness_proposer','missing_shared_checker':'artifact not retained',
    'publication_hash':'recorded scan provenance differs','publication_target':'scan inventory omits',
}
HISTORICAL={'credential_d1':'runs/credential-checkpoint-v3/d1_valid',
    'provider_c8':'runs/provider-checkpoint-v1/c8_valid','envelope_d1':'runs/envelope-checkpoint-v1/d1_valid',
    'golden_c8':'runs/golden-c8-v1'}
AUDIT_CASES=['d1_retained_only','c8_retained_only',*AUDIT_MUTATIONS,*HISTORICAL,'prior_files_preserved']
SUITES={'focused.json':UNIT_CASES,'native.json':NATIVE_CASES,'audits.json':AUDIT_CASES}
PRESERVATION=r6.ROOT/'reviews/2026-09-09/R6-005-PRESERVATION.json'
PRESERVATION_SHA='32b4840cc4a4d4914420c5b853d8609312f324a9e2dc74e803c7569d65725484'


def check_preservation():
    require(r6.sha(PRESERVATION)==PRESERVATION_SHA,'preservation inventory differs from its pre-work anchor')
    inventory=r6.read_json(PRESERVATION)
    for name,h in inventory['files'].items():
        require(r6.sha(r6.ROOT.parents[1]/name)==h,'prior artifact changed: '+name)
    return {'checked_files':len(inventory['files']),'inventory_sha256':PRESERVATION_SHA,'git_base':inventory['git_base'],
        'scope':'pre-work Git-selected bytes, including closed uncommitted R6-004'}


def unit_suite(root):
    suite=Suite(root/'focused.json',UNIT_CASES)
    c=contract.config()
    prepared=r6.read_json(r6.ROOT/'runs/provider-checkpoint-v1/d1_valid/prepared.json')
    request=wire.request(r6.D1,prepared); args=wire.arguments(request)
    suite.case('sources_locked',lambda: contract.verify_sources() or {'policy_sha256':r6.sha(contract.CONFIG),'source_lock_sha256':r6.sha(contract.LOCK)})
    def credential_format():
        with credential.delivery(credential.nonce()) as (canary,path):
            require(live_https.read_credential(path)==credential.header(canary))
            require(path.stat().st_mode & 0o777 == 0o600)
        require(not path.exists())
        return {'read_exact_header':True,'removed':True}
    suite.case('credential_file_format',credential_format)
    def credential_injection():
        with tempfile.TemporaryDirectory(prefix='r6-005-bad-header-') as tmp:
            p=Path(tmp)/'header'; p.write_text('Bearer example\nInjected: header\n')
            return rejected(lambda:live_https.read_credential(p),'credential_format')
    suite.case('credential_header_injection',credential_injection)
    def semantics():
        value=payload.strict_json(request)
        require(value['problem']['rows']==prepared['rows'])
        require({row['relation'] for row in prepared['rows']}<= {'le','eq'})
        require(args['input'][0]['content'].encode()==contract.PROMPT.read_bytes())
        require(args['input'][1]['content'].endswith(request.decode()))
        require(wire.envelope_report(live_https.encode(args),request)['accepted'] is True)
        require('_proof_' not in request.decode() and 'declaration_placeholder' not in request.decode())
        return {'rows':len(prepared['rows']),'message_bytes':sum(len(m['content'].encode()) for m in args['input'])}
    suite.case('input_semantics_preserved',semantics)
    def echo():
        f=harness.canned(r6.D1,request,'invalid_witness')
        text,metadata=wire.response(f['body'].encode(),200)
        require(wire.envelope_payload.echo(text,request)['accepted'] is True)
        require(wire.envelope_payload.response(text,request)['witness']['coefficients'][0]['coefficient']=='1')
        return {'echo_passes_ignored_arithmetic':True,'arithmetic_result':'checked separately by native invalid_witness'}
    suite.case('response_echo_only',echo)
    def reject_tls(kind):
        context=ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT); policy=copy.deepcopy(c)
        if kind=='http': policy['endpoint']['scheme']='http'
        elif kind=='verify': context.check_hostname=False; context.verify_mode=ssl.CERT_NONE
        elif kind=='hostname': context.check_hostname=False
        elif kind=='minimum': context.minimum_version=ssl.TLSVersion.MINIMUM_SUPPORTED
        return rejected(lambda:live_https.connection(policy,context),'policy')
    for name,kind in [('http_endpoint_rejected','http'),('verification_disabled_rejected','verify'),
                      ('hostname_disabled_rejected','hostname'),('tls_floor_rejected','minimum')]:
        suite.case(name,lambda kind=kind:reject_tls(kind))
    suite.case('money_exhausted',lambda:rejected(lambda:wire.reservation(args,spent=c['limits']['total_micro_usd']),'Monetary'))
    def input_limit():
        other=copy.deepcopy(args); other['input'][0]['content']='x'*(c['limits']['message_utf8_bytes']+1)
        return rejected(lambda:wire.reservation(other),'byte admission')
    suite.case('input_bytes_exhausted',input_limit)
    suite.case('request_exhausted',lambda:rejected(lambda:wire.reservation(args,attempts=1),'Request budget'))
    def ledger_test(kind):
        with tempfile.TemporaryDirectory(prefix='r6-005-budget-') as tmp:
            path=Path(tmp)/'ledger'; live_budget.reserve(path,'first',args,wire.sha(request))
            if kind=='durable':
                before=path.read_bytes(); result=rejected(lambda:live_budget.reserve(path,'first',args,wire.sha(request)),'Request budget')
                require(path.read_bytes()==before); return result
            if kind=='campaign':
                live_budget.reserve(path,'second',args,wire.sha(request))
                return rejected(lambda:live_budget.reserve(path,'third',args,wire.sha(request)),'Campaign request')
            if kind=='truncated':
                path.write_bytes(path.read_bytes()[:-1]); return rejected(lambda:live_budget.reserve(path,'second',args,wire.sha(request)),'Truncated')
            row=json.loads(path.read_bytes())
            if kind=='policy': row['policy_sha256']='0'*64
            else: row['reservation']['reserved_micro_usd']=1
            path.write_bytes(events.canonical(row)+b'\n')
            return rejected(lambda:live_budget.reserve(path,'second',args,wire.sha(request)),
                'identity differs' if kind=='policy' else 'amount differs')
    suite.case('durable_attempts',lambda:ledger_test('durable'))
    suite.case('campaign_attempts',lambda:ledger_test('campaign'))
    def unknown():
        fixture=harness.canned(r6.C8,wire.request(r6.C8,r6.read_json(r6.ROOT/'runs/provider-checkpoint-v1/c8_valid/prepared.json')),'valid')
        text,metadata=wire.response(fixture['body'].encode(),200)
        require(metadata['usage']['input_tokens'] is None and metadata['usage']['cost_usd'] is None)
        return metadata['usage']
    suite.case('unknown_usage_not_zero',unknown)
    suite.case('truncated_ledger_rejected',lambda:ledger_test('truncated'))
    suite.case('ledger_policy_rejected',lambda:ledger_test('policy'))
    suite.case('ledger_amount_rejected',lambda:ledger_test('amount'))
    suite.case('model_not_attested',lambda:require(c['model']['model_computation_attested'] is False) or c['model'])
    suite.case('sampling_explicit',lambda:require(args['reasoning']=={'effort':'medium'} and 'temperature' not in args and 'top_p' not in args) or c['sampling'])
    suite.case('no_live_cli',lambda:require(c['live_enabled'] is False and '--endpoint' not in Path(live_https.__file__).read_text()) or 'canned CLI only')
    suite.case('no_proxy_environment',lambda:require('environ' not in Path(live_https.__file__).read_text().replace('environment','')) or 'stdlib direct connection')
    def lock_guard():
        with mock.patch.object(contract,'source_lock',return_value={p:('0'*64 if p=='live_https.py' else h) for p,h in contract.source_lock().items()}):
            return rejected(contract.verify_sources,'locked source changed')
    suite.case('source_binding_changed',lock_guard)
    suite.case('missing_case',lambda:rejected(lambda:assert_complete(UNIT_CASES[:-1],UNIT_CASES),'missing/extra'))
    suite.case('duplicate_case',lambda:rejected(lambda:assert_complete(UNIT_CASES+[UNIT_CASES[0]],UNIT_CASES),'duplicate'))
    suite.finish()


def expected_native(name):
    task=r6.C8 if name.startswith('c8_') else r6.D1; case=name[3:]
    categories={ 'untrusted_ca':'tls_certificate_verification','wrong_hostname':'tls_certificate_verification',
        'expired_certificate':'tls_certificate_verification','redirect':'provider_http_error','http429':'provider_http_error',
        'http503':'provider_http_error','reflected_canary':'provider_http_error','missing_credential':'credential_receipt_failure',
        'wrong_credential':'credential_receipt_failure','wrong_echo':'transport_binding_failure','invalid_witness':'certificate_verification',
        'malformed':'response_decode','wrong_model':'provider_model_binding','wrong_service_tier':'provider_service_tier',
        'incomplete':'provider_incomplete','output_budget':'provider_output_budget','input_budget':'provider_input_budget',
        'truncated_response':'transport_incomplete_response'}
    return task,case,{'accepted':case=='valid','proof_accepted':case=='valid',
        'credential_receipt_accepted':case not in ('missing_credential','wrong_credential','untrusted_ca','wrong_hostname','expired_certificate'),
        'publication_accepted':case!='reflected_canary',
        'failure_category':'outbound_envelope_binding' if case.startswith(('altered_','omitted_')) else categories.get(case)}


def native_suite(root):
    suite=Suite(root/'native.json',NATIVE_CASES)
    for name in NATIVE_CASES:
        def one(name=name):
            task,case,wanted=expected_native(name); target=root/name; target.mkdir()
            log=root/(name+'.log')
            with log.open('x') as stream,redirect_stdout(stream),redirect_stderr(stream):
                print('R6-005 native',name,flush=True)
                result=harness.execute(target,task,case,r6.ROOT.parents[1]/'lean-bridge/.lake/packages')
                print(json.dumps(result),flush=True)
            require(result==wanted,'native boundary differs: '+str(result))
            audited=auditor.audit(target,task)
            for k,v in wanted.items(): require(audited[k]==v,'audit differs: '+k)
            return {'task_id':task.id,'case':case,'seal_sha256':r6.sha(target/'seal.json'),
                    'process_log_sha256':r6.sha(log),'observations':audited}
        suite.case(name,one)
    suite.finish()


def edit(path,fn):
    data=r6.read_json(path); before=events.canonical(data); fn(data)
    require(events.canonical(data)!=before,'mutation changed nothing')
    r6.write_json(path,data)


def audit_suite(root):
    suite=Suite(root/'audits.json',AUDIT_CASES)
    for name,task in [('d1_retained_only',r6.D1),('c8_retained_only',r6.C8)]:
        def check(task=task):
            with tempfile.TemporaryDirectory(prefix='r6-005-retained-') as tmp:
                target=Path(tmp)/'episode'; prior_tests.retained_copy(root/('d1_valid' if task==r6.D1 else 'c8_valid'),target)
                return auditor.audit(target,task)
        suite.case(name,check)
    def change(root,name):
        if name in ('wrong_policy','wrong_source_lock'):
            edit(root/'search-policy.json',lambda v:v.update({('config_sha256' if name=='wrong_policy' else 'source_lock_sha256'):'0'*64}))
        elif name=='wrong_reservation': edit(root/'reservation.json',lambda v:v.update(reserved_micro_usd=1))
        elif name=='wrong_ledger':
            value=json.loads((root/'reservation-ledger.ndjson').read_bytes()); value['reservation']['reserved_micro_usd']=1
            (root/'reservation-ledger.ndjson').write_bytes(events.canonical(value)+b'\n')
        elif name in ('wrong_tls_peer','wrong_ca','headers_before_tls','hidden_retry'):
            def alteration(v):
                if name=='wrong_tls_peer': v['tls']['peer_certificate_sha256']='0'*64
                elif name=='wrong_ca': v['ca_bundle_sha256']='0'*64
                elif name=='headers_before_tls': v['header_send_at_ns']=v['tls_verified_at_ns']-1
                else: v['connection_attempts']=2
            edit(root/'stages/proposal-1/output/http.json',alteration)
        elif name=='wrong_receipt': edit(root/'credential-receipt.json',lambda v:v.update(observed_authorization_sha256='0'*64))
        elif name=='wrong_usage': edit(root/'accounting.json',lambda v:v['usage'].update(input_tokens=0))
        elif name=='wrong_model_metadata': edit(root/'provider-metadata.json',lambda v:v.update(reported_model='forged-model'))
        elif name=='wrong_component': edit(root/'transport-validation.json',lambda v:v['outbound_envelope'].update(mismatches=[{'component':'wrong_component'}]))
        elif name=='wrong_mount': edit(root/'stages/proposal-1/command.json',lambda v:v['argv'].extend(['--share-net']))
        elif name=='wrong_budget': edit(root/'stages/proposal-1/command.json',lambda v:v.update(wall_seconds=61))
        elif name=='wrong_reconstruction_context': edit(root/'stages/reconstruct/output/context.json',lambda v:v.update(target='False'))
        elif name=='wrong_certificate':
            # Keep assembly/certificate consistency, change only proposal relation.
            for p in ('evidence.json','stages/assembly/output/evidence.json'):
                edit(root/p,lambda v:v['certificate']['payload']['witness_data']['coefficients'][0].update(coefficient='1'))
        elif name in ('wrong_type','wrong_axiom','missing_declaration'):
            import gzip
            p=root/'validation-local.raw.json.gz'; value=json.loads(gzip.decompress(p.read_bytes()))
            if name=='wrong_type': value['targets'][0]['type_repr']='False'
            elif name=='wrong_axiom': value['targets'][0]['axioms'].append('sorryAx')
            else: value['targets'][0]['name']='missing'
            p.write_bytes(gzip.compress(events.canonical(value),mtime=0))
        elif name=='wrong_proposer': edit(root/'verdict.json',lambda v:v.update(witness_proposer='frontier_model'))
        elif name=='missing_shared_checker': (root/'provenance/envelope-harness/envelope_proof_audit.py').unlink()
        elif name in ('publication_hash','publication_target'): pass
        else: raise AssertionError(name)
    for name,message in AUDIT_MUTATIONS.items():
        def probe(name=name,message=message):
            with tempfile.TemporaryDirectory(prefix='r6-005-mutation-') as tmp:
                target=Path(tmp)/'episode'; prior_tests.retained_copy(root/'d1_valid',target)
                require(auditor.audit(target,r6.D1)['accepted'] is True)
                ephemeral=r6.read_json(target/'seal.json')['ephemeral_sha256']
                change(target,name)
                prior_tests.recompute_publication(target,True,ephemeral)
                if name=='publication_hash': edit(target/'publication-scan.json',lambda v:v['inventory'][0].update(sha256='0'*64))
                if name=='publication_target':
                    def omit(v):
                        lost=v['inventory'].pop(0);require(not lost['findings'] and lost['streams']==['raw'])
                        v['files_scanned']-=1
                    edit(target/'publication-scan.json',omit)
                if name in ('publication_hash','publication_target'):
                    seed=r6.read_json(target/'credential-canary.json')['nonce']
                    r6.write_json(target/'publication-final.json',publication.final_record(target/'publication-scan.json',credential.derive(seed),seed))
                    rows=events.read(target/'events.ndjson')
                    rows[-1]['payload'].update(publication_scan_sha256=r6.sha(target/'publication-scan.json'),publication_final_sha256=r6.sha(target/'publication-final.json'))
                    (target/'events.ndjson').write_bytes(rehash(rows))
                    harness.publication_driver.seal(target,True,ephemeral)
                result=rejected(lambda:auditor.audit(target,r6.D1),message)
                return {**result,'unmutated_copy_passes':True,'mutation_count':1}
        suite.case(name,probe)
    for name,path in HISTORICAL.items():
        def historical(name=name,path=path):
            p=r6.ROOT/path
            if name.startswith('credential'): return credential_audit.audit(p,r6.D1)
            if name.startswith('provider'): return provider_audit.audit(p,r6.C8)
            if name.startswith('envelope'): return envelope_audit.audit(p,r6.D1)
            return {'accepted':episode.audit(p,r6.C8)['accepted']}
        suite.case(name,historical)
    suite.case('prior_files_preserved',check_preservation)
    suite.finish()


def recount(root,*,publication_scan=True):
    index=r6.read_json(root/'checkpoint.json')
    require(index['passed'] is True,'checkpoint is incomplete')
    require(index['policy_sha256']==r6.sha(contract.CONFIG),'checkpoint policy differs')
    require(index['source_lock_sha256']==r6.sha(contract.LOCK),'checkpoint source lock differs')
    require(index['live_model_calls']==0,'checkpoint live count differs')
    require(set(index['suites'])==set(SUITES),'suite population differs')
    count=0
    for file,names in SUITES.items():
        value=r6.read_json(root/file)
        require(index['suites'][file]=={'sha256':r6.sha(root/file),'count':len(names)},'suite hash/count binding differs')
        assert_complete([x['name'] for x in value['checks']],names)
        require(value['passed'] is True and all(x['passed'] is True for x in value['checks']) and value['check_count']==len(names),'suite incomplete')
        require(value['expected_cases']==names,'suite expected names changed')
        count+=len(names)
    require(index['preservation']==check_preservation(),'checkpoint preservation differs')
    native=r6.read_json(root/'native.json'); records={v['name']:v['detail'] for v in native['checks']}
    require({p.name for p in root.iterdir() if p.is_dir()}==set(NATIVE_CASES),'episode population differs')
    observations={}; canaries=[]
    for name in NATIVE_CASES:
        task,case,wanted=expected_native(name); p=root/name
        policy=r6.read_json(p/'search-policy.json')
        require(policy['task_id']==task.id and policy['case']==case,'episode identity differs from frozen case')
        current=auditor.audit(p,task)
        for k,v in wanted.items(): require(current[k]==v,'native acceptance differs')
        require(current['coverage']['recorded_not_recomputed']==0,'complete checkpoint needs original-tree coverage')
        same_record={'task_id':task.id,'case':case,'seal_sha256':r6.sha(p/'seal.json'),
            'process_log_sha256':r6.sha(root/(name+'.log')),'observations':current}
        require(events.canonical(records[name])==events.canonical(same_record),'native suite record differs from recomputation')
        seed=r6.read_json(p/'credential-canary.json')['nonce']; canaries.append(credential.derive(seed))
        observations[name]=current
    scans=[]
    if publication_scan:
        seed=r6.read_json(root/'d1_valid/credential-canary.json')['nonce']
        report=publication.scan([root],canaries[0],seed,extra_canaries=canaries[1:])
        require(not report['incompletely_scanned'] and not report['unreadable_directories'] and not report['irregular_entries'],'checkpoint publication inventory incomplete')
        for hit in report['disclosures']:
            require(hit['path']=='d1_reflected_canary/stages/proposal-1/output/provider-response.json','unexpected checkpoint disclosure')
        require(len(report['disclosures'])==2,'reflection disclosure population differs')
        scans={'bundle_files_scanned':report['files_scanned'],'expected_synthetic_disclosures':len(report['disclosures'])}
    return {'passed':True,'total_checks':count,'policy_sha256':r6.sha(contract.CONFIG),'source_lock_sha256':r6.sha(contract.LOCK),
        'preservation':check_preservation(),'event_count':sum(v['event_count'] for v in observations.values()),
        'sealed_entries':sum(v['sealed_files'] for v in observations.values()),'episodes':observations,
        'publication':scans,'live_model_calls':0,'live_model_cost_usd':0}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir',type=Path,required=True)
    parser.add_argument('--development-policy-dir',type=Path)
    parser.add_argument('--recount',action='store_true')
    parser.add_argument('--only',choices=('focused','native','audits'))
    args=parser.parse_args()
    if args.development_policy_dir: contract.development(args.development_policy_dir)
    root=args.run_dir.resolve()
    if args.recount:
        print(json.dumps(recount(root),indent=2)); return
    root.mkdir(parents=True,exist_ok=False)
    r6.write_json(root/'checkpoint.json',{'passed':False})
    for name,fn in [('focused',unit_suite),('native',native_suite),('audits',audit_suite)]:
        if args.only is None or args.only==name: fn(root)
    if args.only: return
    r6.write_json(root/'checkpoint.json',{'passed':True,'policy_sha256':r6.sha(contract.CONFIG),
        'source_lock_sha256':r6.sha(contract.LOCK),'live_model_calls':0,'preservation':check_preservation(),
        'suites':{file:{'sha256':r6.sha(root/file),'count':len(names)} for file,names in SUITES.items()}})
    r6.write_json(root/'final-checks.json',recount(root))
    print('R6-005 content checkpoint passed',sum(map(len,SUITES.values())))


if __name__=='__main__': main()

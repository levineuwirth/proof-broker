#!/usr/bin/env python3
"""R6-006 exact-name-gated units, native HTTPS episodes and audit mutations."""
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
import priced_audit as auditor
import priced_budget as live_budget
import pricing_gate as gate
import time
import argparse as argtypes
import priced_contract as contract
import priced_episode as harness
import live_audit as historical_live_audit
import priced_https as live_https
import priced_payload as wire
import payload
import provider_audit
import publication
import run as r6
import test_credentials as prior_tests
from test_proposals import Suite,require,rejected,assert_complete
from test_task_identity import rehash

UNIT_CASES="""sources_locked dated_model_fields cache_surcharge_zero_not_free nano_rounding_up
source_policy_admission fresh_capture_new_receipt wire_encoding_distinct missing_source_before_ledger stale_source_before_ledger forged_source_extract
source_bytes_changed semantic_source_changed model_alias_rejected exact_message_binding
missing_permit_before_connect forged_permit_before_connect wrong_amount_before_connect expired_permit
durable_attempt_limit campaign_attempt_limit monetary_limit input_limit unknown_usage_not_zero
tls_primitives_reused no_live_cli duplicate_json_rejected missing_case duplicate_case""".split()
NATIVE_CASES=['d1_'+c for c in harness.CASES]+['c8_valid','c8_invalid_witness']
AUDIT_MUTATIONS={
 'wrong_policy':'frozen policy binding','wrong_source_lock':'frozen policy binding',
 'wrong_host_admission':'host pricing admission differs','wrong_actor_admission':'actor pricing admission differs',
 'connection_before_price':'connection or credential read precedes pricing admission',
 'credential_before_price':'connection or credential read precedes pricing admission',
 'transport_after_rejection':'transport occurred after pricing rejection',
 'wrong_reservation':'reservation differs','wrong_ledger':'durable reservation differs',
 'wrong_mount':'HTTPS command permits','wrong_model_metadata':'provider metadata differs',
 'wrong_certificate':'assembled witness differs','wrong_type':'frozen type/axiom policy',
 'wrong_axiom':'frozen type/axiom policy','missing_declaration':'missing expected declaration',
 'wrong_proof_replayed':'verdict differs: proof_replayed','wrong_proposer':'verdict differs: witness_proposer',
 'wrong_reconstruction_context':'reconstruction context differs','missing_shared_checker':'artifact not retained',
 'wrong_pricing_source':'host pricing source differs',
 'wrong_origin_binding':'frozen policy binding','missing_origin_page':'artifact not retained',
}
HISTORICAL={'https_d1':'runs/https-checkpoint-v1/d1_valid','https_c8':'runs/https-checkpoint-v1/c8_valid',
 'credential_d1':'runs/credential-checkpoint-v3/d1_valid','provider_c8':'runs/provider-checkpoint-v1/c8_valid',
 'envelope_d1':'runs/envelope-checkpoint-v1/d1_valid','golden_c8':'runs/golden-c8-v1'}
AUDIT_CASES=['d1_retained_only','c8_retained_only','archived_capture_independent',*AUDIT_MUTATIONS,*HISTORICAL,'prior_files_preserved']
SUITES={'focused.json':UNIT_CASES,'native.json':NATIVE_CASES,'audits.json':AUDIT_CASES}
PRESERVATION=r6.ROOT/'reviews/2026-09-09/R6-006-PRESERVATION.json'
PRESERVATION_SHA='7203c7be2bc8f68c6472bb7cc6e810f758d8adf5adc7e078958b47ee9b60d6b9'


def check_preservation():
    require(r6.sha(PRESERVATION)==PRESERVATION_SHA,'preservation inventory differs from its pre-work anchor')
    inventory=r6.read_json(PRESERVATION)
    for name,h in inventory['files'].items():
        require(r6.sha(r6.ROOT.parents[1]/name)==h,'prior artifact changed: '+name)
    return {'checked_files':len(inventory['files']),'inventory_sha256':PRESERVATION_SHA,'git_base':inventory['git_base'],
        'scope':'pre-work Git-selected bytes, including closed uncommitted R6-004/005 and closeouts'}


def unit_suite(root):
    suite=Suite(root/'focused.json',UNIT_CASES)
    c=contract.config()
    prepared=r6.read_json(r6.ROOT/'runs/provider-checkpoint-v1/d1_valid/prepared.json')
    request=wire.request(r6.D1,prepared); args=wire.arguments(request)
    suite.case('sources_locked',lambda:contract.verify_sources() or {'policy_sha256':r6.sha(contract.CONFIG)})
    def dated():
        require(c['model']['requested_id']==gate.MODEL and c['model']['allowed_response_ids']==[gate.MODEL])
        require(c['model']['model_computation_attested'] is False and c['live_enabled'] is False)
        return {'requested_id':gate.MODEL,'inference_attested':False}
    suite.case('dated_model_fields',dated)
    def rate_basis():
        values=gate.source_evidence(contract.SOURCES); rates=gate.rates_from(values)
        require(rates=={'input':2500,'cached_input':250,'cache_write':2500,'output':15000})
        return {'additional_write_charge':0,'write_input_charge_nano_usd_per_token':rates['cache_write']}
    suite.case('cache_surcharge_zero_not_free',rate_basis)
    def rounding():
        rates=c['pricing']['nano_usd_per_token']
        require(gate.cost_micro(1,0,rates)==3 and gate.cost_micro(2,0,rates)==5)
        require(gate.cost_micro(16384,4096,rates)==102400)
        return {'one_input_token_micro_usd':3,'two_input_tokens_micro_usd':5,'reservation_micro_usd':102400}
    suite.case('nano_rounding_up',rounding)
    suite.case('source_policy_admission',lambda:gate.admission(c,contract.SOURCES,args,request,time.time()))
    def refreshed_receipt():
        from datetime import datetime,timezone
        with tempfile.TemporaryDirectory() as tmp:
            source=Path(tmp)/'sources';shutil.copytree(contract.SOURCES,source)
            before=contract.capture_identity(source)
            for path in source.glob('*.receipt.json'):
                value=gate.strict(path.read_bytes());stamp=datetime.now(timezone.utc).isoformat()
                value.update(started_at_utc=stamp,finished_at_utc=stamp)
                path.write_bytes(gate.canonical(value)+b'\n')
            require(contract.capture_identity(source)!=before)
            require(gate.admission(c,source,args,request,time.time())['accepted'] is True)
            return {'changed_capture_identity':True,'same_approved_content_admitted':True,
                    'scope':'synthetic receipt timestamps; not an actual refetch'}
    suite.case('fresh_capture_new_receipt',refreshed_receipt)
    def wire_encoding():
        require(any(ord(ch)>127 for message in args['input'] for ch in message['content']), 'encoding control lacks non-ASCII input')
        body=live_https.serialize(args,'valid')
        require(body==gate.entity_body(args) and body!=gate.canonical(args)+b'\n')
        admitted=gate.admission(c,contract.SOURCES,args,request,time.time())
        require(admitted['body_sha256']==gate.sha(body))
        return {'non_ascii_precondition':True,'body_binding_matches_frozen_encoder':True,
                'body_bytes':len(body),'canonical_utf8_bytes':len(gate.canonical(args)+b'\n')}
    suite.case('wire_encoding_distinct',wire_encoding)
    def sources(kind):
        with tempfile.TemporaryDirectory(prefix='r6-006-unit-') as tmp:
            directory=Path(tmp)/'sources';shutil.copytree(contract.SOURCES,directory)
            gate.admission(c,directory,args,request,time.time())
            path=Path(tmp)/'ledger'
            if kind=='missing': (directory/'model.html').unlink(); message='pricing_source_population'
            elif kind=='stale': harness.source_fault(directory,'stale_source'); message='pricing_capture_stale'
            elif kind=='extract':
                value=gate.strict((directory/'model.extract.json').read_bytes());value['output']='1.00'
                (directory/'model.extract.json').write_bytes(gate.canonical(value)+b'\n')
                value=gate.strict((directory/'model.receipt.json').read_bytes());value['extract_sha256']=r6.sha(directory/'model.extract.json')
                (directory/'model.receipt.json').write_bytes(gate.canonical(value)+b'\n');message='pricing_extract_binding'
            else:
                harness.source_fault(directory,'raw_source_changed' if kind=='raw' else 'semantic_source_changed')
                message='pricing_raw_drift_model' if kind=='raw' else 'pricing_semantic_drift_model'
            result=rejected(lambda:live_budget.reserve(path,'first',args,request,directory),message)
            require(not path.exists(),'rejected admission opened a ledger')
            return {**result,'unmutated_copy_passes':True,'ledger_created':False}
    for name,kind in [('missing_source_before_ledger','missing'),('stale_source_before_ledger','stale'),
        ('forged_source_extract','extract'),('source_bytes_changed','raw'),('semantic_source_changed','semantic')]:
        suite.case(name,lambda kind=kind:sources(kind))
    def changed_argument(kind):
        other=copy.deepcopy(args)
        if kind=='model':other['model']='gpt-5.4'; message='pricing_request_options'
        else:other['input'][1]['content']+=' ';message='pricing_request_body_binding'
        return rejected(lambda:gate.admission(c,contract.SOURCES,other,request,time.time()),message)
    suite.case('model_alias_rejected',lambda:changed_argument('model'))
    suite.case('exact_message_binding',lambda:changed_argument('body'))
    def before_connect(kind):
        with tempfile.TemporaryDirectory(prefix='r6-006-actor-') as tmp:
            directory=Path(tmp); out=directory/'out';out.mkdir()
            row=live_budget.reserve(directory/'ledger','unit',args,request,contract.SOURCES)
            gate.transport_admission(c,contract.SOURCES,args,request,row,(directory/'ledger').read_bytes(),'unit',time.time())
            permit=copy.deepcopy(row)
            if kind=='missing':permit=None;expected='pricing_permit_missing'
            elif kind=='forged':permit['pricing_admission']['body_sha256']='0'*64;expected='pricing_permit_binding'
            else:permit['reservation']['reserved_micro_usd']+=1;expected='pricing_reservation_amount'
            r6.write_json(directory/'permit',permit)
            (directory/'ledger').write_bytes(gate.canonical(permit if permit is not None else row)+b'\n')
            r6.write_json(directory/'args',args);(directory/'request').write_bytes(request)
            r6.write_json(directory/'fixture',{'status':200,'body':'{}'});(directory/'ca').write_text('never parsed as TLS')
            options=argtypes.Namespace(out=str(out),policy=str(contract.CONFIG),fixture=str(directory/'fixture'),
                arguments=str(directory/'args'),credential_file=str(directory/'absent-credential'),case='valid',ca=str(directory/'ca'),
                request=str(directory/'request'),sources=str(contract.SOURCES),permit=str(directory/'permit'),
                ledger=str(directory/'ledger'),episode='unit')
            with mock.patch.object(live_https,'connection',side_effect=AssertionError('connected before admission')) as connect,\
                 mock.patch.object(live_https,'read_credential',side_effect=AssertionError('read credential before admission')) as read_secret:
                live_https.execute(options)
                require(connect.call_count==0 and read_secret.call_count==0)
            observed=r6.read_json(out/'pricing-check.json')
            require(observed['accepted'] is False and observed['failure_code']==expected)
            return {'unmutated_permit_passes':True,'connection_calls':0,'credential_reads':0,'failure_code':expected}
    for name,kind in [('missing_permit_before_connect','missing'),('forged_permit_before_connect','forged'),('wrong_amount_before_connect','amount')]:
        suite.case(name,lambda kind=kind:before_connect(kind))
    def expired():
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'ledger'; row=live_budget.reserve(path,'unit',args,request,contract.SOURCES)
            return rejected(lambda:gate.transport_admission(c,contract.SOURCES,args,request,row,path.read_bytes(),'unit',
                row['pricing_admission']['evaluated_at_unix']+61),'pricing_permit_stale')
    suite.case('expired_permit',expired)
    def ledger(kind):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'ledger';live_budget.reserve(path,'first',args,request,contract.SOURCES)
            if kind=='campaign':live_budget.reserve(path,'second',args,request,contract.SOURCES)
            before=path.read_bytes()
            result=rejected(lambda:live_budget.reserve(path,'third' if kind=='campaign' else 'first',args,request,contract.SOURCES),
                            'campaign_request_budget' if kind=='campaign' else 'Request budget')
            require(path.read_bytes()==before)
            return {**result,'ledger_unchanged':True}
    suite.case('durable_attempt_limit',lambda:ledger('episode'))
    suite.case('campaign_attempt_limit',lambda:ledger('campaign'))
    suite.case('monetary_limit',lambda:rejected(lambda:wire.reservation(args,spent=c['limits']['total_micro_usd']),'Monetary'))
    def input_limit():
        other=copy.deepcopy(args);other['input'][0]['content']='x'*(c['limits']['message_utf8_bytes']+1)
        return rejected(lambda:wire.reservation(other),'byte admission')
    suite.case('input_limit',input_limit)
    def unknown():
        value=wire.previous.usage({});require(value['input_tokens'] is None and value['output_tokens'] is None)
        return value
    suite.case('unknown_usage_not_zero',unknown)
    def reused():
        import live_https as frozen
        require(live_https.handoff.__code__.co_code==frozen.handoff.__code__.co_code
                and live_https.connection.__code__.co_code==frozen.connection.__code__.co_code)
        return {'frozen_transport_sha256':r6.sha(r6.ROOT/'live_https.py')}
    suite.case('tls_primitives_reused',reused)
    def no_live():
        require(c['live_enabled'] is False and 'fixture_port=server.server_port' in (r6.ROOT/'priced_https.py').read_text())
        require('--share-net' not in (r6.ROOT/'priced_episode.py').read_text())
        return {'live_enabled':False,'real_calls':0}
    suite.case('no_live_cli',no_live)
    suite.case('duplicate_json_rejected',lambda:rejected(lambda:gate.strict(b'{"x":1,"x":2}'),'duplicate_json_key'))
    suite.case('missing_case',lambda:rejected(lambda:assert_complete(UNIT_CASES[:-1],UNIT_CASES),'missing/extra cases'))
    suite.case('duplicate_case',lambda:rejected(lambda:assert_complete(UNIT_CASES+[UNIT_CASES[0]],UNIT_CASES),'duplicate case'))
    suite.finish()


def expected_native(name):
    task=r6.C8 if name.startswith('c8_') else r6.D1; case=name[3:]
    categories={'untrusted_ca':'tls_certificate_verification','http503':'provider_http_error',
                'reflected_canary':'provider_http_error','invalid_witness':'certificate_verification'}
    price=case not in ('valid','invalid_witness','untrusted_ca','http503','reflected_canary')
    return task,case,{'accepted':case=='valid','proof_accepted':case=='valid',
        'credential_receipt_accepted':not price and case!='untrusted_ca','publication_accepted':case!='reflected_canary',
        'failure_category':'pricing_admission' if price else categories.get(case)}


def native_suite(root):
    suite=Suite(root/'native.json',NATIVE_CASES)
    for name in NATIVE_CASES:
        def one(name=name):
            task,case,wanted=expected_native(name); target=root/name; target.mkdir()
            log=root/(name+'.log')
            with log.open('x') as stream,redirect_stdout(stream),redirect_stderr(stream):
                print('R6-006 native',name,flush=True)
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
            with tempfile.TemporaryDirectory(prefix='r6-006-retained-') as tmp:
                target=Path(tmp)/'episode'; prior_tests.retained_copy(root/('d1_valid' if task==r6.D1 else 'c8_valid'),target)
                return auditor.audit(target,task)
        suite.case(name,check)
    def archived():
        with mock.patch.object(contract,'SOURCES',Path('/unavailable-original-pricing-capture')):
            require(auditor.audit(root/'d1_valid',r6.D1)['accepted'] is True)
        return {'external_source_unavailable':True,'episode_owned_capture_audits':True}
    suite.case('archived_capture_independent',archived)
    def change(root,name):
        if name in ('wrong_policy','wrong_source_lock'):
            edit(root/'search-policy.json',lambda v:v.update({('config_sha256' if name=='wrong_policy' else 'source_lock_sha256'):'0'*64}))
        elif name=='wrong_host_admission': edit(root/'host-pricing-admission.json',lambda v:v.update(reserved_micro_usd=1))
        elif name=='wrong_actor_admission': edit(root/'stages/proposal-1/output/pricing-check.json',lambda v:v['current'].update(reserved_micro_usd=1))
        elif name in ('connection_before_price','credential_before_price','transport_after_rejection'):
            def alter(v):
                if name=='connection_before_price': v['connection_started_at_ns']=v['pricing_admitted_at_ns']-1
                elif name=='credential_before_price': v['credential_read_at_ns']=v['pricing_admitted_at_ns']-1
                else: v['connection_attempts']=1
            edit(root/'stages/proposal-1/output/http.json',alter)
        elif name=='wrong_pricing_source':
            p=root/'pricing-sources/model.html'; p.write_bytes(p.read_bytes()+b' ')
        elif name=='wrong_origin_binding': edit(root/'search-policy.json',lambda v:v.update(pricing_origin_sha256='0'*64))
        elif name=='missing_origin_page': (root/'pricing-origin/model.html').unlink()
        elif name=='wrong_proof_replayed': edit(root/'verdict.json',lambda v:v.update(proof_replayed=False))
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
            with tempfile.TemporaryDirectory(prefix='r6-006-mutation-') as tmp:
                target=Path(tmp)/'episode'; original=root/('d1_missing_permit' if name=='transport_after_rejection' else 'd1_valid')
                prior_tests.retained_copy(original,target)
                require(auditor.audit(target,r6.D1)['accepted'] is (name!='transport_after_rejection'))
                ephemeral=r6.read_json(target/'seal.json')['ephemeral_sha256']
                change(target,name)
                prior_tests.recompute_publication(target,name!='transport_after_rejection',ephemeral)
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
            if name.startswith('https'): return historical_live_audit.audit(p,r6.C8 if name.endswith('c8') else r6.D1)
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
    parser.add_argument('--pricing-sources',type=Path,default=contract.SOURCES)
    parser.add_argument('--recount',action='store_true')
    parser.add_argument('--only',choices=('focused','native','audits'))
    args=parser.parse_args()
    contract.SOURCES=args.pricing_sources.resolve()
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
    print('R6-006 content checkpoint passed',sum(map(len,SUITES.values())))


if __name__=='__main__': main()

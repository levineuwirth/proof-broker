#!/usr/bin/env python3
"""Independent R6-008 review probes. Temporary state; synthetic credentials only."""
import argparse
import contextlib
import copy
import importlib.util
import io
import json
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import types
from pathlib import Path
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
import campaign_ledger as ledger
import campaign_contract as contract
import campaign_budget as budget
import campaign_episode as driver
import campaign_https as actor
import credential
import episode
import events
import pricing_gate_v2 as gate
import live_tls_fixture
import run as r6

def j(p): return json.loads(Path(p).read_bytes())
def w(p, v): Path(p).write_bytes(events.canonical(v)+b'\n')
def module(name):
    spec = importlib.util.spec_from_file_location('review_'+name, ROOT/'reviews/2026-09-13'/(name+'.py'))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

def authorization():
    return {'approved_by': 'synthetic review', 'approved_utc': '2026-09-13T00:00:00Z',
            'scope': 'synthetic test; no provider request', 'model_id': contract.MODEL,
            'maximum_transmissions': 1, 'maximum_micro_usd': contract.ATTEMPT_MICRO_USD,
            'maximum_presend_attempts': 3}

def simple_book(d):
    b = ledger.Ledger(d, 'a'*64); b.activate(authorization())
    p, raw = b.reserve('review', {'reserved_micro_usd': 102400},
                       {'request_sha256': 'b'*64, 'arguments_sha256': 'c'*64}, {})
    return b, p, raw

def termination():
    outcomes = {}
    for label, process in [('terminated', {'exit_code': 1, 'workload_empty_after_cleanup': True, 'monitor_error': None}),
                           ('workload_still_alive', {'exit_code': 1, 'workload_empty_after_cleanup': False, 'monitor_error': None}),
                           ('empty_record', {})]:
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp); b,p,_=simple_book(d/'ledger'); grant=d/'grant';grant.mkdir()
            result,_=b.reconcile(p,grant,process,{'body_sends_started':0,'header_sends_started':0},{})
            outcomes[label]={'kind':result['kind'],'transmissions_consumed':b.snapshot()[1]['transmissions_consumed']}
    assert outcomes['terminated']['kind']=='release'
    return outcomes

def concurrent_grant():
    with tempfile.TemporaryDirectory() as tmp:
        d=Path(tmp);b,p,_=simple_book(d/'ledger'); slot=d/'grant';slot.mkdir()
        final=slot/'send-grant.json'; temp=slot/'send-grant.json.tmp'
        barrier=threading.Barrier(2); first_done=threading.Event(); original_exists=Path.exists; original_open=ledger.os.open
        results={}
        def exists(path):
            result=original_exists(path)
            if path==final and threading.current_thread().name in ('first','second'):
                assert result is False; barrier.wait(timeout=10)
            return result
        def open_file(path,*args,**kwargs):
            if Path(path)==temp and threading.current_thread().name=='second':
                assert first_done.wait(10)
            return original_open(path,*args,**kwargs)
        def worker(name):
            try:
                g=ledger.grant_record(p,time.monotonic_ns());ledger.commit_grant(slot,g)
                results[name]={'accepted':True,'grant_id':g['grant_id']}
            except Exception as e:results[name]={'accepted':False,'error':repr(e)}
            finally:
                if name=='first':first_done.set()
        with patch.object(Path,'exists',exists),patch.object(ledger.os,'open',open_file):
            threads=[threading.Thread(target=worker,args=(name,),name=name) for name in ('first','second')]
            for t in threads:t.start()
            for t in threads:t.join(15)
            assert all(not t.is_alive() for t in threads)
        results['retained_grant_id']=j(final)['grant_id']
        return results

def authorization_substitution():
    with tempfile.TemporaryDirectory() as tmp:
        d=Path(tmp);c=copy.deepcopy(contract.config());c.update(live_enabled=True,live_model_calls_authorized=1,authorization=authorization())
        p=d/'policy.json';w(p,c);digest=r6.sha(p)
        prepared=j(ROOT/'campaign-runs/rehearsal-3/prepared.json');task=r6.get_task('verinf-d1-70')
        with patch.object(contract,'CONFIG',p):
            request=budget.request(task,prepared);arguments=budget.arguments(request)
        (d/'request.json').write_bytes(request);w(d/'arguments.json',arguments)
        admitted=gate.admission(c,contract.SOURCES,arguments,request,time.time())
        # A rehearsal activation for these exact policy bytes, not the approved live scope.
        b=ledger.Ledger(d/'rehearsal',digest);b.activate(contract.REHEARSAL_AUTHORIZATION)
        permit,raw=b.reserve('probe',budget.reservation(arguments),
            {'request_sha256':gate.sha(request),'arguments_sha256':gate.sha(gate.canonical(arguments))},admitted)
        w(d/'permit.json',permit);(d/'ledger.ndjson').write_bytes(raw)
        out=d/'out';out.mkdir(); grant=d/'grant';grant.mkdir()
        ca,_=contract.bundle()
        args=types.SimpleNamespace(mode='live',policy=str(p),arguments=str(d/'arguments.json'),ca=str(ca),out=str(out),
            permit=str(d/'permit.json'),ledger=str(d/'ledger.ndjson'),request=str(d/'request.json'),sources=str(contract.SOURCES),
            episode='probe',grant=str(grant),commitment_nonce='review',credential_file='/synthetic-not-read',fixture_port=None)
        reached=[]
        def stop_before_read(path):
            reached.append(path);raise ValueError('credential_format')
        def no_connection(*a,**kw):raise AssertionError('connection must not be reached')
        with patch.object(actor,'read_credential',stop_before_read),patch.object(actor,'connection',no_connection):
            actor.execute(args)
        h=j(out/'http.json')
        assert h['connection_attempts']==0
        return {'live_authorization_transmissions':c['authorization']['maximum_transmissions'],
            'ledger_activation_transmissions':ledger.parse(raw)[0]['maximum_transmissions'],
            'ledger_activation_approver':ledger.parse(raw)[0]['authorization']['approved_by'],
            'authorization_checked':h['authorization_present_in_policy'],'permit_verified':h['permit_verified_at_ns'] is not None,
            'pricing_admitted':j(out/'pricing-check.json')['accepted'],'credential_boundary_reached':bool(reached),
            'credential_reads':0,'connections':0,'failure_category':h['failure_category']}

def stale_permit(loopback):
    with tempfile.TemporaryDirectory() as tmp:
        d=Path(tmp);task=r6.get_task('verinf-d1-70');c=contract.config()
        request=budget.request(task,j(ROOT/'campaign-runs/rehearsal-3/prepared.json'));arguments=budget.arguments(request)
        admitted=gate.admission(c,contract.SOURCES,arguments,request,time.time())
        b=ledger.Ledger(d/'ledger',contract.policy_sha256());b.activate(authorization())
        permit,raw=b.reserve('same-episode',budget.reservation(arguments),
            {'request_sha256':gate.sha(request),'arguments_sha256':gate.sha(gate.canonical(arguments))},admitted)
        (d/'request.json').write_bytes(request);w(d/'arguments.json',arguments);w(d/'permit.json',permit);(d/'snapshot.ndjson').write_bytes(raw)
        results=[]
        if not loopback:
            slot=d/'first';slot.mkdir();ledger.commit_grant(slot,ledger.grant_record(permit,1))
            b.reconcile(permit,slot,{'exit_code':0,'workload_empty_after_cleanup':True},{'send_outcome':'returned'},{})
            v=ledger.verify_permit(permit,raw,contract.policy_sha256(),'same-episode')
            return {'shared_consumed':b.snapshot()[1]['transmissions_consumed'],'stale_snapshot_accepted':True,
                    'snapshot_consumed':v['transmissions_consumed']}
        for index in (1,2):
            root=d/str(index);root.mkdir();out=root/'out';out.mkdir();grant=root/'grant';grant.mkdir()
            nonce=credential.nonce();canary=credential.derive(nonce)
            (root/'credential').write_text(credential.header(canary)+'\n')
            w(root/'fixture.json',driver.canned(task,request))
            with live_tls_fixture.materialize(root,'valid') as (ca,cert,key):
                args=[sys.executable,'-I','-S','-B',str(ROOT/'campaign_https.py'),'--mode','rehearsal',
                    '--policy',str(contract.CONFIG),'--arguments',str(d/'arguments.json'),'--credential-file',str(root/'credential'),
                    '--out',str(out),'--sources',str(contract.SOURCES),'--permit',str(d/'permit.json'),'--ledger',str(d/'snapshot.ndjson'),
                    '--request',str(d/'request.json'),'--episode','same-episode','--grant',str(grant),'--commitment-nonce',nonce,
                    '--ca',str(ca),'--fixture',str(root/'fixture.json'),'--server-cert',str(cert),'--server-key',str(key)]
                proc=subprocess.run(args,capture_output=True,text=True,timeout=30)
            assert proc.returncode==0,proc.stderr[-600:]
            http=j(out/'http.json');server=j(out/'server.json')
            assert http['http_status']==200 and http['body_sends_started']==1 and len(server['requests'])==1
            results.append({'instance':index,'http_status':http['http_status'],'body_sends_started':http['body_sends_started'],
                'receiver_requests':len(server['requests']),'grant_id':http['grant_id']})
            if index==1:b.reconcile(permit,grant,{'exit_code':0,'workload_empty_after_cleanup':True},http,{})
        return {'maximum_transmissions':1,'shared_ledger_consumed':b.snapshot()[1]['transmissions_consumed'],
            'same_permit':True,'total_receiver_requests':sum(x['receiver_requests'] for x in results),'instances':results}

def interrupted_record():
    with tempfile.TemporaryDirectory() as tmp:
        d=Path(tmp);run=d/'run';run.mkdir(); task=r6.get_task('verinf-d1-70')
        b=ledger.Ledger(d/'ledgers/rehearsal',contract.policy_sha256());b.activate(contract.REHEARSAL_AUTHORIZATION)
        expected=r6.frozen_task(task)[1]
        tools={'expected':expected,'runtime':{'stdlib':'/review','extension_binaries':[]},'runtime_path':d,'python':Path(sys.executable)}
        def prepare(run,task,tools):
            request=budget.request(task,j(ROOT/'campaign-runs/rehearsal-3/prepared.json'))
            (run/'live-request.json').write_bytes(request);w(run/'live-arguments.json',budget.arguments(request));return request
        def stopped(run,name,binary,argv,mounts,grant,**kwargs):
            out=run/'stages/proposal-1/output';out.mkdir(parents=True);grant.mkdir()
            p=j(run/'campaign-permit.json');ledger.commit_grant(grant,ledger.grant_record(p,time.monotonic_ns()))
            w(out.parent/'proposal-1.process.json',{'exit_code':137,'workload_empty_after_cleanup':True,'monitor_error':None})
            (out/'http.json').write_bytes(b'{')
            raise episode.StageFailure('proposal-1','resource_exhaustion','synthetic termination during record write')
        proxy=types.SimpleNamespace(path=ROOT/'ledgers/rehearsal'/(contract.policy_sha256()+'.ndjson'),reserve=b.reserve,reconcile=b.reconcile,snapshot=b.snapshot)
        with patch.object(contract,'campaign_ledger',lambda live:proxy),patch.object(driver,'setup',lambda *a:tools), \
             patch.object(driver,'prepare',prepare),patch.object(driver.network,'stage',stopped):
            try:driver.execute(run,task,'rehearsal',d,None)
            except Exception as e:error={'type':type(e).__name__,'message':str(e)}
            else:error=None
        rows=events.read(run/'events.ndjson') if (run/'events.ndjson').exists() else []
        return {'exception':error,'seal_exists':(run/'seal.json').exists(),
            'terminal_events':[r['event'] for r in rows if r['event'] in events.TERMINAL_EVENTS],
            'reservation_open':bool(b.snapshot()[1]['open_reservations']),
            'grant_exists':(run/'stages/proposal-1/grant/send-grant.json').exists(),'connections':0}

def audit_mutations():
    ctl=module('campaign_audit_controls');audit=ctl.audit;out={}
    for name in ('source_lock_rebound','publication_scan_rejected','disclosure_overridden_by_terminal','false_terminal_summary_digest'):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);root=d/'campaign-runs';books=d/'ledgers'
            shutil.copytree(ROOT/'campaign-runs',root);shutil.copytree(ROOT/'ledgers',books)
            assert ctl.run_audit(root,books)['accepted']
            run=root/'rehearsal-3'
            if name=='source_lock_rebound':
                def change(run,rows):
                    ph=run/'provenance/campaign-harness';p=ph/'campaign_ledger.py';p.write_bytes(p.read_bytes()+b'\n# altered source without changing policy\n')
                    lock=ph/'policies/campaign-harness-v1.sha256.json';v=j(lock);v['campaign_ledger.py']=r6.sha(p);w(lock,v)
                    sp=j(run/'search-policy.json');sp['source_lock_sha256']=r6.sha(lock);w(run/'search-policy.json',sp)
                    rows[0]['payload']['policy_sha256']=r6.sha(run/'search-policy.json')
                ctl.refinalize(run,change)
            elif name=='disclosure_overridden_by_terminal':
                def change(run,rows):
                    nonce=j(run/'credential-canary.json')['nonce']
                    (run/'synthetic-disclosure.txt').write_text(credential.header(credential.derive(nonce)))
                ctl.refinalize(run,change)
                scan=j(run/'publication-scan.json');assert scan['accepted'] is False and len(scan['disclosures'])>0
                rows=events.read(run/'events.ndjson');assert rows[-1]['event']=='episode_rejected'
                rows[-1]['event']='episode_finished';rows[-1]['payload'].update(accepted=True,publication_accepted=True)
                ctl.rechain(run,rows);driver.publication_driver.seal(run,True)
            else:
                # Mutate one reported relationship, maintaining chain and seal consistency.
                rows=events.read(run/'events.ndjson')
                if name=='publication_scan_rejected':
                    p=run/'publication-scan.json';v=j(p);assert v['accepted'] is True;v['accepted']=False;w(p,v)
                    rows[-1]['payload']['publication_scan_sha256']=r6.sha(p)
                else:rows[-1]['payload']['summary_sha256']='0'*64
                ctl.rechain(run,rows);driver.publication_driver.seal(run,True)
            out[name]=ctl.run_audit(root,books)
    return out

def operator_coverage():
    op=module('operator_disclosure_scan')
    with tempfile.TemporaryDirectory() as tmp:
        d=Path(tmp);empty=d/'empty';empty.mkdir();run=d/'unscanned-run';out=run/'stages/proposal-1/output';out.mkdir(parents=True)
        header='Bearer '+credential.derive(credential.nonce());nonce='synthetic-review'
        w(out/'http.json',{'credential_commitment_sha256':actor.commitment(nonce,header),'commitment_nonce':nonce})
        # A real disclosure in the bound run, deliberately outside the requested scan roots.
        (run/'disclosure.txt').write_text(header)
        report=d/'report.json'
        original_load=op.load
        def load(name):
            return types.SimpleNamespace(read_credential=lambda ignored:header) if name=='live_https' else original_load(name)
        args=['operator_disclosure_scan.py','--credential-file','/synthetic-not-read','--report',str(report),
              '--root',str(empty),'--bind-runs',str(run)]
        with patch.object(op,'load',load),patch.object(sys,'argv',args):
            try:op.main()
            except SystemExit as e:code=e.code
        v=j(report)
        return {'exit_code':code,'scan_accepted':v['accepted'],'files_scanned':v['files_scanned'],
            'commitment_bound':v['operator_scan']['run_receipts'][0]['commitment_bound'],
            'seal_sha256':v['operator_scan']['run_receipts'][0]['seal_sha256'],
            'bound_run_inside_scan_roots':False,'synthetic_disclosure_outside_scan':True,'real_credentials_read':0}

def operator_single_relationships():
    op=module('operator_disclosure_scan');results={}
    for name in ('unscanned_run','missing_seal','sealed_http_changed'):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);run=d/'run';out=run/'stages/proposal-1/output';out.mkdir(parents=True);empty=d/'empty';empty.mkdir()
            header='Bearer '+credential.derive(credential.nonce());nonce='synthetic-review'
            w(out/'http.json',{'credential_commitment_sha256':actor.commitment(nonce,header),'commitment_nonce':nonce})
            events.append(run,'episode','episode_started',{},task_id='verinf-d1-70')
            events.append(run,'episode','episode_rejected',{},task_id='verinf-d1-70')
            driver.publication_driver.seal(run,False)
            original_load=op.load
            def load(name):
                return types.SimpleNamespace(read_credential=lambda ignored:header) if name=='live_https' else original_load(name)
            def call(scan_root,report):
                args=['operator_disclosure_scan.py','--credential-file','/synthetic-not-read','--report',str(report),
                      '--root',str(scan_root),'--bind-runs',str(run)]
                with patch.object(op,'load',load),patch.object(sys,'argv',args),contextlib.redirect_stdout(io.StringIO()):
                    try:op.main()
                    except SystemExit as e:code=e.code
                v=j(report)
                return {'exit_code':code,'scan_accepted':v['accepted'],'files_scanned':v['files_scanned'],
                        'commitment_bound':v['operator_scan']['run_receipts'][0]['commitment_bound'],
                        'seal_sha256':v['operator_scan']['run_receipts'][0]['seal_sha256']}
            before=call(run,d/'before.json');assert before['exit_code']==0 and before['commitment_bound']
            scan_root=run
            if name=='unscanned_run':scan_root=empty
            elif name=='missing_seal':(run/'seal.json').unlink()
            else:
                value=j(out/'http.json');value['extra']='changed after sealing';w(out/'http.json',value)
            results[name]={'unmutated':before,'mutated':call(scan_root,d/'after.json')}
    return results

def main():
    p=argparse.ArgumentParser();p.add_argument('--loopback-replay',action='store_true');p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    assert not args.output.exists()
    if args.loopback_replay:results={'loopback_permit_replay':stale_permit(True)}
    else:
        results={'termination':termination(),'concurrent_grant':concurrent_grant(),
            'authorization_substitution':authorization_substitution(),'stale_permit':stale_permit(False),
            'interrupted_record':interrupted_record(),'audit_mutations':audit_mutations(),
            'operator_coverage':operator_coverage(),'operator_single_relationships':operator_single_relationships()}
    results.update(provider_calls=0,real_credentials_read=0,program_sha256=r6.sha(Path(__file__)),
        reviewed_policy_sha256=contract.policy_sha256(),reviewed_source_lock_sha256=r6.sha(contract.LOCK))
    args.output.write_text(json.dumps(results,indent=1)+'\n');print(json.dumps(results,indent=1))

if __name__=='__main__':main()

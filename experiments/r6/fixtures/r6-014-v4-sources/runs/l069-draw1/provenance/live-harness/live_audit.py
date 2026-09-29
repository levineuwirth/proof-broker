"""Independent retained-artifact checks for R6-005; no execution attestation."""
from pathlib import Path
import hashlib
import ssl
import subprocess

import credential
import credential_audit as scanner_audit
import credential_contract
import envelope_proof_audit
import episode
import events
import live_contract as contract
import live_episode as harness
import live_https
import live_payload as wire
import provider_audit
import provider_payload
import publication
import run as r6
from supervise import resource_violations

STAGES = ('preparation-build','preparation','pipeline-prepare','proposal-1','assembly','certificate-check',
          'capture-build','reconstruct','export','validation-local','validation-whole')


def require(ok, message):
    if not ok: raise ValueError('HTTPS audit: '+message)


def same(a,b,message): require(events.canonical(a)==events.canonical(b),message)


def check_command(spec,runtime,roles,case):
    prefix = ['bwrap','--unshare-all','--die-with-parent','--new-session','--cap-drop','ALL',
        '--clearenv','--setenv','PATH','/no-programs','--setenv','LEAN_ABORT_ON_PANIC','1',
        '--symlink','usr/lib','/lib','--symlink','usr/lib64','/lib64',
        '--proc','/proc','--dev','/dev','--tmpfs','/tmp','--dir','/work','--chdir','/work']
    for lib in runtime['libraries']: prefix += ['--ro-bind',lib['host'],lib['guest']]
    original = Path(spec['run'])
    require(original.is_absolute() and spec['records']==str(original/'stages/proposal-1'),'stage path binding')
    argv=spec['argv']; tail=argv[len(prefix):]
    guests={tail[i+2]:tail[i+1] for i,v in enumerate(tail[:-2]) if v=='--ro-bind'}
    ephemeral={guest:guests.get(guest) for guest in ('/credential','/ca.pem','/server.pem','/server.key')}
    require(all(p and Path(p).is_absolute() and not Path(p).is_relative_to(original)
                and not Path(p).exists() for p in ephemeral.values()),'private mount survived or entered artifact tree')
    actor = roles['actor_source'].replace('/provider_http.py','/live_https.py')
    mounts=[(roles['runtime_path'],runtime['stdlib']),(actor,'/adapter.py'),
        (str(contract.CONFIG),'/policy.json'),(str(original/'live-arguments.json'),'/arguments.json'),
        (str(original/'canned-provider.json'),'/fixture.json'),*[(ephemeral[g],g) for g in ephemeral]]
    for host,guest in mounts: prefix += ['--ro-bind',host,guest]
    prefix += ['--ro-bind',runtime['python'],'/runner/bin/program','--bind',str(original/'stages/proposal-1/output'),'/out',
        '/runner/bin/program','-I','-S','-B','/adapter.py','--policy','/policy.json','--arguments','/arguments.json',
        '--fixture','/fixture.json','--credential-file','/credential','--ca','/ca.pem','--server-cert','/server.pem',
        '--server-key','/server.key','--case',case,'--out','/out']
    same(argv,prefix,'HTTPS command permits an extra input, capability or endpoint')
    require(spec['capture_events'] is False,'transport observation channel changed')
    for key in ('wall_seconds','cpu_seconds','memory_bytes','output_bytes'):
        require(spec[key]==contract.config()['limits']['request_'+key],'HTTPS resource limit changed')


def check_https(path,read,task,case,request):
    root='stages/proposal-1/output/'
    http,server=read(root+'http.json'),read(root+'server.json')
    pki=read('tls-fixture/provenance.json')
    same(http['endpoint'],contract.config()['endpoint'],'endpoint identity')
    require(http['transport_scope']=='isolated_loopback_https_fixture','transport scope')
    require(type(http['fixture_tcp_port']) is int and 0<http['fixture_tcp_port']<65536,'fixture port')
    require(http['connection_attempts']==1 and type(http['connection_attempts']) is int
            and http['retries']==0 and http['redirects_followed']==0,'extra transport attempt')
    require(type(http['elapsed_ns']) is int and http['elapsed_ns']>0,'elapsed time missing')
    same(server['server_names'],['api.openai.com'],'SNI identity differs')
    require(http['maximum_response_bytes']==contract.config()['limits']['maximum_response_bytes'],'response byte budget')
    ca=path('tls-fixture/'+('other-ca.pem' if case=='untrusted_ca' else 'ca.pem'))
    require(http['ca_bundle_sha256']==r6.sha(ca)==pki['trust_root_sha256'],'trust root binding')
    leaf_hash=hashlib.sha256(ssl.PEM_cert_to_DER_cert(path('tls-fixture/server.pem').read_text())).hexdigest()
    require(leaf_hash==pki['leaf_der_sha256'],'certificate provenance differs')
    cert_check=subprocess.run(['openssl','verify','-CAfile',str(ca),'-verify_hostname','api.openai.com',
        '-attime',str(http['verification_time_unix']),str(path('tls-fixture/server.pem'))],capture_output=True)
    broken = case in ('untrusted_ca','wrong_hostname','expired_certificate')
    require((cert_check.returncode!=0)==broken,'retained certificate validity differs from TLS control')
    serialized=path(root+'serialized-body.json').read_bytes()
    require(serialized==live_https.serialize(wire.arguments(request),case),'serialized request differs from declared case')
    require(http['request_sha256']==wire.sha(serialized) and http['request_bytes']==len(serialized),'HTTP request binding')
    files={'http.json','server.json','serialized-body.json'}
    if broken:
        require(http['failure_category']=='tls_certificate_verification' and http['tls'] is None
            and type(http['tls_verify_code']) is int,'wrong TLS rejection boundary')
        require(all(http[k]==0 and type(http[k]) is int for k in ('header_sends_started','header_sends_returned','body_sends_started','body_sends_returned')),'credential or body sent before TLS acceptance')
        require(server['requests']==[] and http['response_sha256'] is None
            and http['tls_verified_at_ns'] is None and http['header_send_at_ns'] is None,'HTTP observed after failed TLS')
    else:
        tls=http['tls']
        require(tls['verified'] is True and tls['peer_certificate_sha256']==leaf_hash
            and tls['server_hostname']=='api.openai.com' and tls['version'] in ('TLSv1.2','TLSv1.3')
            and tls['alpn']=='http/1.1','TLS observation binding')
        require(type(http['tls_verified_at_ns']) is int and http['tls_verified_at_ns']<http['header_send_at_ns'],'headers precede TLS validation')
        require(all(http[k]==1 and type(http[k]) is int for k in ('header_sends_started','header_sends_returned','body_sends_started','body_sends_returned')),'send accounting differs')
        require(len(server['requests'])==1,'HTTP receipt count')
        sent=path(root+'outbound-body.json').read_bytes(); received=path(root+'received-body.json').read_bytes()
        require(sent==received==serialized and http['outbound_body_sha256']==wire.sha(sent),'captured send/receive body differs')
        seen=server['requests'][0]
        expected={ 'method':'POST','path':'/v1/responses','host':'api.openai.com','content_type':'application/json',
            'declared_bytes':len(received),'observed_bytes':len(received),'body_sha256':wire.sha(received),
            'authorization_present':seen['authorization_present'],'authorization_sha256':seen['authorization_sha256']}
        same(seen,expected,'receiver body receipt differs')
        raw=path(root+'provider-response.json').read_bytes()
        require(http['response_sha256']==wire.sha(raw) and http['response_bytes']==len(raw),'response body binding')
        fixture=read('canned-provider.json')
        if case=='reflected_canary':
            canary=credential.derive(read('credential-canary.json')['nonce'])
            require(credential.header(canary).encode() in raw and http['http_status']==500,'reflection precondition absent')
        else: require(raw==fixture['body'].encode() and http['http_status']==fixture['status'],'canned response changed')
        same(http['response_headers'],{'Content-Type':'application/json','Content-Length':str(len(raw)),
            'x-request-id':'r6-local-canned-https'} if case!='truncated_response' else
            {'Content-Type':'application/json','Content-Length':str(len(raw)+1),'x-request-id':'r6-local-canned-https'},'response header allowlist')
        require(http['failure_category']==('transport_incomplete_response' if case=='truncated_response' else None),'HTTP failure boundary differs')
        files |= {'outbound-body.json','received-body.json','provider-response.json'}
    require({p.name for p in path(root+'http.json').parent.iterdir()}==files,'unexpected HTTP output artifact')
    same(read('canned-provider.json'),harness.canned(task,request,case),'fixture response binding')
    return http,server


def audit(run,task):
    contract.verify_sources()
    run=Path(run); seal=r6.read_json(run/'seal.json')
    require(seal['schema_version']=='r6-credential-seal-1','seal schema')
    def path(name):
        p=run/name
        require(name in seal['retained_sha256'] and p.resolve().is_relative_to(run.resolve()),'artifact not retained: '+name)
        require(r6.sha(p)==seal['retained_sha256'][name],'sealed artifact changed: '+name)
        return p
    def read(name): return r6.read_json(path(name))
    for name in seal['retained_sha256']: path(name)
    rows=episode.observations(run)
    require(rows and len(rows)==seal['event_count'] and rows[-1]['event_hash']==seal['last_event_hash'],'receipt seal')
    require(all(r['task_id']==task.id for r in rows),'task identity differs')
    def receipt(stage,event):
        hits=[r['payload'] for r in rows if r['source']=='supervisor' and r['stage']==stage and r['event']==event]
        require(len(hits)==1,'expected one receipt: '+stage+'/'+event)
        return hits[0]
    policy=read('search-policy.json'); case=policy['case']; c=contract.config()
    require(case in harness.CASES,'unknown canned case')
    same(policy,{'name':contract.NAME,'task_id':task.id,'case':case,'config_sha256':r6.sha(contract.CONFIG),
        'source_lock_sha256':r6.sha(contract.LOCK),'manifest_sha256':r6.sha(task.path/'manifest.json')},'frozen policy binding')
    _,expected=r6.frozen_task(task)
    nonce=read('credential-canary.json')['nonce']; canary=credential.derive(nonce)
    same(read('credential-canary.json'),credential.record(nonce),'canary derivation')
    same(receipt('episode','episode_started'),{'policy_sha256':r6.sha(path('search-policy.json')),
        'challenge_sha256':expected['challenge_sha256'],'nonce':nonce},'admission receipt')
    binaries,roles,runtime=provider_audit.check_provenance(path,read)
    for section,module in [('credential-harness',credential_contract),('live-harness',contract)]:
        for name,h in module.source_lock().items():
            require(r6.sha(path('provenance/'+section+'/'+name))==h,'retained source differs: '+name)
        for source in (module.CONFIG,module.LOCK):
            require(r6.sha(path('provenance/'+section+'/'+str(source.relative_to(r6.ROOT))))==r6.sha(source),'retained policy differs')
    summary=read('credential-summary.json')
    scan,final,state=scanner_audit.check_disclosure(run,seal,path,read,canary,nonce,summary)
    context=read('stages/preparation/output/context.json')
    same(context,r6.read_json(task.path/'context/local-context.json'),'preparation context differs')
    provider_payload.old.context(context,read('sanitized-context.json'))
    prepared=read('prepared.json'); reified=read('stages/preparation/output/reification.json')
    same(prepared,read('stages/pipeline-prepare/output/prepared.json'),'prepared pipeline output differs')
    same(prepared['input_ir'],reified['ir'],'prepared reification differs')
    same(read('input-ir.json'),reified['ir'],'input IR differs')
    original=provider_payload.request(task,prepared)
    require(path('request.json').read_bytes()==original,'preparation request differs')
    require(path('request.sha256').read_text()==wire.sha(original)+'  request.json\n','preparation request hash differs')
    require(path('prompt.txt').read_bytes()==contract.PROMPT.read_bytes(),'prompt differs')
    same(read('client-arguments.json'),provider_payload.arguments(original),'preparation arguments differ')
    same(read('messages.json'),provider_payload.arguments(original)['input'],'preparation messages differ')
    old_audit={'request_sha256':wire.sha(original),'prompt_sha256':r6.sha(contract.PROMPT),
        'sanitized_context_sha256':r6.sha(path('sanitized-context.json')),'context_projection_is_model_visible':False,
        'source_context_sha256':r6.sha(task.path/'context/local-context.json'),
        'let_facts_preserved':[r['name'] for r in context['telescope'] if r['kind']=='let'],
        'reifier_omissions':reified['skipped_locals'],'farkas_omissions':prepared['farkas_omissions']}
    same(read('payload-audit.json'),old_audit,'preparation payload audit')
    same(receipt('payload','payload_validated'),{'payload_audit_sha256':r6.sha(path('payload-audit.json')),
        'request_sha256':wire.sha(original),'prompt_sha256':r6.sha(contract.PROMPT),
        'client_arguments_sha256':r6.sha(path('client-arguments.json')),'messages_sha256':r6.sha(path('messages.json'))},'preparation payload receipt')
    request=wire.request(task,prepared); args=wire.arguments(request)
    require(path('live-request.json').read_bytes()==request,'live request differs')
    same(read('live-arguments.json'),args,'live arguments differ')
    same(read('live-messages.json'),args['input'],'live messages differ')
    binding={'request_sha256':wire.sha(request),'policy_sha256':r6.sha(contract.CONFIG),'prompt_sha256':r6.sha(contract.PROMPT),
        'arguments_sha256':r6.sha(path('live-arguments.json')),'messages_sha256':r6.sha(path('live-messages.json')),
        'prepared_sha256':r6.sha(path('prepared.json')),'preparation_request_sha256':r6.sha(path('request.json'))}
    same(read('live-payload.json'),binding,'live payload record'); same(receipt('live-payload','payload_validated'),binding,'live payload receipt')
    reservation={**wire.reservation(args),'request_sha256':wire.sha(request),'arguments_sha256':r6.sha(path('live-arguments.json')),
                 'policy_sha256':r6.sha(contract.CONFIG)}
    same(read('reservation.json'),reservation,'reservation differs'); same(receipt('proposal','request_reserved'),reservation,'reservation receipt differs')
    ledger=path('reservation-ledger.ndjson').read_bytes().splitlines()
    require(len(ledger)==1,'reservation ledger population')
    original_root=Path(read('stages/proposal-1/command.json')['run'])
    same(provider_payload.legacy.strict_json(ledger[0]),{'sequence':0,'previous_hash':'0'*64,
        'policy_sha256':r6.sha(contract.CONFIG),'episode_id':original_root.name,'request_sha256':wire.sha(request),
        'arguments_sha256':events.digest(args),'reservation':wire.reservation(args)},'durable reservation differs')
    same(receipt('proposal','recovery_started'),{'route':contract.NAME,'proposer':'canned_provider_response'},'route attribution')
    http,server=check_https(path,read,task,case,request)
    check_command(read('stages/proposal-1/command.json'),runtime,roles,case)
    same(receipt('proposal','https_observed'),{'http_sha256':r6.sha(path('stages/proposal-1/output/http.json')),
        'server_sha256':r6.sha(path('stages/proposal-1/output/server.json'))},'HTTPS observation receipt')
    response,text,metadata,transport,error=wire.interpret(run/'stages/proposal-1/output',request)
    same(read('transport-validation.json'),transport,'transport report differs')
    same(receipt('proposal','transport_validated'),transport,'transport receipt differs')
    same(read('provider-metadata.json'),metadata,'provider metadata differs')
    if text is not None: require(path('response.json').read_bytes()==text,'response text differs')
    seen=server['requests'][0] if server['requests'] else {}
    observed=seen.get('authorization_sha256'); exact=observed==credential.commitment(canary)
    expected_credential=(None if case in ('missing_credential','untrusted_ca','wrong_hostname','expired_certificate') else
        hashlib.sha256(b'Bearer deliberately-wrong-canned-credential').hexdigest() if case=='wrong_credential' else credential.commitment(canary))
    require(observed==expected_credential,'canned credential precondition differs')
    receipt_record={'schema_version':'r6-credential-receipt-1','channel':'private_read_only_file','declared_case':case,
        'transmissions':len(server['requests']),'authorization_present':seen.get('authorization_present',False),
        'expected_authorization_sha256':credential.commitment(canary),'observed_authorization_sha256':observed,
        'exact_receipt':exact,'evidence_scope':read('credential-receipt.json')['evidence_scope']}
    same(read('credential-receipt.json'),receipt_record,'credential receipt differs')
    same(receipt('credential-receipt','credential_receipt_checked'),receipt_record,'credential receipt event')
    if error is None and not exact: error=wire.Failure('credential_receipt_failure','credential_receipt','Endpoint did not receive the expected credential')
    accounting=read('accounting.json')
    usage=provider_payload.usage({}); status='unreported'
    if http['response_sha256']:
        try: usage=provider_payload.usage(provider_payload.legacy.strict_json(path('stages/proposal-1/output/provider-response.json').read_bytes())); status=usage['status']
        except (ValueError,AttributeError): status='invalid'
    rate=c['pricing']['reservation_micro_usd_per_token']
    estimate=None if usage['input_tokens'] is None or usage['output_tokens'] is None else usage['input_tokens']*rate['input']+usage['output_tokens']*rate['output']
    same(accounting,{'attempts_reserved':1,'reservation':reservation,'connection_attempts':http['connection_attempts'],
        'headers_started':http['header_sends_started'],'bodies_started':http['body_sends_started'],
        'bodies_returned':http['body_sends_returned'],'endpoint_receipts':len(server['requests']),
        'usage':usage,'usage_status':status,'priced_usage_ceiling_micro_usd':estimate,'reservation_released':False,
        'live_model_calls':0,'live_model_cost_usd':0,
        'scope':'independent simulated episode reservation; synthetic usage or unknown, no billing observation'},'accounting differs')
    proof_ok=False
    if error is None:
        same(response,read('validated-response.json'),'validated proposal changed')
        packet=read('evidence.json'); cert=packet['certificate']; report=read('certificate-verdict.json')
        same(packet,read('stages/assembly/output/evidence.json'),'assembly output changed')
        same({k:packet[k] for k in ('input_ir','final_ir','trace')},{k:prepared[k] for k in ('input_ir','final_ir','trace')},'assembled problem differs')
        same(cert['payload']['witness_data'],response['witness'],'assembled witness differs')
        same(cert['backend'],{'name':'r6_fixture_witness','version':'1','config_hash':'sha256:'+r6.sha(contract.consumer.CONFIG)},'consumer certificate policy chain')
        require(type(cert['tier']) is int and cert['tier']==1 and cert['format']=='farkas','evidence tier')
        same(receipt('assembly','certificate_assembled'),{'certificate_sha256':events.digest(cert),
            'witness_proposer':'canned_provider_response','certificate_assembler':'sdk_proposal_assembler_v1',
            'response_sha256':r6.sha(path('validated-response.json'))},'assembler attribution')
        same(report,receipt('certificate-check','independent_certificate_verdict'),'certificate verifier receipt')
        require(report['certificate_hash']=='sha256:'+events.digest(cert),'certificate hash binding')
        same(receipt('proposal','recovery_finished'),{'route':contract.consumer.NAME,'ok':report['accepted'],
            'witness':response['witness'],'reason':report['reason'],'proposer':'canned_provider_response'},'consumer route attribution')
        if report['accepted'] is False:
            require(report['stage']=='certificate_verification' and report['reason']['kind']=='farkas_not_contradictory','wrong witness rejection boundary')
            error=wire.Failure('certificate_verification','certificate_verification','Farkas witness was not verified')
        else:
            require(report['accepted'] is True and report['reason']=={'kind':'verified_farkas'},'certificate verdict')
            same(read('stages/reconstruct/output/context.json'),context,'reconstruction context differs from frozen obligation')
            verdict=read('verdict.json')
            require(set(verdict)=={'schema_version','task_id','search_policy','manifest_sha256','challenge_sha256','request_sha256',
                'solution_sha256','final_validation','axiom_delta','certificate_validation','witness_proposer','certificate_assembler',
                'certificate_verified','certificate_consumed','derivation_replayed','residual_closer','trust_tier',
                'local_obligation_closed','whole_declaration_validated'} and verdict['schema_version']=='r6-https-proof-1','proof verdict shape')
            require(verdict['task_id']==task.id and verdict['manifest_sha256']==r6.sha(task.path/'manifest.json')
                and verdict['challenge_sha256']==expected['challenge_sha256'] and verdict['request_sha256']==wire.sha(request),'verdict challenge binding')
            for k,v in {'witness_proposer':'canned_provider_response','certificate_assembler':'sdk_proposal_assembler_v1',
                'certificate_verified':True,'certificate_consumed':True,'derivation_replayed':False,
                'residual_closer':'omega','trust_tier':1,'local_obligation_closed':True,'whole_declaration_validated':True,
                'certificate_validation':report,'search_policy':contract.NAME}.items(): same(verdict[k],v,'verdict differs: '+k)
            envelope_proof_audit.audit(task,packet,verdict,rows,path,read,receipt)
            same(receipt('episode','proof_validated'),{'verdict_sha256':r6.sha(path('verdict.json')),
                'proof_accepted':True,'solution_sha256':verdict['solution_sha256']},'proof verdict receipt')
            proof_ok=True
    if not proof_ok:
        require('verdict.json' not in seal['retained_sha256'],'rejected episode has proof verdict')
        require(not any(r['source']=='child_report' for r in rows),'rejected episode reports hidden reconstruction or search')
    stage=('certificate-check' if error and error.category=='certificate_verification' else
           'proposal-1' if error and error.phase=='https_transport' else error.phase if error else None)
    same(summary,{'schema_version':'r6-https-summary-1','task_id':task.id,'case':case,'search_policy':contract.NAME,
        'proof_accepted':proof_ok,'credential_receipt_accepted':exact,'failure_category':error.category if error else None,
        'failure_phase':error.phase if error else None,'failure_stage':stage,'error':str(error) if error else None,
        'scope':c['scope']},'summary differs from recomputed boundaries')
    coverage=scanner_audit.check_scan_provenance(run,seal,scan,final,path,state)
    accepted=bool(proof_ok and exact and scan['accepted'] and final['report_clean'])
    terminal={'accepted':accepted,'proof_accepted':proof_ok,'credential_receipt_accepted':exact,
        'publication_accepted':bool(scan['accepted'] and final['report_clean']),
        'summary_sha256':r6.sha(path('credential-summary.json')),'publication_scan_sha256':r6.sha(path('publication-scan.json')),
        'publication_final_sha256':r6.sha(path('publication-final.json'))}
    same(rows[-1]['payload'],terminal,'terminal predicates differ')
    require(seal['accepted'] is accepted,'seal verdict differs')
    check_stages(rows,path,read,receipt,proof_ok,accepted,error)
    return {**terminal,'failure_category':summary['failure_category'],'coverage':coverage,
        'event_count':len(rows),'sealed_files':len(seal['retained_sha256']),'disclosures':len(scan['disclosures']),
        'scope':'artifact consistency and observed local TLS/credential/proof boundaries; no execution or inference attestation'}


def check_stages(rows,path,read,receipt,proof_ok,accepted,error):
    stages=list(STAGES if proof_ok else STAGES[:6] if error and error.category=='certificate_verification' else STAGES[:4])
    order=[('episode','episode_started')]
    for stage in stages:
        if stage=='proposal-1': order += [('payload','payload_validated'),('live-payload','payload_validated'),
            ('proposal','recovery_started'),('proposal','request_reserved')]
        order += [(stage,'stage_started'),(stage,'stage_finished')]
        if stage=='proposal-1': order += [('proposal','https_observed'),('proposal','transport_validated'),('credential-receipt','credential_receipt_checked')]
        if stage=='assembly': order += [('assembly','certificate_assembled')]
        if stage=='certificate-check': order += [('certificate-check','independent_certificate_verdict'),('proposal','recovery_finished')]
        if stage=='reconstruct': order += [('reconstruct','context_validated')]
        if stage.startswith('validation-'): order += [(stage,'kernel_verdict')]
        spec=read(f'stages/{stage}/command.json'); stats=read(f'stages/{stage}/{stage}.process.json')
        same(receipt(stage,'stage_finished'),stats,'stage receipt differs')
        bad_cert=bool(stage=='certificate-check' and not proof_ok)
        require((stats['exit_code']!=0)==bad_cert and stats['resource_exhausted'] is None
            and stats.get('monitor_error') is None and stats.get('observation_error') is None
            and stats['workload_empty_after_cleanup'] is True,'unhealthy stage')
        require(not resource_violations(spec,stats.get('execution_wall_seconds',stats['wall_seconds']),
            stats['cgroup_cpu_usec'],stats['memory_events'],stats['output_bytes']),'stage exceeded budget')
        begun=receipt(stage,'stage_started')
        require(begun['command_file']==f'stages/{stage}/command.json' and spec['stage']==stage,'stage command receipt')
        for field,key in [('wall_limit_seconds','wall_seconds'),('cpu_limit_seconds','cpu_seconds'),('memory_limit_bytes','memory_bytes')]:
            require(begun[field]==spec[key],'stage limit receipt')
    if proof_ok: order += [('episode','proof_validated')]
    order += [('episode','episode_finished' if accepted else 'episode_rejected')]
    same([(r['stage'],r['event']) for r in rows if r['source']=='supervisor'],order,'extra, missing or reordered supervisor receipts')
    require(set(p.name for p in path('stages/proposal-1/command.json').parents[1].iterdir())==set(stages),'stage inventory differs')

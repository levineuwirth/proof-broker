"""R6-005: new HTTPS proposal path, unchanged frozen proof consumer."""
import argparse
from pathlib import Path
import shutil

import admission
import credential
import credential_contract
import credential_episode as publication_driver
import episode
import events
import priced_contract as contract
import priced_budget as live_budget
import pricing_gate as gate
import time
import json
from datetime import datetime,timezone
import priced_payload as wire
import live_tls_fixture
import payload
import provider_episode as consumer
import provider_payload
import live_episode as prior
import run as r6

CASES = ('valid','invalid_witness','missing_permit','forged_admission','wrong_reservation','changed_request',
         'raw_source_changed','semantic_source_changed','stale_source','future_source','host_stale_source',
         'wrong_request_model','http503','untrusted_ca','reflected_canary')


def canned(task, request, case):
    fixture = consumer.canned_provider(task, request, case)
    if fixture['status'] == 200:
        obj = payload.strict_json(fixture['body'])
        obj['model'] = 'wrong-canned-model' if case == 'wrong_model' else contract.config()['model']['requested_id']
        obj['service_tier'] = 'priority' if case == 'wrong_service_tier' else 'default'
        if case in ('output_budget','input_budget'):
            field = 'output_tokens' if case == 'output_budget' else 'input_tokens'
            limit = 'output_tokens' if case == 'output_budget' else 'input_tokens_reserved'
            obj['usage'][field] = contract.config()['limits'][limit]+1
            obj['usage']['total_tokens'] = obj['usage']['input_tokens']+obj['usage']['output_tokens']
        fixture['body'] = (events.canonical(obj)+b'\n').decode()
    return fixture


def setup(run, task, packages):
    contract.verify_sources()
    tools = prior.setup(run, task, packages)
    for section, module in [('priced-harness', contract)]:
        for source in [r6.ROOT/p for p in module.FILES]+[module.CONFIG,module.LOCK]:
            dst = run/'provenance'/section/source.relative_to(r6.ROOT)
            dst.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(source,dst)
    return tools


def prepare(run, task, tools):
    prepared = consumer.prepare(run, task, tools)
    # Keep its request/receipt untouched as preparation-component evidence.
    # Only the separately named live input is ever mounted in the HTTPS actor.
    request = wire.request(task, prepared)
    (run/'live-request.json').write_bytes(request)
    args = wire.arguments(request)
    r6.write_json(run/'live-arguments.json', args)
    r6.write_json(run/'live-messages.json', args['input'])
    record = {'request_sha256':wire.sha(request), 'policy_sha256':r6.sha(contract.CONFIG),
        'prompt_sha256':r6.sha(contract.PROMPT), 'arguments_sha256':r6.sha(run/'live-arguments.json'),
        'messages_sha256':r6.sha(run/'live-messages.json'), 'prepared_sha256':r6.sha(run/'prepared.json'),
        'preparation_request_sha256':r6.sha(run/'request.json')}
    r6.write_json(run/'live-payload.json',record)
    events.append(run, 'live-payload', 'payload_validated',record)
    return request


def shift_capture(directory, offset):
    for path in directory.glob('*.receipt.json'):
        value=gate.strict(path.read_bytes())
        for key in ('started_at_utc','finished_at_utc'):
            stamp=datetime.fromisoformat(value[key]).timestamp()+offset
            value[key]=datetime.fromtimestamp(stamp,timezone.utc).isoformat()
        path.write_bytes(gate.canonical(value)+b'\n')


def source_fault(directory,case):
    if case in ('stale_source','host_stale_source'): shift_capture(directory,-172800)
    elif case=='future_source': shift_capture(directory,172800)
    elif case in ('raw_source_changed','semantic_source_changed'):
        path=directory/'model.html'; raw=path.read_bytes()
        if case=='raw_source_changed': raw+=b'\n<!-- R6-006 raw-byte control -->\n'
        else:
            gate.require(raw.count(b'10% uplift')==1,'semantic_source_control_precondition')
            raw=raw.replace(b'10% uplift',b'11% uplift')
        path.write_bytes(raw)
        derived=gate.extract(raw,'model')
        (directory/'model.extract.json').write_bytes(gate.canonical(derived)+b'\n')
        receipt=gate.strict((directory/'model.receipt.json').read_bytes())
        receipt.update(raw_sha256=gate.sha(raw),raw_bytes=len(raw),extract_sha256=gate.sha((directory/'model.extract.json').read_bytes()))
        receipt['transfer']['download_bytes']=len(raw)
        (directory/'model.receipt.json').write_bytes(gate.canonical(receipt)+b'\n')


def actor_inputs(run,case,row):
    shutil.copytree(run/'pricing-sources',run/'transport-pricing-sources')
    source_fault(run/'transport-pricing-sources',case)
    args=r6.read_json(run/'live-arguments.json')
    request=(run/'live-request.json').read_bytes()
    if case=='wrong_request_model': args['model']='gpt-5.4'
    if case=='changed_request': request+=b' '
    r6.write_json(run/'transport-arguments.json',args)
    (run/'transport-request.json').write_bytes(request)
    permit=json.loads(json.dumps(row))
    if case=='forged_admission': permit['pricing_admission']['body_sha256']='0'*64
    if case=='wrong_reservation': permit['reservation']['reserved_micro_usd']+=1
    r6.write_json(run/'pricing-permit.json',None if case=='missing_permit' else permit)
    (run/'transport-ledger.ndjson').write_bytes(gate.canonical(permit)+b'\n')


def invoke(run, tools, case, nonce):
    c=contract.config(); runtime=tools['runtime']; limits=c['limits']
    request=(run/'live-request.json').read_bytes()
    shutil.copytree(run/'pricing-origin',run/'pricing-sources')
    if case=='host_stale_source': source_fault(run/'pricing-sources',case)
    try:
        row=live_budget.reserve(run/'reservation-ledger.ndjson',run.name,
                               r6.read_json(run/'live-arguments.json'),request,run/'pricing-sources')
    except (gate.Failure,wire.Failure) as failure:
        code=failure.code if isinstance(failure,gate.Failure) else failure.category
        denied={'accepted':False,'failure_code':code,'evaluated_at_unix':time.time()}
        r6.write_json(run/'host-pricing-admission.json',denied)
        events.append(run,'pricing-admission','pricing_rejected',denied)
        receipt=publication_driver.receipt(run,{'requests':[]},credential.derive(nonce),case)
        accounting={'attempts_reserved':0,'reservation':None,'connection_attempts':0,'headers_started':0,
            'bodies_started':0,'bodies_returned':0,'endpoint_receipts':0,'usage':provider_payload.usage({}),
            'usage_status':'unreported','priced_usage_ceiling_micro_usd':None,'reservation_released':False,
            'live_model_calls':0,'live_model_cost_usd':0,'scope':'host pricing rejection before ledger or transport'}
        r6.write_json(run/'accounting.json',accounting)
        return None,wire.Failure('pricing_admission','pricing_admission','Pricing admission: '+code),receipt,accounting
    admission_record=row['pricing_admission']
    r6.write_json(run/'host-pricing-admission.json',admission_record)
    events.append(run,'pricing-admission','pricing_admitted',{'admission_sha256':r6.sha(run/'host-pricing-admission.json')})
    reservation={**row['reservation'],'request_sha256':wire.sha(request),
        'arguments_sha256':r6.sha(run/'live-arguments.json'),'policy_sha256':r6.sha(contract.CONFIG),
        'pricing_admission_sha256':r6.sha(run/'host-pricing-admission.json')}
    r6.write_json(run/'reservation.json',reservation)
    events.append(run,'proposal','request_reserved',reservation)
    actor_inputs(run,case,row)
    with credential.delivery(nonce) as (canary,secret),live_tls_fixture.materialize(run,case) as (ca,cert,key):
        mounts=[(tools['runtime_path'],runtime['stdlib']),(r6.ROOT/'priced_https.py','/adapter.py'),
            (r6.ROOT/'live_https.py','/live_https.py'),(r6.ROOT/'pricing_gate.py','/pricing_gate.py'),
            (contract.CONFIG,'/policy.json'),(run/'transport-arguments.json','/arguments.json'),
            (run/'canned-provider.json','/fixture.json'),(secret,'/credential'),(ca,'/ca.pem'),(cert,'/server.pem'),(key,'/server.key'),
            (run/'transport-request.json','/request.json'),(run/'transport-pricing-sources','/pricing-sources'),
            (run/'pricing-permit.json','/permit.json'),(run/'transport-ledger.ndjson','/ledger.ndjson')]
        argv=['-I','-S','-B','/adapter.py','--policy','/policy.json','--arguments','/arguments.json',
            '--fixture','/fixture.json','--credential-file','/credential','--ca','/ca.pem','--server-cert','/server.pem',
            '--server-key','/server.key','--case',case,'--out','/out','--request','/request.json',
            '--sources','/pricing-sources','--permit','/permit.json','--ledger','/ledger.ndjson','--episode',run.name]
        out=episode.stage(run,'proposal-1',tools['python'],argv,mounts,
            extra_binaries=[Path(p) for p in runtime['extension_binaries']],wall=limits['request_wall_seconds'],
            cpu=limits['request_cpu_seconds'],memory=limits['request_memory_bytes'],output_limit=limits['request_output_bytes'])
    http,server=r6.read_json(out/'http.json'),r6.read_json(out/'server.json')
    events.append(run,'proposal','https_observed',{'http_sha256':r6.sha(out/'http.json'),'server_sha256':r6.sha(out/'server.json'),
        'pricing_check_sha256':r6.sha(out/'pricing-check.json')})
    proposed,text,metadata,validation,error=wire.interpret(out,request)
    r6.write_json(run/'transport-validation.json',validation); r6.write_json(run/'provider-metadata.json',metadata)
    if text is not None: (run/'response.json').write_bytes(text)
    events.append(run,'proposal','transport_validated',validation)
    receipt=publication_driver.receipt(run,server,canary,case)
    if error is None and not receipt['exact_receipt']:
        error=wire.Failure('credential_receipt_failure','credential_receipt','Endpoint did not receive the expected credential')
    raw=(out/'provider-response.json').read_bytes() if (out/'provider-response.json').exists() else None
    usage=provider_payload.usage({}); status='unreported'
    if raw is not None:
        try: usage=provider_payload.usage(payload.strict_json(raw)); status=usage['status']
        except (ValueError,AttributeError): status='invalid'
    estimate=None if usage['input_tokens'] is None or usage['output_tokens'] is None else gate.cost_micro(usage['input_tokens'],usage['output_tokens'],c['pricing']['nano_usd_per_token'])
    accounting={'attempts_reserved':1,'reservation':reservation,'connection_attempts':http['connection_attempts'],
        'headers_started':http['header_sends_started'],'bodies_started':http['body_sends_started'],
        'bodies_returned':http['body_sends_returned'],'endpoint_receipts':len(server['requests']),
        'usage':usage,'usage_status':status,'priced_usage_ceiling_micro_usd':estimate,'reservation_released':False,
        'live_model_calls':0,'live_model_cost_usd':0,
        'scope':'independent simulated episode reservation; synthetic usage or unknown, no billing observation'}
    r6.write_json(run/'accounting.json',accounting)
    return proposed,error,receipt,accounting

def execute(run, task, case, packages):
    if case not in CASES: raise ValueError('Unknown canned case')
    if task.id not in admission.verify()['controls']: raise ValueError('Task outside frozen controls')
    tools = setup(run,task,packages)
    config = contract.config(); nonce = credential.nonce()
    # Enrollment owns its immutable input copy. A later external refresh must
    # never change the reference used to audit this episode.
    shutil.copytree(contract.SOURCES,run/'pricing-origin')
    r6.write_json(run/'credential-canary.json',credential.record(nonce))
    policy = {'name':contract.NAME,'task_id':task.id,'case':case,'config_sha256':r6.sha(contract.CONFIG),
              'source_lock_sha256':r6.sha(contract.LOCK),'manifest_sha256':r6.sha(task.path/'manifest.json'),
              'pricing_origin_sha256':contract.capture_identity(run/'pricing-origin')}
    r6.write_json(run/'search-policy.json',policy)
    events.append(run,'episode','episode_started',{'policy_sha256':r6.sha(run/'search-policy.json'),
        'challenge_sha256':tools['expected']['challenge_sha256'],'nonce':nonce},task_id=task.id)
    request = prepare(run,task,tools)
    r6.write_json(run/'canned-provider.json',canned(task,request,case))
    events.append(run,'proposal','recovery_started',{'route':contract.NAME,'proposer':'canned_provider_response'})
    response,error,receipt,accounting = invoke(run,tools,case,nonce)
    verdict = None
    if error is None:
        try:
            packet,report,reports,delta,solution_hash = consumer.consume(run,task,tools,response)
            verdict = {'schema_version':'r6-priced-https-proof-1','task_id':task.id,'search_policy':contract.NAME,
                'manifest_sha256':r6.sha(task.path/'manifest.json'),'challenge_sha256':tools['expected']['challenge_sha256'],
                'request_sha256':wire.sha(request),'solution_sha256':solution_hash,'final_validation':reports,
                'axiom_delta':delta,'certificate_validation':report,
                'witness_proposer':'canned_provider_response','certificate_assembler':'sdk_proposal_assembler_v1',
                'certificate_verified':True,'certificate_consumed':True,'derivation_replayed':False,
                'residual_closer':'omega','proof_replayed':True,'trust_tier':1,'local_obligation_closed':True,'whole_declaration_validated':True}
            r6.write_json(run/'verdict.json',verdict)
            events.append(run,'episode','proof_validated',{'verdict_sha256':r6.sha(run/'verdict.json'),
                'proof_accepted':True,'solution_sha256':solution_hash})
        except provider_payload.Failure as failure:
            error = wire.Failure(failure.category,'certificate_verification',str(failure))
    summary = {'schema_version':'r6-priced-https-summary-1','task_id':task.id,'case':case,'search_policy':contract.NAME,
        'proof_accepted':verdict is not None,'credential_receipt_accepted':receipt['exact_receipt'],
        'failure_category':error.category if error else None,'failure_phase':error.phase if error else None,
        'failure_stage':('certificate-check' if error and error.category=='certificate_verification' else
                         'proposal-1' if error and (run/'stages/proposal-1').exists() and error.phase in ('https_transport','pricing_admission') else error.phase if error else None),
        'error':str(error) if error else None,'scope':config['scope']}
    r6.write_json(run/'credential-summary.json',summary)
    accepted,scan,final = publication_driver.finalize(run,credential.derive(nonce),nonce,summary)
    return {'accepted':accepted,'proof_accepted':verdict is not None,'failure_category':summary['failure_category'],
            'credential_receipt_accepted':receipt['exact_receipt'],'publication_accepted':scan['accepted'] and final['report_clean']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--task',choices=('verinf-d1-70','c1-c8-2p18'),required=True)
    parser.add_argument('--case',choices=CASES,default='valid')
    parser.add_argument('--run-dir',type=Path,required=True)
    parser.add_argument('--pricing-sources',type=Path,default=contract.SOURCES)
    args = parser.parse_args()
    contract.SOURCES=args.pricing_sources.resolve()
    run = args.run_dir.resolve(); run.mkdir(parents=True,exist_ok=False)
    print(execute(run,r6.get_task(args.task),args.case,r6.ROOT.parents[1]/'lean-bridge/.lake/packages'))

#!/usr/bin/env python3
"""R6-003 exact-name-gated component, native HTTP and retained-audit controls."""
import argparse
import copy
import gzip
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest import mock

import admission
import envelope_audit
import envelope_proof_audit
import episode
import events
import instrument
import payload as legacy
import provider_audit as auditor
import provider_contract as contract
import provider_episode as harness
import provider_http
import provider_payload as wire
import proposal_instrument as overlay
import run as r6
from test_proposals import Suite, assert_complete, rejected, require, retained_copy
from test_task_identity import rehash

UNIT_CASES = '''prompt_le_eq_only compiled_strict_integer_once decisive_tightening_witness injected_lt_before_request real_mislabeled_lia_before_request
prompt_request_binding alternate_encoding_equal_messages
system_component missing_system_component empty_system_component prefix_component suffix_component multiple_components
missing_user_components role_layout options_component duplicate_envelope malformed_envelope
correct_echo_ignored_body wrong_echo_neutral malformed_witness invalid_witness_well_formed
reasoning_before_message split_text_reassembly refusal incomplete unrequested_tool missing_message reported_model_mismatch
unknown_usage partial_usage reported_zero bad_usage_details inconsistent_usage excessive_output
no_external_endpoint no_hidden_retry budget_before_second_stage reserved_observations_unknown killed_after_transmission missing_http_observations
production_lt_admission_order production_real_admission_order shared_checker_binding source_lock_guard
missing_case_rejected duplicate_case_rejected'''.split()
NATIVE_CASES = ['d1_valid', 'c8_valid', 'd1_alternate_encoding', 'd1_invalid_witness', 'c8_invalid_witness',
    'd1_altered_prompt', 'd1_omitted_prompt', 'd1_altered_prefix', 'd1_altered_body', 'd1_wrong_echo', 'd1_malformed',
    'd1_http429', 'd1_http503', 'd1_redirect', 'd1_timeout', 'd1_connection_error', 'd1_disconnect',
    'd1_refusal', 'd1_incomplete', 'd1_tool_call', 'd1_malformed_provider', 'd1_oversized_response', 'd1_exhausted_budget']
AUDIT_CASES = '''d1_retained_only c8_retained_only alternate_retained_only
wrong_prompt_file wrong_client_arguments capture_only_mutation unreported_second_capture hidden_retry false_http_status invented_usage_zero
wrong_output_extraction wrong_provider_metadata missing_http_receipt wrong_request_mount unsafe_network_flag wrong_runtime
wrong_new_source wrong_shared_checker_source false_attestation hidden_fallback late_failure_marker
shared_checker_certificate shared_checker_proof shared_checker_type shared_checker_axiom
false_component_resealed false_missing_component_presence current_source_independence
legacy_broker_v1 legacy_broker_v2 legacy_broker_v3 legacy_c8_v1 legacy_d1_fixture legacy_c8_fixture
legacy_d1_envelope legacy_c8_envelope legacy_alternate_envelope prior_artifacts_preserved'''.split()


def failure(fn, category, stage=None):
    try: fn()
    except wire.Failure as error:
        require(error.category == category, f'wrong rejection {error.category}: {error}')
        if stage: require(error.stage == stage, 'wrong stage')
        return {'category': error.category, 'stage': error.stage, 'phase': error.phase, 'evidence': error.evidence, 'error': str(error)}
    raise AssertionError('Corruption was accepted')


def units(root):
    suite = Suite(root/'provider-units.json', UNIT_CASES)
    prepared = r6.read_json(r6.ROOT/'runs/envelope-checkpoint-v1/d1_valid/prepared.json')
    request = wire.request(r6.D1, prepared); args = wire.arguments(request)
    fixture = harness.canned_provider(r6.D1, request, 'valid')
    raw, meta = wire.provider_response(fixture['body'].encode(), 200)
    def prompt():
        require('"lt"' not in contract.PROMPT.read_text())
        schema = r6.read_json(r6.ROOT/'schema/provider-request.schema.json')
        require(schema['properties']['problem']['properties']['rows']['items']['properties']['relation']['enum'] == ['le','eq'])
        require(set(r['relation'] for r in prepared['rows']) == {'le','eq'})
        return {'prompt_sha256': r6.sha(contract.PROMPT), 'admitted_relations': ['le','eq']}
    suite.case('prompt_le_eq_only', prompt)
    def strict():
        rows = {r['name']: r for r in prepared['rows']}
        source = next(r for r in prepared['final_ir']['context']['hypotheses'] if r['name'] == 'hx')['shell']
        require(source['symbol'] == 'LT.lt' and source['args'][1]['value'] == '16777216')
        require(rows['hx'] == {'name':'hx','relation':'le','constant':'-16777215','terms':[{'variable':'_pb_atom_0','coefficient':'1'}]})
        require(next(r for r in legacy.strict_json(request)['problem']['rows'] if r['name'] == 'hx') == rows['hx'])
        return {'compiled_source': 'x.val < 16777216', 'compiled_row': rows['hx'], 'tightening_count': 1,
                'provenance': 'retained R6-002 compiler output; fresh D1 native run checks the same row'}
    suite.case('compiled_strict_integer_once', strict)
    def decisive():
        coefficients=wire.response(raw,request)['witness']['coefficients']
        by_name={r['name']:r for r in prepared['rows']}
        total=0; variables={}
        for item in coefficients:
            row=by_name[item['hypothesis']]; k=int(item['coefficient']); total+=k*int(row['constant'])
            for term in row['terms']: variables[term['variable']]=variables.get(term['variable'],0)+k*int(term['coefficient'])
        neg_goal=by_name['neg_goal']
        require(neg_goal['constant']==str(18446744069414584321-16777216+1))
        require(all(v==0 for v in variables.values()) and total==4)
        neg_weight=next(int(x['coefficient']) for x in coefficients if x['hypothesis']=='neg_goal')
        require(neg_weight==4 and total-neg_weight==0)
        return {'variables_canceled':True,'constant':total,'without_integer_tightening':total-neg_weight,
                'criterion':'constant > 0; zero is not contradictory','witness':coefficients}
    suite.case('decisive_tightening_witness',decisive)
    for name, change in [('injected_lt_before_request', lambda p: p['rows'][0].update(relation='lt')),
                         ('real_mislabeled_lia_before_request', lambda p: p['final_ir']['context']['free_vars'][0].update(type='Real'))]:
        def rejected_before(change=change):
            altered = copy.deepcopy(prepared); change(altered); require(altered != prepared)
            with mock.patch.object(legacy, 'request') as builder:
                result = failure(lambda: wire.request(r6.D1, altered), 'unsupported_theory', 'provider-admission')
                require(not builder.called)
            return {**result, 'requests_constructed': 0, 'transmissions': 0}
        suite.case(name, rejected_before)
    def binding():
        require(args['input'][0]['content'].encode() == contract.PROMPT.read_bytes())
        require(args['input'][1]['content'].encode() == (wire.PREFIX+wire.sha(request)+wire.SEPARATOR).encode()+request)
        require(wire.sha(request).encode() not in request)
        return {'request_sha256':wire.sha(request), 'prompt_sha256':r6.sha(contract.PROMPT)}
    suite.case('prompt_request_binding', binding)
    def encoding():
        a, b = [provider_http.serialize(args,c) for c in ['valid','alternate_encoding']]
        require(a != b and legacy.strict_json(a) == legacy.strict_json(b) == args)
        require(wire.envelope_report(a, request)['accepted'] and wire.envelope_report(b, request)['accepted'])
    suite.case('alternate_encoding_equal_messages', encoding)
    def diagnose(actual, components):
        encoded = events.canonical(actual)+b'\n'; require(legacy.strict_json(encoded) != args)
        report = wire.envelope_report(encoded, request)
        require(not report['accepted'] and [v['component'] for v in report['mismatches']] == components)
        return report
    for name, case, components in [('system_component','altered_prompt',['system_message']),
        ('missing_system_component','omitted_prompt',['message_layout','system_message']),
        ('prefix_component','altered_prefix',['user_prefix']), ('suffix_component','altered_body',['request_suffix'])]:
        suite.case(name, lambda c=case, wanted=components: diagnose(legacy.strict_json(provider_http.serialize(args,c)),wanted))
    def empty():
        actual=copy.deepcopy(args); actual['input'][0]['content']=''
        result=diagnose(actual,['system_message']); value=result['mismatches'][0]['observed']
        require(value['present'] and value['bytes']==0 and value['sha256']==wire.sha(b''))
        missing=wire.envelope_report(provider_http.serialize(args,'omitted_prompt'),request)['mismatches'][-1]['observed']
        require(missing=={'present':False,'type':None,'bytes':None,'sha256':None})
        return {'empty':value,'absent':missing}
    suite.case('empty_system_component',empty)
    a=copy.deepcopy(args); a['input'][0]['content']='changed'; a['input'][1]['content']='missing separator'
    suite.case('multiple_components',lambda:diagnose(a,['system_message','user_prefix','request_suffix']))
    no_user=copy.deepcopy(args); no_user['input'].pop()
    suite.case('missing_user_components',lambda:diagnose(no_user,['message_layout','user_prefix','request_suffix']))
    role=copy.deepcopy(args); role['input'][0]['role']='developer'
    suite.case('role_layout',lambda:diagnose(role,['message_layout','system_message']))
    options=copy.deepcopy(args); options['store']=True
    suite.case('options_component',lambda:diagnose(options,['request_options']))
    for name, body in [('duplicate_envelope',b'{"input":[],"input":[]}'),('malformed_envelope',b'{')]:
        suite.case(name,lambda body=body: failure(lambda:wire.check_envelope(body,request),'outbound_envelope_binding'))
    def ignored():
        altered=provider_http.serialize(args,'altered_body')
        require(wire.old.echo(raw,request)['accepted'] and wire.response(raw,request))
        result=wire.envelope_report(altered,request)
        require(not result['accepted'] and result['mismatches'][0]['component']=='request_suffix')
        return {'echo':True,'response_format':True,'envelope':False,'arithmetic_verification':'unobserved here'}
    suite.case('correct_echo_ignored_body',ignored)
    for name, case, category in [('wrong_echo_neutral','wrong_echo','transport_binding_failure'),('malformed_witness','malformed','response_decode')]:
        suite.case(name,lambda case=case,category=category: failure(lambda:wire.response(wire.provider_response(harness.canned_provider(r6.D1,request,case)['body'].encode(),200)[0],request),category))
    suite.case('invalid_witness_well_formed',lambda:wire.response(wire.provider_response(harness.canned_provider(r6.D1,request,'invalid_witness')['body'].encode(),200)[0],request))
    suite.case('reasoning_before_message',lambda:require(meta['reasoning_items']==1))
    suite.case('split_text_reassembly',lambda:require(meta['output_text_parts']==2 and wire.response(raw,request)['request_sha256']==wire.sha(request)))
    for name, case, category in [('refusal','refusal','provider_refusal'),('incomplete','incomplete','provider_incomplete'),('unrequested_tool','tool_call','provider_output_shape')]:
        suite.case(name,lambda case=case,category=category:failure(lambda:wire.provider_response(harness.canned_provider(r6.D1,request,case)['body'].encode(),200),category))
    for name, field, value, category in [('missing_message','output',[],'provider_output_shape'),('reported_model_mismatch','model','crossed-model','provider_model_binding')]:
        def changed(field=field,value=value,category=category):
            obj=legacy.strict_json(fixture['body'].encode()); obj[field]=value
            return failure(lambda:wire.provider_response(events.canonical(obj),200),category)
        suite.case(name,changed)
    suite.case('unknown_usage',lambda:require(wire.usage({})['total_tokens'] is None))
    suite.case('partial_usage',lambda:require(wire.usage({'usage':{'input_tokens':2}})['total_tokens'] is None))
    suite.case('reported_zero',lambda:require(wire.usage({'usage':{'total_tokens':0}})['total_tokens']==0))
    suite.case('bad_usage_details',lambda:[failure(lambda v=v:wire.usage({'usage':{'input_tokens_details':v}}),'usage_decode') for v in [False,0,[], '']])
    suite.case('inconsistent_usage',lambda:failure(lambda:wire.usage({'usage':{'input_tokens':1,'output_tokens':2,'total_tokens':4}}),'usage_decode'))
    def excess():
        obj=legacy.strict_json(fixture['body'].encode()); obj['usage']={'output_tokens':257}
        return failure(lambda:wire.provider_response(events.canonical(obj),200),'provider_output_budget')
    suite.case('excessive_output',excess)
    suite.case('no_external_endpoint',lambda:require(contract.config()['live_endpoint'] is None and '--endpoint' not in (r6.ROOT/'provider_http.py').read_text()))
    def retry():
        class Broken:
            calls=0
            def connect(self): self.calls+=1; raise OSError('canned connection failure')
        client=Broken(); record={'connection_attempts':0}
        try: provider_http.transmit(client,b'{}',record,lambda:None)
        except OSError: pass
        else: raise AssertionError('Broken connection accepted')
        require(client.calls==record['connection_attempts']==1)
        return record
    suite.case('no_hidden_retry',retry)
    def budget():
        with tempfile.TemporaryDirectory() as tmp:
            session=harness.Session(Path(tmp)); session.reserved=1
            events.append(Path(tmp),'episode','episode_started',{},task_id=r6.D1.id)
            with mock.patch.object(episode,'stage') as stage:
                result=failure(lambda:session.invoke({},'valid'),'request_budget_exhaustion')
                require(not stage.called)
            return result
    suite.case('budget_before_second_stage',budget)
    def unknown_observations():
        with tempfile.TemporaryDirectory() as tmp:
            session=harness.Session(Path(tmp)); session.reserved=1
            value=session.write_accounting()
            require(value['attempts_reserved']==1 and all(value[k] is None for k in ['client_connection_attempts',
                'body_sends_started','body_sends_returned','transmissions_observed']))
            return value
    suite.case('reserved_observations_unknown',unknown_observations)
    def killed():
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); out=root/'stages/proposal-1/output'; out.mkdir(parents=True)
            events.append(root,'episode','episode_started',{},task_id=r6.D1.id)
            (root/'request.json').write_bytes(request); shutil.copyfile(contract.PROMPT,root/'prompt.txt')
            r6.write_json(root/'client-arguments.json',args)
            r6.write_json(out/'http.json',{'connection_attempts':1,'body_sends_started':1,'body_sends_returned':1})
            r6.write_json(out/'server.json',{'requests':[{'complete':True}]})
            session=harness.Session(root)
            tools={'python':Path('/python'),'runtime_path':Path('/stdlib'), 'runtime':{'stdlib':'/stdlib','extension_binaries':[]}}
            with mock.patch.object(episode,'stage',side_effect=episode.StageFailure('proposal-1','resource_exhaustion','canned kill')):
                try: session.invoke(tools,'valid')
                except episode.StageFailure as error: require(error.category=='resource_exhaustion')
                else: raise AssertionError('Killed adapter accepted')
            value=r6.read_json(root/'accounting.json')
            require(value['attempts_reserved']==value['body_sends_started']==value['transmissions_observed']==1)
            require(value['reported_usage']['total_tokens'] is None)
            return value
    suite.case('killed_after_transmission',killed)
    def missing_observations():
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); out=root/'empty'; out.mkdir()
            events.append(root,'episode','episode_started',{},task_id=r6.D1.id)
            (root/'request.json').write_bytes(request); shutil.copyfile(contract.PROMPT,root/'prompt.txt')
            r6.write_json(root/'client-arguments.json',args)
            tools={'python':Path('/python'),'runtime_path':Path('/stdlib'),'runtime':{'stdlib':'/stdlib','extension_binaries':[]}}
            session=harness.Session(root)
            with mock.patch.object(episode,'stage',return_value=out):
                result=failure(lambda:session.invoke(tools,'valid'),'transport_capture_failure')
            require(session.reserved==1 and r6.read_json(root/'accounting.json')['transmissions_observed'] is None)
            return result
    suite.case('missing_http_observations',missing_observations)
    for name, change in [('production_lt_admission_order',lambda p:p['rows'][0].update(relation='lt')),
        ('production_real_admission_order',lambda p:p['final_ir']['context']['free_vars'][0].update(type='Real'))]:
        def preparation_order(change=change):
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp); capture=root/'capture'; capture.mkdir(); pipeline=root/'pipeline'; pipeline.mkdir()
                r6.write_json(capture/'context.json',r6.read_json(r6.D1.path/'context/local-context.json'))
                r6.write_json(capture/'reification.json',{'ir':prepared['input_ir']})
                altered=copy.deepcopy(prepared); change(altered); require(altered!=prepared)
                r6.write_json(pipeline/'prepared.json',altered)
                tools={'compiler':Path('/compiler'),'mounts':[],'loads':[],'lean_path':'','extras':[],'driver':Path('/driver')}
                with mock.patch.object(harness.downstream,'compile_input',return_value=root/'input'), \
                     mock.patch.object(episode,'stage',side_effect=[root/'built',capture,pipeline]) as stage:
                    result=failure(lambda:harness.prepare(root,r6.D1,tools),'unsupported_theory','provider-admission')
                    require(stage.call_count==3 and not (root/'request.json').exists())
                return {**result,'requests_constructed':0,'proposal_stages':0}
        suite.case(name,preparation_order)
    suite.case('shared_checker_binding',lambda:require(contract.config()['shared_proof_checker_sha256']==r6.sha(r6.ROOT/'envelope_proof_audit.py')))
    def source_guard():
        original=r6.sha
        with mock.patch.object(r6,'sha',side_effect=lambda p:'0'*64 if Path(p)==r6.ROOT/'provider_http.py' else original(p)):
            return rejected(contract.verify_sources,'frozen source revision')
    suite.case('source_lock_guard',source_guard)
    suite.case('missing_case_rejected',lambda:rejected(lambda:assert_complete(['a'],['a','b']),'missing/extra'))
    suite.case('duplicate_case_rejected',lambda:rejected(lambda:assert_complete(['a','a'],['a']),'duplicate'))
    suite.finish()


def native(root):
    suite=Suite(root/'provider-native.json',NATIVE_CASES)
    boundaries={
        'invalid_witness':('certificate_verification','certificate-check'),
        'malformed':('response_decode','response-decode'), 'wrong_echo':('transport_binding_failure','response-binding'),
        **{c:('outbound_envelope_binding','envelope-audit') for c in ['altered_prompt','omitted_prompt','altered_prefix','altered_body']},
        'timeout':('transport_timeout','proposal-1'),'connection_error':('transport_failure','proposal-1'),
        'disconnect':('transport_failure','proposal-1'),
        **{c:('provider_http_error','provider-response') for c in ['http429','http503','redirect']},
        'refusal':('provider_refusal','provider-response'),'incomplete':('provider_incomplete','provider-response'),
        'tool_call':('provider_output_shape','provider-response'),'malformed_provider':('provider_decode','provider-response'),
        'oversized_response':('provider_response_byte_budget','proposal-1'),
        'exhausted_budget':('request_budget_exhaustion','proposal')}
    for name in NATIVE_CASES:
        control,case=name.split('_',1); task=r6.D1 if control=='d1' else r6.C8
        def test(name=name,case=case,task=task):
            target=root/name
            command=[sys.executable,str(r6.ROOT/'provider_episode.py'),'run','--task',task.id,'--case',case,'--run-dir',str(target)]
            if contract.CONFIG.parent!=r6.ROOT/'policies': command+=['--development-policy-dir',str(contract.CONFIG.parent)]
            with (root/(name+'.log')).open('w') as log:
                completed=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
            require((target/'events.ndjson').exists(),name+' failed before episode; see log')
            rows=events.read(target/'events.ndjson')
            if case in {'valid','alternate_encoding'}:
                require(completed.returncode==0,name+' failed; see log')
                verdict=auditor.audit(target,task)
                require(all(not d['added'] and not d['removed'] for d in verdict['axiom_delta'].values()))
                if task==r6.D1:
                    compiled=next(r for r in r6.read_json(target/'prepared.json')['rows'] if r['name']=='hx')
                    require(compiled['relation']=='le' and compiled['constant']=='-16777215')
                return {'verdict_sha256':r6.sha(target/'verdict.json'),'seal_sha256':r6.sha(target/'seal.json'),
                    'events':len(rows),'sealed_files':len(r6.read_json(target/'seal.json')['retained_sha256']),
                    'solution_sha256':verdict['solution_sha256'],'axiom_delta':verdict['axiom_delta'],'accounting':verdict['accounting']}
            require(completed.returncode!=0,name+' corruption accepted')
            failure_record=r6.read_json(target/'failure.json')
            require((failure_record['failure_category'],failure_record['failure_stage'])==boundaries[case],str(failure_record))
            result=auditor.audit_failure(target,task)
            require(result['audit_accepted'] and not result['accepted'])
            require(not (target/'stages/reconstruct').exists() and not (target/'verdict.json').exists() and not (target/'seal.json').exists())
            require(not any(r['event']=='episode_finished' for r in rows))
            observed=result['accounting']; require(observed['attempts_reserved']==1 and observed['client_connection_attempts']==1)
            count=0 if case=='connection_error' else 1
            require(observed['body_sends_started']==observed['body_sends_returned']==observed['transmissions_observed']==count)
            if case in {'http429','http503','redirect','timeout','disconnect'}:
                require(len(r6.read_json(target/'stages/proposal-1/output/server.json')['requests'])==1,'hidden retry')
            if case.startswith('altered_') or case=='omitted_prompt':
                transport=result['transport_validation']
                require(transport['response_request_binding']['accepted'] is True and transport['response_validated'] is True
                    and transport['outbound_envelope']['accepted'] is False)
                require(not (target/'certificate-verdict.json').exists())
            if case=='invalid_witness':
                transport=result['transport_validation']
                require(transport['response_request_binding']['accepted'] is True and transport['outbound_envelope']['accepted'] is True)
                require(r6.read_json(target/'certificate-verdict.json')['accepted'] is False)
            return {**result,'failure_sha256':r6.sha(target/'failure.json'), 'failure_seal_sha256':r6.sha(target/'failure-seal.json'),
                    'completion_event_absent':True,'failure_marker_preserved':True}
        suite.case(name,test)
    suite.finish()


def snapshot(root):
    base='13baa73'
    paths=['experiments/r6/tasks','experiments/r6/runs','experiments/c1-cert-recovery',
        'experiments/r6/policies','experiments/r6/schema',
        *['experiments/r6/'+p for p in {*overlay.source_lock(),*contract.previous.FILES}]]
    entries=subprocess.check_output(['git','-C',str(instrument.REPO),'ls-tree','-rz',base,'--',*paths])
    records,blobs={},{}
    process=subprocess.Popen(['git','-C',str(instrument.REPO),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    try:
        for entry in entries.split(b'\0'):
            if not entry:continue
            info,name=entry.split(b'\t',1); _,kind,oid=info.split(); require(kind==b'blob')
            if oid not in blobs:
                process.stdin.write(oid+b'\n');process.stdin.flush()
                header=process.stdout.readline().split(); require(header[:2]==[oid,b'blob'])
                raw=process.stdout.read(int(header[2])); require(process.stdout.read(1)==b'\n')
                blobs[oid]=wire.sha(raw)
            records[name.decode()]=blobs[oid]
    finally:
        process.stdin.close();process.stdout.close();require(process.wait()==0)
    r6.write_json(root/'prior-artifacts.sha256.json',records)


def audits(root):
    suite=Suite(root/'provider-audits.json',AUDIT_CASES)
    for name,source,task in [('d1_retained_only','d1_valid',r6.D1),('c8_retained_only','c8_valid',r6.C8),('alternate_retained_only','d1_alternate_encoding',r6.D1)]:
        def standalone(source=source,task=task):
            with tempfile.TemporaryDirectory() as tmp:
                target=Path(tmp);retained_copy(root/source,target)
                with mock.patch.object(envelope_proof_audit,'audit',wraps=envelope_proof_audit.audit) as checker:
                    require(auditor.audit(target,task)['accepted'] and checker.call_count==1)
                return {'shared_checker_calls':1,'retained_files':len(r6.read_json(target/'seal.json')['retained_sha256'])}
        suite.case(name,standalone)
    def edit(target,name,change):
        value=r6.read_json(target/name); change(value);r6.write_json(target/name,value)
    def log_edit(target,change):
        rows=events.read(target/'events.ndjson'); change(rows);(target/'events.ndjson').write_bytes(rehash(rows))
    def mutate(name,change,contains,*,helper=False,source='d1_valid',failed=False):
        def test():
            with tempfile.TemporaryDirectory() as tmp:
                target=Path(tmp)
                if failed:
                    seal=r6.read_json(root/source/'failure-seal.json')
                    for item in [*seal['retained_sha256'],'failure-seal.json']:
                        destination=target/item;destination.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/source/item,destination)
                else:retained_copy(root/source,target)
                before={str(p.relative_to(target)):r6.sha(p) for p in target.rglob('*') if p.is_file()}
                change(target)
                after={str(p.relative_to(target)):r6.sha(p) for p in target.rglob('*') if p.is_file()}
                require(before!=after,'mutation matched nothing')
                rows=events.read(target/'events.ndjson')
                if failed: rows[-1]['payload']=r6.read_json(target/'failure.json')
                else: rows[-1]['payload']['verdict_sha256']=r6.sha(target/'verdict.json')
                (target/'events.ndjson').write_bytes(rehash(rows))
                if failed:harness.seal_failure(target)
                else:episode.seal(target,retained_sources=contract.RETAINED_SOURCES)
                with mock.patch.object(envelope_proof_audit,'audit',wraps=envelope_proof_audit.audit) as checker:
                    result=rejected(lambda:auditor.audit_failure(target,r6.D1) if failed else auditor.audit(target,r6.D1),contains)
                    if helper:require(checker.call_count==1,'mutation did not reach shared proof checker')
                return {**result,'coherently_resealed':True,'shared_checker_reached':checker.call_count==1,
                    'changed_artifacts':sorted(k for k in before.keys()|after.keys() if before.get(k)!=after.get(k))}
        suite.case(name,test)
    mutate('wrong_prompt_file',lambda p:(p/'prompt.txt').write_text('Changed'),'semantic prompt changed')
    mutate('wrong_client_arguments',lambda p:edit(p,'client-arguments.json',lambda x:x.update(store=True)),'client arguments differ')
    mutate('capture_only_mutation',lambda p:(p/'stages/proposal-1/output/received-body-1.json').write_bytes(b'{}'),'server receipt differs')
    mutate('unreported_second_capture',lambda p:shutil.copyfile(p/'stages/proposal-1/output/received-body-1.json',p/'stages/proposal-1/output/received-body-2.json'),'HTTP observation file inventory')
    mutate('hidden_retry',lambda p:edit(p,'stages/proposal-1/output/http.json',lambda x:x.update(connection_attempts=2)),'unreserved transmission')
    mutate('false_http_status',lambda p:edit(p,'stages/proposal-1/output/http.json',lambda x:x.update(http_status=503)),'HTTP status differs')
    mutate('invented_usage_zero',lambda p:edit(p,'accounting.json',lambda x:x['reported_usage'].update(cost_usd=0)),'accounting differs')
    mutate('wrong_output_extraction',lambda p:(p/'response.json').write_bytes(b'{}'),'extracted provider output')
    mutate('wrong_provider_metadata',lambda p:edit(p,'provider-metadata.json',lambda x:x.update(model='different')),'provider decode metadata')
    def drop_http(rows):
        indices=[i for i,r in enumerate(rows) if r['event']=='http_observed'];require(len(indices)==1);rows.pop(indices[0])
    mutate('missing_http_receipt',lambda p:log_edit(p,drop_http),'supervisor receipts')
    def mount(spec):
        indices=[i for i,v in enumerate(spec['argv']) if v=='/arguments.json'];require(len(indices)==2)
        spec['argv'][indices[0]-1]=str(r6.D1.path/'Pristine.lean')
    mutate('wrong_request_mount',lambda p:edit(p,'stages/proposal-1/command.json',mount),'HTTP command')
    mutate('unsafe_network_flag',lambda p:edit(p,'stages/proposal-1/command.json',lambda x:x['argv'].remove('--unshare-all')),'HTTP command')
    mutate('wrong_runtime',lambda p:edit(p,'provenance/python-runtime.json',lambda x:x.update(python_sha256='0'*64)),'pinned runtime inventory')
    mutate('wrong_new_source',lambda p:(p/'provenance/provider-harness/provider_http.py').write_text('# changed'),'retained harness source')
    mutate('wrong_shared_checker_source',lambda p:(p/'provenance/envelope-harness/envelope_proof_audit.py').write_text('# changed'),'retained harness source')
    mutate('false_attestation',lambda p:edit(p,'transport-validation.json',lambda x:x.update(model_input_verified=True)),'transport diagnostics differ')
    mutate('hidden_fallback',lambda p:edit(p,'search-policy.json',lambda x:x.update(fallback_routes=['cvc4'])),'frozen envelope policy')
    mutate('late_failure_marker',lambda p:r6.write_json(p/'failure.json',{'accepted':False}),'failure marker')
    def changed_cert(rows):
        matched=[r for r in rows if r['source']=='child_report' and r['event']=='dispatch_received'];require(len(matched)==1)
        matched[0]['payload']['data']['certificate']['tier']=2
    mutate('shared_checker_certificate',lambda p:log_edit(p,changed_cert),'received different evidence',helper=True)
    def proof(target):
        with gzip.open(target/'solution.ndjson.gz','rb') as f:raw=f.read()
        with gzip.open(target/'solution.ndjson.gz','wb') as f:f.write(raw+b'\n')
    mutate('shared_checker_proof',proof,'proof hash mismatch',helper=True)
    def validation(target,field,value):
        path=target/'validation-local.raw.json.gz'
        with gzip.open(path,'rb') as f:obj=json.load(f)
        obj['targets'][0][field]=value
        with gzip.open(path,'wb') as f:f.write(events.canonical(obj))
    mutate('shared_checker_type',lambda p:validation(p,'type_repr','False'),'frozen type/axiom policy',helper=True)
    mutate('shared_checker_axiom',lambda p:validation(p,'axioms',['sorryAx']),'frozen type/axiom policy',helper=True)
    def relabel(target):
        def change(value):
            row=value['outbound_envelope']['mismatches'][0];require(row['component']=='request_suffix');row['component']='system_message'
        edit(target,'transport-validation.json',change)
        log_edit(target,lambda rows:[change(r['payload']) for r in rows if r['event']=='transport_validated'])
        def marker(x):
            require(x['evidence']['mismatches'][0]['component']=='request_suffix')
            x['evidence']['mismatches'][0]['component']='system_message';x['error']='Envelope components differ: system_message'
        edit(target,'failure.json',marker)
    mutate('false_component_resealed',relabel,'transport diagnostics differ',source='d1_altered_body',failed=True)
    def missing_presence(target):
        def change(value):
            row=next(x for x in value['outbound_envelope']['mismatches'] if x['component']=='system_message')
            require(row['observed']['present'] is False);row['observed']={'present':True,'type':'str','bytes':0,'sha256':wire.sha(b'')}
        edit(target,'transport-validation.json',change)
        log_edit(target,lambda rows:[change(r['payload']) for r in rows if r['event']=='transport_validated'])
    mutate('false_missing_component_presence',missing_presence,'transport diagnostics differ',source='d1_omitted_prompt',failed=True)
    def current_independence():
        original=r6.sha
        live={r6.ROOT/n for n in (*overlay.source_lock(),*contract.previous.FILES,*contract.FILES) if n.endswith(('.py','.c','.ml','.lean'))}
        def checked(path):require(Path(path) not in live,'audit consulted mutable launcher');return original(path)
        with mock.patch.object(r6,'sha',side_effect=checked):require(auditor.audit(root/'d1_valid',r6.D1)['accepted'])
        return 'Locks and retained source bytes; trusted auditor implementation and frozen protocol inputs'
    suite.case('current_source_independence',current_independence)
    for name,source,task in [('legacy_broker_v1','golden-broker-v1',r6.D1),('legacy_broker_v2','golden-broker-v2',r6.D1),
        ('legacy_broker_v3','golden-broker-v3',r6.D1),('legacy_c8_v1','golden-c8-v1',r6.C8),
        ('legacy_d1_fixture','proposal-checkpoint-v2/d1_valid',r6.D1),('legacy_c8_fixture','proposal-checkpoint-v2/c8_valid',r6.C8),
        ('legacy_d1_envelope','envelope-checkpoint-v1/d1_valid',r6.D1),('legacy_c8_envelope','envelope-checkpoint-v1/c8_valid',r6.C8),
        ('legacy_alternate_envelope','envelope-checkpoint-v1/d1_alternate_encoding',r6.D1)]:
        def historical(source=source,task=task):
            check=envelope_audit.audit if source.startswith('envelope-') else episode.audit
            return {'accepted':check(r6.ROOT/'runs'/source,task)['accepted']}
        suite.case(name,historical)
    def preservation():
        values=r6.read_json(root/'prior-artifacts.sha256.json')
        require(all((instrument.REPO/p).is_file() and r6.sha(instrument.REPO/p)==h for p,h in values.items()),'prior artifacts changed')
        return {'checked_files':len(values),'changed':0,'missing':0,'git_base':'13baa73'}
    suite.case('prior_artifacts_preserved',preservation)
    suite.finish()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir',type=Path,required=True)
    parser.add_argument('--units-only',action='store_true')
    parser.add_argument('--development-policy-dir',type=Path)
    args=parser.parse_args()
    root=args.run_dir.resolve(); root.mkdir(parents=True,exist_ok=False)
    r6.write_json(root/'checkpoint.json',{'passed':False})
    if args.development_policy_dir: contract.development(args.development_policy_dir)
    contract.verify_sources(); units(root)
    if args.units_only: return
    snapshot(root); native(root); audits(root)
    suites=['provider-units.json','provider-native.json','provider-audits.json']
    r6.write_json(root/'checkpoint.json',{'passed':True,'live_model_calls':0,
        'scope':'isolated local HTTP fixture; no remote receipt, compilation or inference attestation',
        'prompt_sha256':r6.sha(contract.PROMPT),'policy_sha256':r6.sha(contract.CONFIG),'source_lock_sha256':r6.sha(contract.LOCK),
        'runtime_lock_sha256':r6.sha(contract.RUNTIME),
        'suites':{p:{'sha256':r6.sha(root/p),'count':r6.read_json(root/p)['check_count']} for p in suites}})


if __name__=='__main__': main()

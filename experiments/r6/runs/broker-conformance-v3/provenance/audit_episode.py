"""Check relationships inside a saved episode; this does not replay a kernel.

Seals detect changed bytes relative to their manifest. These checks additionally
reject contradictory claims even when a producer recomputed all those hashes.
The host, seal anchor, and recorded verifier executions remain trust assumptions.
"""
import difflib
import gzip
import hashlib
import json

import events
import instrument
import run as r6
from supervise import resource_violations

STAGES = ('capture-build','search','certificate-check','export','validation-local','validation-whole')


def require(condition, message):
    if not condition:
        raise ValueError('Episode consistency: '+message)


def verify(run, rows, packet, route, verdict, seal, local_policy):
    def path(name):
        require(name in seal['retained_sha256'], f'used artifact is not retained: {name}')
        return run/name

    def read(name):
        return r6.read_json(path(name))

    def supervisor(stage, event):
        found=[r for r in rows if r['source']=='supervisor' and r['stage']==stage and r['event']==event]
        require(len(found)==1, f'expected one {stage}/{event} receipt')
        return found[0]

    expected_order=[('episode','episode_started')]
    for stage in STAGES:
        expected_order.extend([(stage,'stage_started'),(stage,'stage_finished')])
        if stage=='search': expected_order.append((stage,'context_validated'))
        if stage=='certificate-check': expected_order.append((stage,'independent_certificate_verdict'))
        if stage.startswith('validation-'): expected_order.append((stage,'kernel_verdict'))
    expected_order.append(('episode','episode_finished'))
    require([(r['stage'],r['event']) for r in rows if r['source']=='supervisor']==expected_order,
            'missing, extra, or reordered supervisor receipts')
    require(rows[0]['source']=='supervisor' and rows[-1]['source']=='supervisor', 'invalid episode endpoints')
    begin=supervisor('search','stage_started')['sequence']
    end=supervisor('search','stage_finished')['sequence']
    require(all(begin<r['sequence']<end for r in rows if r['source']=='child_report'),
            'child observations escape the search stage')

    manifest, expected=r6.frozen_task()
    manifest_hash=r6.sha(r6.TASK/'manifest.json')
    policy=read('search-policy.json')
    require(policy['parent_task_manifest_sha256']==manifest_hash==verdict['manifest_sha256'], 'task manifest binding')
    require(verdict['challenge_sha256']==expected['challenge_sha256'], 'challenge binding')
    require(policy['name']==verdict['search_policy']=='cvc4_term_mode_v1', 'search policy identity')
    require(policy['sdk_base_commit']==instrument.BASE and policy['task_revision']==1, 'broker/task revision')
    require(policy['manifest_order']==['cvc4'] and policy['attempt_limit']==1 and policy['model_calls']==0,
            'single deterministic attempt policy')
    started=supervisor('episode','episode_started')['payload']
    require(started=={'task_manifest_sha256':manifest_hash,'search_policy_sha256':r6.sha(path('search-policy.json')),
                     'challenge_sha256':expected['challenge_sha256']}, 'episode admission receipt')
    for field, name in [('source_patch_sha256','provenance/search.patch'),
                        ('capture_sha256','input/BrokerCapture.lean'),
                        ('instrumentation_patch_sha256','provenance/instrumentation.patch')]:
        require(policy[field]==r6.sha(path(name)), f'policy/file binding: {field}')
    pristine=(r6.TASK/'Pristine.lean').read_text()
    source=r6.instrument(pristine).replace('import Capture\n','import BrokerCapture\n').replace('r6_capture_human','r6_capture_broker')
    require(path('input/Frozen.lean').read_text()==source, 'source differs from the permitted extraction')
    require(path('input/BrokerCapture.lean').read_text()==instrument.broker_capture_source(), 'capture helper changed')
    patch=''.join(difflib.unified_diff(pristine.splitlines(True),source.splitlines(True),fromfile='Pristine.lean',tofile='Frozen.lean'))
    require(path('provenance/search.patch').read_text()==patch, 'source patch differs from actual source')
    dispatch=next(r['payload']['data'] for r in rows if r['source']=='child_report' and r['event']=='dispatch_started')
    require(read('manifests/manifest-cvc4.json')==dispatch['manifests'][0], 'dispatched backend manifest')
    require(read('stages/search/output/context.json')==r6.read_json(r6.TASK/'context/local-context.json'), 'frozen context equality')
    context=supervisor('search','context_validated')['payload']
    require(context['captured_context_sha256']==r6.sha(path('stages/search/output/context.json'))
            and context['frozen_context_sha256']==r6.sha(r6.TASK/'context/local-context.json'), 'context receipt hashes')

    require(verdict['recovery_route']==route, 'recovery branch contradicts the observed search')
    certificate=read('certificate-verdict.json')
    require(certificate.get('accepted') is True and certificate.get('stage')=='certificate_verification'
            and certificate.get('reason')=={'kind':'verified_farkas'}, 'saved certificate verifier did not accept')
    require(certificate.get('certificate_hash')=='sha256:'+events.digest(packet['certificate']), 'verified certificate hash')
    require(verdict['certificate_validation']==certificate==supervisor('certificate-check','independent_certificate_verdict')['payload'],
            'certificate verdict/receipt mismatch')

    # Stream proof hashing so checking an artifact never requires loading its
    # entire exported environment into the host Python process.
    digest=hashlib.sha256()
    length=0
    with gzip.open(path('solution.ndjson.gz'),'rb') as f:
        while block:=f.read(1024*1024):
            length+=len(block)
            require(length<=256*1024**2, 'saved proof exceeds the export budget')
            digest.update(block)
    require(digest.hexdigest()==verdict['solution_sha256'], 'saved proof hash disagrees with the verdict')
    baselines={t['name']:t for t in expected['targets']}
    deltas={}
    for kind, target, config in [('local',r6.LOCAL,local_policy),('whole',r6.WHOLE,r6.policy([r6.WHOLE],True))]:
        require(read(f'validation-input/{kind}/policy.json')==config, f'{kind} validation policy')
        with gzip.open(path(f'validation-{kind}.raw.json.gz'),'rb') as f:
            data=f.read(4*1024**2+1)
        require(len(data)<=4*1024**2, 'oversized frozen-task validation report')
        report=json.loads(data)
        require(report.get('accepted') is True and report.get('stage')=='complete'
                and report.get('kernel_version')=='4.32.2' and report.get('local_proof_binding_checked') is True,
                f'{kind} replay/required reference did not pass')
        require(type(report.get('checked_declarations')) is int and report['checked_declarations']>0,
                f'{kind} replay has no checked declarations')
        targets=report.get('targets',[])
        require(len(targets)==1 and targets[0].get('name')==target, f'{kind} expected declaration missing')
        t=targets[0]
        require(all(t.get(k) is True for k in ['declaration_exists','statement_and_dependencies_match','kernel_accepted']),
                f'{kind} final acceptance predicate')
        t['type_sha256']=hashlib.sha256(t.pop('type_repr').encode()).hexdigest()
        t['type_hash_format']='Lean-4.32.2-reprStr-Expr-UTF8'
        require(t['type_sha256']==baselines[target]['type_sha256'], f'{kind} frozen type fingerprint')
        require(isinstance(t['axioms'],list) and all(isinstance(a,str) for a in t['axioms'])
                and set(t['axioms'])<=set(r6.AXIOMS) and len(t['axioms'])==len(set(t['axioms'])), f'{kind} axiom policy')
        require(report==verdict['final_validation'][kind]==supervisor('validation-'+kind,'kernel_verdict')['payload'],
                f'{kind} kernel report/receipt/verdict mismatch')
        deltas[target]={'added':sorted(set(t['axioms'])-set(baselines[target]['axioms'])),
                        'removed':sorted(set(baselines[target]['axioms'])-set(t['axioms']))}
    require(verdict['axiom_delta']==deltas, 'axiom delta disagrees with the audited footprints')
    require(verdict.get('local_proof_required_reference')==local_policy['required_dependency'][1]
            ==policy.get('required_local_proof_reference'), 'reconstruction reference policy')

    require(set(verdict['resources'])==set(STAGES), 'missing or extra stage resource records')
    for stage in STAGES:
        spec=read(f'stages/{stage}/command.json')
        stats=read(f'stages/{stage}/{stage}.process.json')
        require(spec['stage']==stage, f'{stage} command identity')
        require(stats==verdict['resources'][stage]==supervisor(stage,'stage_finished')['payload'], f'{stage} resource record mismatch')
        require(stats['exit_code']==0 and stats['resource_exhausted'] is None
                and stats.get('monitor_error') is None and stats.get('observation_error') is None
                and stats.get('workload_empty_after_cleanup') is True, f'{stage} process/monitor did not succeed')
        for key in ['wall_seconds','cgroup_cpu_usec','cgroup_memory_peak_bytes','output_bytes']:
            require(type(stats[key]) in (int,float) and stats[key]>=0, f'{stage} invalid resource measurement')
        # Older retained stages do not split execution and cleanup wall time.
        wall=stats.get('execution_wall_seconds',stats['wall_seconds'])
        require(not resource_violations(spec,wall,stats['cgroup_cpu_usec'],stats['memory_events'],stats['output_bytes']),
                f'{stage} accepted despite exceeding its budget')
        receipt=supervisor(stage,'stage_started')['payload']
        require(receipt['command_file']==f'stages/{stage}/command.json', f'{stage} command receipt')
        for flag, field in [('wall_limit_seconds','wall_seconds'),('cpu_limit_seconds','cpu_seconds'),('memory_limit_bytes','memory_bytes')]:
            require(receipt[flag]==spec[field], f'{stage} resource policy mismatch')
        if stage=='search':
            for field in ['wall_seconds','cpu_seconds','memory_bytes']:
                require(spec[field]==policy['search_stage_'+field], 'search budget differs from frozen policy')
    require(supervisor('episode','episode_finished')['payload']=={'accepted':True,'verdict_sha256':r6.sha(path('verdict.json'))},
            'terminal acceptance verdict')

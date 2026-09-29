#!/usr/bin/env python3
"""Regressions for the September 7 review, with an exact expected-case gate.

Audits and controlled stage/monitor injections run here. Native resource
observations come from a separately executed resource_probe.py run. This
command neither launches search nor replays a kernel.
"""
import argparse
from collections import Counter
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

import episode
import events
import run as r6

REVIEW=r6.ROOT/'reviews/2026-09-07'
AUDIT_ERRORS={
    'wrong_recovery_branch':'recovery branch contradicts the observed search',
    'negative_certificate_verdict':'certificate verdict/receipt mismatch',
    'missing_kernel_targets':'local kernel report/receipt/verdict mismatch',
    'wrong_solution_hash':'saved proof hash disagrees with the verdict',
    'resource_error_in_verdict':'search resource record mismatch',
    'missing_independent_check_event':'missing, extra, or reordered supervisor receipts',
    'changed_source':'source differs from the permitted extraction',
    'missing_recovery_start':'Recovery start/finish observations are incomplete or out of order',
}
STAGE_CASES={('valid_certificate','supervisor_failure'),
             ('broker_proof_local','stage_rejected'),
             ('broker_proof_local','supervisor_failure'),
             ('invalid_witness','resource_exhaustion')}
MONITOR_CASES={'below_budget_at_eof','at_budget_at_eof','over_budget_at_eof','archived_over_budget_at_eof'}
NATIVE_CASES={f'finite_{i}' for i in range(6)} | {'terminal_event'}
EXPECTED_CASES=({'audit_'+n for n in AUDIT_ERRORS}
                | {'stage_'+n+'_'+category for n,category in STAGE_CASES}
                | {'monitor_'+n for n in MONITOR_CASES}
                | {'native_'+n for n in NATIVE_CASES}
                | {'retained_golden-broker-v1','retained_golden-broker-v2','retained_golden-c8-v1'})


def require(condition,message):
    if not condition: raise AssertionError(message)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir',type=Path)
    parser.add_argument('--resource-run',type=Path,default=r6.ROOT/'runs/resource-review-after-v1')
    args=parser.parse_args()
    out=(args.run_dir or r6.ROOT/'runs'/f'further-review-{time.time_ns()}').resolve()
    out.mkdir(parents=True,exist_ok=False)
    report={'suite_version':'r6-further-review-1','passed':False,
            'expected_cases':sorted(EXPECTED_CASES),'checks':[],
            'native_resource_run':str(args.resource_run.resolve())}
    r6.write_json(out/'tests.json',report)

    def record(name,observed):
        report['checks'].append({'case':name,'passed':True,'observed':observed})
        r6.write_json(out/'tests.json',report)

    def probe(name):
        result=subprocess.run([sys.executable,str(REVIEW/(name+'_probe.py'))],check=True,
                              capture_output=True,text=True,timeout=120)
        (out/(name+'-after.json')).write_text(result.stdout)
        return r6.read_json(out/(name+'-after.json'))

    # Positive audits use only the sealed publication files, never native cache
    # products or ignored uncompressed exports from the original run directory.
    for name in ['golden-broker-v1','golden-broker-v2','golden-c8-v1']:
        source=r6.ROOT/'runs'/name
        seal=r6.read_json(source/'seal.json')
        with tempfile.TemporaryDirectory(prefix='r6-retained-audit-') as temp:
            copy=Path(temp)
            for item in [*seal['retained_sha256'],'seal.json']:
                target=copy/item
                target.parent.mkdir(parents=True,exist_ok=True)
                shutil.copyfile(source/item,target)
            require(episode.audit(copy)['accepted'] is True,'Positive retained artifact rejected')
        record('retained_'+name,{'source_seal_sha256':r6.sha(source/'seal.json'),
                                'retained_files':len(seal['retained_sha256'])})

    for row in probe('audit'):
        name=row['case']
        require(name in AUDIT_ERRORS and row['audit_accepted'] is False
                and AUDIT_ERRORS[name] in (row['error'] or ''),f'Wrong audit rejection: {row}')
        record('audit_'+name,row)
    for row in probe('stage'):
        key=(row['case'],row['injected_failure'])
        require(key in STAGE_CASES and row['counted_as_pass'] is False
                and row['error']=='injected post-verdict failure',f'Wrong stage rejection: {row}')
        record('stage_'+'_'.join(key),row)
    for row in probe('monitor'):
        name=row['case']
        require(name in MONITOR_CASES,f'Unknown monitor case: {name}')
        stats=row['process']
        exhausted=name=='over_budget_at_eof'
        require(row['monitor_exit_code']==int(exhausted) and stats['exit_code']==0
                and stats['resource_exhausted']==('cpu_time' if exhausted else None)
                and stats['monitor_error'] is None and stats.get('observation_error') is None
                and stats['workload_empty_after_cleanup'] is True,f'Wrong EOF decision: {row}')
        require(row['resource_limit_events']==([{'resource':'cpu_time','detection':'final_accounting'}] if exhausted else []),
                f'EOF decision did not exercise final accounting: {row}')
        if exhausted or name.startswith('archived_'):
            require(stats['cgroup_cpu_usec']==9000,'Controlled CPU measurement was not used')
        record('monitor_'+name,row)

    native=args.resource_run.resolve()
    native_rows=events.read(native/'events.ndjson')
    for row in r6.read_json(native/'probe.json'):
        name=row['case']
        require(name in NATIVE_CASES and row['accepted'] is False,f'Native rejection missing: {row}')
        stats=r6.read_json(native/f'stages/{name}/{name}.process.json')
        receipts=[e['payload'] for e in native_rows if e['stage']==name and e['event']=='stage_finished']
        require(stats==row['process'] and receipts==[stats],'Native process/receipt mismatch')
        require(stats['monitor_error'] is None and stats['workload_empty_after_cleanup'] is True,
                f'Unhealthy native monitor: {row}')
        if name=='terminal_event':
            require(row['category']=='observation_protocol_failure' and bool(stats['observation_error'])
                    and stats['resource_exhausted'] is None,'Wrong observation rejection boundary')
            require(not any(e['source']=='child_report' and e['event'] in events.TERMINAL_EVENTS for e in native_rows),
                    'Child closed the native event log')
        else:
            spec=r6.read_json(native/f'stages/{name}/command.json')
            require(row['category']=='resource_exhaustion' and stats['resource_exhausted']=='cpu_time'
                    and row['limit_usec']==spec['cpu_seconds']*1_000_000<stats['cgroup_cpu_usec']
                    and stats['observation_error'] is None,'Wrong native budget decision')
        record('native_'+name,row)

    counts=Counter(row['case'] for row in report['checks'])
    require(set(counts)==EXPECTED_CASES and all(n==1 for n in counts.values()),'Incomplete or duplicated review checks')
    sources=['test_review.py','test_episode.py','test_validation.py','episode.py','audit_episode.py',
             'supervise.py','events.py','instrument.py','run.py','task_spec.py','c8_control.py','test_task_identity.py',
             *['reviews/2026-09-07/'+n+'_probe.py' for n in ['audit','stage','monitor','resource']],
             'reviews/2026-09-07/resource_probe.c',
             *['schema/'+p.name for p in sorted((r6.ROOT/'schema').glob('*.json'))]]
    for name in sources:
        target=out/'provenance'/name
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(r6.ROOT/name,target)
    report['artifact_sha256']={str(p.relative_to(out)):r6.sha(p) for p in sorted(out.rglob('*'))
                               if p.is_file() and p!=out/'tests.json'}
    report['native_artifact_sha256']={str(p.relative_to(native)):r6.sha(p) for p in sorted(native.rglob('*'))
                                      if p.is_file() and p.name!='fixture'}
    report['native_fixture_sha256']=r6.sha(native/'fixture')
    report['passed']=True
    r6.write_json(out/'tests.json',report)
    print(f'{len(report["checks"])} review checks passed: {out}/tests.json')


if __name__=='__main__':
    main()

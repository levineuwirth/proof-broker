"""R6-012 site stages for the cohort driver: three frozen functions with one line changed each.

The frozen supervisor runs in its own process and appends receipts through the frozen registry, and the frozen event schema
enumerates task ids; both name only the two registered controls. `stage` is `campaign_network.stage` (the one stage that may
reach the network) launching `site_supervise.py` instead of `supervise.py`; `final_validation` is `episode.final_validation`
calling `site_stage.stage` instead of `episode.stage`; `seal` is `credential_episode.seal` reading the events through
`observations` below instead of `episode.observations`. `test_cohort.py` pins each difference to that one line; `command`,
the sandbox, the checker and the seal format are the frozen ones.
"""
import copy
import hashlib
import subprocess
import sys
import uuid

import jsonschema

from campaign_network import command
import credential_episode
from credential_episode import contract
import episode
from episode import local_policy
import events
import run as r6
import site_stage
import site_task


def observations(run):
    """`episode.observations` under the frozen event schema with only its task enumeration widened to the reviewed sites."""
    rows = events.read(run/'events.ndjson')
    schema = copy.deepcopy(r6.read_json(episode.ROOT/'schema/event.schema.json'))
    if schema['properties']['task_id'] != {'enum': ['verinf-d1-70', 'c1-c8-2p18']}: raise ValueError('frozen event schema changed')
    schema['properties']['task_id'] = {'enum': list(site_task.primary())}
    for row in rows:
        jsonschema.validate(row, schema)
    return rows


def stage(run, name, binary, argv, mounts, grant, *, shared_network, extra_binaries=(), wall, cpu, memory, output_limit):
    rows = events.read(run/'events.ndjson')
    if not rows: raise ValueError('A stage requires an initialized task receipt log')
    if rows[-1]['source'] == 'supervisor' and rows[-1]['event'] in events.TERMINAL_EVENTS:
        raise ValueError('Episode is already closed')
    records = run/'stages'/name
    records.mkdir(parents=True, exist_ok=False)
    (records/'output').mkdir()
    if not grant.is_dir(): raise ValueError('campaign_grant_slot_missing')
    cmd, spec = command(run, name, binary, argv, mounts, grant, shared_network=shared_network, extra_binaries=extra_binaries,
                        wall=wall, cpu=cpu, memory=memory, output_limit=output_limit)
    r6.write_json(records/'command.json', spec)
    unit = 'r6-'+uuid.uuid4().hex+'.scope'
    scope = ['systemd-run', '--user', '--scope', '--quiet', '--unit='+unit,
             '-p', 'Delegate=yes', '-p', 'OOMPolicy=continue', '-p', 'TasksMax=128',
             '-p', f'RuntimeMaxSec={wall+15}',
             sys.executable, str(r6.ROOT/'site_supervise.py'), str(records/'command.json')]
    r6.write_json(records/'scope-command.json', scope)
    try:
        result = subprocess.run(scope, capture_output=True, text=True, timeout=wall+30)
    except (subprocess.TimeoutExpired, KeyboardInterrupt):
        subprocess.run(['systemctl', '--user', 'kill', '--kill-whom=all', '--signal=KILL', unit],
                       capture_output=True, timeout=10)
        raise episode.StageFailure(name, 'supervisor_failure', f'{name}: outer watchdog interrupted the scope')
    (records/'supervisor.stdout').write_text(result.stdout)
    (records/'supervisor.stderr').write_text(result.stderr)
    process = records/f'{name}.process.json'
    if not process.exists():
        raise episode.StageFailure(name, 'supervisor_failure', f'{name}: no supervisor verdict')
    stats = r6.read_json(process)
    bad_monitor = stats.get('monitor_error') or not stats.get('workload_empty_after_cleanup', False)
    if result.returncode != 0 or stats['exit_code'] != 0 or stats['resource_exhausted'] or bad_monitor or stats.get('observation_error'):
        category = 'resource_exhaustion' if stats['resource_exhausted'] else 'stage_rejected'
        if stats.get('observation_error'): category = 'observation_protocol_failure'
        if bad_monitor or (result.returncode != 0 and stats['exit_code'] == 0
                           and not stats['resource_exhausted'] and not stats.get('observation_error')):
            category = 'supervisor_failure'
        raise episode.StageFailure(name, category, f'{name}: stage failed; see {records}', stats)
    return records/'output'


def final_validation(run, challenge, solution, checker, expected, task):
    reports = {}
    for name, config in [('local', local_policy(task)), ('whole', r6.policy([task.whole], True,task=task))]:
        inp = run/'validation-input'/name
        inp.mkdir(parents=True)
        r6.write_json(inp/'policy.json', config)
        out = site_stage.stage(run, 'validation-'+name, checker,
                    ['/challenge.ndjson', '/solution.ndjson', '/policy.json', '/out/verdict.json'],
                    [(challenge, '/challenge.ndjson'), (solution, '/solution.ndjson'), (inp/'policy.json', '/policy.json')])
        report = r6.read_json(out/'verdict.json')
        r6.accepted(report)
        r6.pack(out/'verdict.json', run/f'validation-{name}.raw.json.gz')
        for t in report['targets']:
            t['type_sha256'] = hashlib.sha256(t.pop('type_repr').encode()).hexdigest()
            t['type_hash_format'] = 'Lean-4.32.2-reprStr-Expr-UTF8'
        reports[name] = report
        events.append(run, 'validation-'+name, 'kernel_verdict', report)
    baseline = {t['name']: set(t['axioms']) for t in expected['targets']}
    delta = {t['name']: {'added': sorted(set(t['axioms'])-baseline[t['name']]),
                         'removed': sorted(baseline[t['name']]-set(t['axioms']))}
             for report in reports.values() for t in report['targets']}
    return reports, delta


def seal(run, accepted, ephemeral=None):
    """`ephemeral` carries a frozen build-product inventory into a resealed copy."""
    rows = observations(run)
    retained, ephemeral = {}, dict(ephemeral or {})
    for p in sorted(run.rglob('*')):
        if not p.is_file() or p.name == 'seal.json': continue
        name = str(p.relative_to(run))
        drop = ('.olean' in p.name or p.suffix in {'.ilean', '.c', '.o'}
                or (p.name in {'proof.ndjson', 'verdict.json'} and '/output/' in name)
                or name.endswith('/export/export.stdout'))
        (ephemeral if drop and name not in contract.RETAINED_SOURCES else retained)[name] = r6.sha(p)
    r6.write_json(run/'seal.json', {'schema_version': 'r6-credential-seal-1', 'accepted': accepted,
        'event_count': len(rows), 'last_event_hash': rows[-1]['event_hash'],
        'retained_sha256': retained, 'ephemeral_sha256': ephemeral})

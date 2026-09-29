"""The one stage that may reach the network, with the supervisor owning receipts.

Mirrors `episode.stage` minus the network namespace, as the pilot's did, with
two corrections: this module appends no `stage_started`/`stage_finished`
receipts of its own — `supervise.py` already records both, and the pilot's
extra pair produced duplicate receipts for one process — and it mounts the
reservation's authoritative slot, created beside the ledger at reservation
time, writable at `/grant`, where the sender commits its single-use send grant
before the first header byte. `shared_network=False` keeps `--unshare-net`,
so a rehearsal stays fully isolated while exercising the same grant path. When
shared, the namespace is shared, not filtered.
"""
import subprocess
import sys
import uuid

import episode
import events
import run as r6

NAMESPACES = ('--unshare-user', '--unshare-ipc', '--unshare-pid', '--unshare-uts', '--unshare-cgroup')
RESOLVER = '/etc/resolv.conf'


def command(run, name, binary, argv, mounts, grant, *, shared_network, extra_binaries=(), wall, cpu, memory, output_limit):
    records = run/'stages'/name
    output = records/'output'
    namespaces = NAMESPACES if shared_network else (*NAMESPACES, '--unshare-net')
    cmd = ['bwrap', *namespaces, '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
           '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
           '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
           '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
    deps = set()
    for executable in [binary, *extra_binaries]:
        deps.update(episode.libraries(executable))
    for lib in sorted(deps):
        cmd += ['--ro-bind', str(lib.resolve()), str(lib)]
    if shared_network: cmd += ['--ro-bind', RESOLVER, RESOLVER]
    for host, guest in mounts:
        cmd += ['--ro-bind', str(host.resolve()), guest]
    cmd += ['--ro-bind', str(binary), '/runner/bin/program', '--bind', str(output), '/out',
            '--bind', str(grant), '/grant', '/runner/bin/program', *argv]
    return cmd, {'run': str(run), 'stage': name, 'records': str(records), 'argv': cmd,
                 'wall_seconds': wall, 'cpu_seconds': cpu, 'memory_bytes': memory,
                 'output_bytes': output_limit, 'capture_events': False,
                 'network_namespace': 'shared_with_host' if shared_network else 'unshared', 'grant_slot': str(grant),
                 'network_scope': 'shared namespace, not an egress filter; destination is enforced by the '
                                  'actor endpoint check and this recorded command'}


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
             sys.executable, str(r6.ROOT/'supervise.py'), str(records/'command.json')]
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

"""The one stage in R6 that is allowed to reach the network.

`episode.stage` is frozen under earlier policy locks and always passes
`--unshare-all`, which implies `--unshare-net`. A provider request needs a route
out, so this module builds that single stage's command explicitly instead of
weakening the shared builder. Every other stage in a pilot episode still goes
through `episode.stage` unchanged.

What is given up is precisely the network namespace. User, IPC, PID, UTS and
cgroup namespaces, the capability drop, the cleared environment, the new
session, the read-only mounts and the supervisor's resource accounting are all
retained. The namespace is *shared*, not filtered: this is not an egress
allowlist, and the destination is controlled by the endpoint check inside the
actor and by the audited command, not by the sandbox.
"""
import subprocess
import sys
import uuid

import episode
import events
import run as r6

# Everything `--unshare-all` would give except the network namespace.
NAMESPACES = ('--unshare-user', '--unshare-ipc', '--unshare-pid', '--unshare-uts', '--unshare-cgroup')
RESOLVER = '/etc/resolv.conf'


def command(run, name, binary, argv, mounts, *, extra_binaries=(), wall, cpu, memory, output_limit):
    """Mirror `episode.stage`'s command, minus the network namespace."""
    records = run/'stages'/name
    output = records/'output'
    cmd = ['bwrap', *NAMESPACES, '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
           '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
           '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
           '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
    deps = set()
    for executable in [binary, *extra_binaries]:
        deps.update(episode.libraries(executable))
    for lib in sorted(deps):
        cmd += ['--ro-bind', str(lib.resolve()), str(lib)]
    # Name resolution is the one host file the network path additionally needs.
    cmd += ['--ro-bind', RESOLVER, RESOLVER]
    for host, guest in mounts:
        cmd += ['--ro-bind', str(host.resolve()), guest]
    cmd += ['--ro-bind', str(binary), '/runner/bin/program', '--bind', str(output), '/out',
            '/runner/bin/program', *argv]
    return cmd, {'run': str(run), 'stage': name, 'records': str(records), 'argv': cmd,
                 'wall_seconds': wall, 'cpu_seconds': cpu, 'memory_bytes': memory,
                 'output_bytes': output_limit, 'capture_events': False,
                 'network_namespace': 'shared_with_host',
                 'network_scope': 'shared namespace, not an egress filter; destination is enforced by the '
                                  'actor endpoint check and this recorded command'}


def stage(run, name, binary, argv, mounts, *, extra_binaries=(), wall, cpu, memory, output_limit):
    rows = events.read(run/'events.ndjson')
    if not rows: raise ValueError('A stage requires an initialized task receipt log')
    if rows[-1]['source'] == 'supervisor' and rows[-1]['event'] in events.TERMINAL_EVENTS:
        raise ValueError('Episode is already closed')
    records = run/'stages'/name
    records.mkdir(parents=True, exist_ok=False)
    (records/'output').mkdir()
    cmd, spec = command(run, name, binary, argv, mounts, extra_binaries=extra_binaries,
                        wall=wall, cpu=cpu, memory=memory, output_limit=output_limit)
    r6.write_json(records/'command.json', spec)
    unit = 'r6-'+uuid.uuid4().hex+'.scope'
    scope = ['systemd-run', '--user', '--scope', '--quiet', '--unit='+unit,
             '-p', 'Delegate=yes', '-p', 'OOMPolicy=continue', '-p', 'TasksMax=128',
             '-p', f'RuntimeMaxSec={wall+15}',
             sys.executable, str(r6.ROOT/'supervise.py'), str(records/'command.json')]
    r6.write_json(records/'scope-command.json', scope)
    events.append(run, name, 'stage_started', {'command_file': f'stages/{name}/command.json',
        'wall_limit_seconds': wall, 'cpu_limit_seconds': cpu, 'memory_limit_bytes': memory,
        'network_namespace': 'shared_with_host'})
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
    events.append(run, name, 'stage_finished', stats)
    if result.returncode != 0 or stats['exit_code'] != 0 or stats['resource_exhausted'] or stats.get('monitor_error'):
        raise episode.StageFailure(name, 'stage_rejected', f'{name}: stage failed; see {records}', stats)
    return records/'output'

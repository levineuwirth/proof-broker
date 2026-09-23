"""R6-011 site stage: `episode.stage` with one line changed, the supervisor it launches.

The frozen supervisor (`supervise.py`) runs in its own process and appends its receipts through the frozen registry, which names
only the two registered controls. `site_supervise.py` registers the verified census sites in that process and then runs the
frozen supervisor unchanged. Every other byte of this function is `episode.stage`; `test_site.py` pins the difference to that
single line.
"""
import subprocess
import sys
import uuid

import events
from episode import ROOT, StageFailure, libraries
import run as r6


def stage(run, name, binary, argv, mounts, *, compiler=None, env=None, extra_binaries=(),
          wall=150, cpu=120, memory=8 * 1024**3, output_limit=256 * 1024**2, capture_events=False):
    log = run/'events.ndjson'
    rows = events.read(log) if log.exists() else []
    if not rows:
        raise ValueError('A stage requires an initialized task receipt log')
    r6.get_task(rows[0]['task_id'])
    if rows[-1]['source'] == 'supervisor' and rows[-1]['event'] in events.TERMINAL_EVENTS:
        raise ValueError('Episode is already closed')
    records = run/'stages'/name
    records.mkdir(parents=True, exist_ok=False)
    output = records/'output'
    output.mkdir()
    cmd = ['bwrap', '--unshare-all', '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
           '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
           '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
           '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
    if compiler:
        cmd += ['--ro-bind', str(compiler/'lib'), '/toolchain/lib',
                '--ro-bind', str(compiler/'bin/lean'), '/toolchain/bin/lean',
                '--setenv', 'LEAN_SYSROOT', '/toolchain',
                '--setenv', 'LD_LIBRARY_PATH', '/toolchain/lib/lean:/toolchain/lib']
    deps = set()
    for executable in [binary, *extra_binaries]:
        deps.update(libraries(executable))
    for lib in sorted(deps):
        if compiler and lib.is_relative_to(compiler):
            continue
        cmd += ['--ro-bind', str(lib.resolve()), str(lib)]
    for host, guest in mounts:
        cmd += ['--ro-bind', str(host.resolve()), guest]
    for key, value in (env or {}).items():
        cmd += ['--setenv', key, value]
    program = '/toolchain/bin/program' if compiler else '/runner/bin/program'
    cmd += ['--ro-bind', str(binary), program, '--bind', str(output), '/out', program, *argv]
    spec = {'run': str(run), 'stage': name, 'records': str(records), 'argv': cmd,
            'wall_seconds': wall, 'cpu_seconds': cpu, 'memory_bytes': memory,
            'output_bytes': output_limit, 'capture_events':capture_events}
    r6.write_json(records/'command.json', spec)
    unit = 'r6-'+uuid.uuid4().hex+'.scope'
    scope = ['systemd-run', '--user', '--scope', '--quiet', '--unit='+unit,
             '-p', 'Delegate=yes', '-p', 'OOMPolicy=continue', '-p', 'TasksMax=128',
             '-p', f'RuntimeMaxSec={wall+15}',
             sys.executable, str(ROOT/'site_supervise.py'), str(records/'command.json')]
    r6.write_json(records/'scope-command.json', scope)
    try:
        result = subprocess.run(scope, capture_output=True, text=True, timeout=wall+30)
    except (subprocess.TimeoutExpired, KeyboardInterrupt):
        # Independent backstop if the monitor cannot complete its own cleanup.
        subprocess.run(['systemctl','--user','kill','--kill-whom=all','--signal=KILL',unit],
                       capture_output=True, timeout=10)
        raise StageFailure(name, 'supervisor_failure', f'{name}: outer watchdog interrupted the scope')
    (records/'supervisor.stdout').write_text(result.stdout)
    (records/'supervisor.stderr').write_text(result.stderr)
    process = records/f'{name}.process.json'
    if not process.exists():
        raise StageFailure(name, 'supervisor_failure', f'{name}: no supervisor verdict: {result.stderr[-1500:]}')
    stats = r6.read_json(process)
    bad_monitor = stats.get('monitor_error') or not stats.get('workload_empty_after_cleanup', False)
    if result.returncode != 0 or stats['exit_code'] != 0 or stats['resource_exhausted'] or bad_monitor or stats.get('observation_error'):
        category = 'resource_exhaustion' if stats['resource_exhausted'] else 'stage_rejected'
        if stats.get('observation_error'):
            category = 'observation_protocol_failure'
        if bad_monitor or (result.returncode != 0 and stats['exit_code'] == 0
                           and not stats['resource_exhausted'] and not stats.get('observation_error')):
            category = 'supervisor_failure'
        raise StageFailure(name, category, f'{name}: stage failed; see {records}', stats)
    return output

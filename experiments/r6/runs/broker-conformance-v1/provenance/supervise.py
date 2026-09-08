"""Run one isolated stage in a dedicated systemd cgroup.

This process stays outside Bubblewrap and the workload's resource cgroup.
Only it can write the episode log. Resource figures cover the sandbox tree.
"""
import json
import os
from pathlib import Path
import resource
import selectors
import subprocess
import sys
import time

import events


def main(spec_path):
    spec = json.loads(Path(spec_path).read_text())
    run, stage = Path(spec['run']), spec['stage']
    out = Path(spec['records'])
    cg = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip().split('::', 1)[1].lstrip('/')
    if not cg.name.startswith('r6-'):
        raise RuntimeError('Dedicated R6 cgroup is required')
    # Move the trusted monitor into a sibling before enabling subtree controls.
    # A workload OOM may kill the whole workload, but must not kill its recorder.
    monitor, workload = cg/'monitor', cg/'workload'
    monitor.mkdir()
    (monitor/'cgroup.procs').write_text(str(os.getpid()))
    (cg/'cgroup.subtree_control').write_text('+cpu +memory +pids')
    workload.mkdir()
    (workload/'memory.max').write_text(str(spec['memory_bytes']))
    (workload/'memory.swap.max').write_text('0')
    (workload/'memory.oom.group').write_text('1')
    (workload/'pids.max').write_text('120')
    memory_max = int((workload/'memory.max').read_text())
    if memory_max != spec['memory_bytes'] or int((workload/'memory.swap.max').read_text()) != 0:
        raise RuntimeError('Cgroup memory policy was not applied')

    def cpu():
        return int(dict(line.split() for line in (workload/'cpu.stat').read_text().splitlines())['usage_usec'])

    def limits():
        (workload/'cgroup.procs').write_text(str(os.getpid()))
        resource.setrlimit(resource.RLIMIT_AS, (32 * 1024**3,) * 2)
        resource.setrlimit(resource.RLIMIT_FSIZE, (256 * 1024**2,) * 2)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    start, cpu_start = time.monotonic(), cpu()
    events.append(run, stage, 'stage_started', {'command_file': str(Path(spec_path).relative_to(run)),
        'wall_limit_seconds': spec['wall_seconds'], 'cpu_limit_seconds': spec['cpu_seconds'],
        'memory_limit_bytes': memory_max, 'cgroup': str(workload)})
    proc = subprocess.Popen(spec['argv'], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True, preexec_fn=limits)
    sel = selectors.DefaultSelector()
    buffers = {'stdout': b'', 'stderr': b''}
    files = {s: (out/f'{stage}.{s}').open('xb') for s in buffers}
    for stream, pipe in [('stdout', proc.stdout), ('stderr', proc.stderr)]:
        os.set_blocking(pipe.fileno(), False)
        sel.register(pipe, selectors.EVENT_READ, stream)
    termination = None
    monitor_error = None
    total_bytes = 0
    try:
        while sel.get_map() or proc.poll() is None:
            exceeded = None
            memory_events = dict(line.split() for line in (workload/'memory.events').read_text().splitlines())
            if int(memory_events['oom_kill']) > 0:
                exceeded = 'memory'
            elif time.monotonic() - start > spec['wall_seconds']:
                exceeded = 'wall_time'
            elif cpu() - cpu_start > spec['cpu_seconds'] * 1_000_000:
                exceeded = 'cpu_time'
            elif total_bytes > spec['output_bytes']:
                exceeded = 'output_bytes'
            if exceeded and termination is None:
                termination = exceeded
                events.append(run, stage, 'resource_limit', {'resource': exceeded})
                (workload/'cgroup.kill').write_text('1')
            for key, _ in sel.select(0.02):
                data = os.read(key.fd, 65536)
                stream = key.data
                if not data:
                    sel.unregister(key.fileobj)
                    key.fileobj.close()
                    continue
                total_bytes += len(data)
                if total_bytes > spec['output_bytes']:
                    continue
                files[stream].write(data)
                if stream != 'stderr':
                    continue
                buffers[stream] += data
                while b'\n' in buffers[stream]:
                    line, buffers[stream] = buffers[stream].split(b'\n', 1)
                    if line.startswith(b'R6_EVENT '):
                        child = json.loads(line[9:])
                        if set(child) != {'component', 'event', 'data'} or not isinstance(child['data'], dict):
                            raise ValueError('Malformed broker observation')
                        events.append(run, stage, child['event'],
                                      {'component': child['component'], 'data': child['data']}, 'child_report')
                if len(buffers[stream]) > spec['output_bytes']:
                    raise ValueError('Unterminated observation exceeds output budget')
        code = proc.wait()
    except Exception as error:
        monitor_error = str(error)
    finally:
        (workload/'cgroup.kill').write_text('1')
        code = proc.wait()
        sel.close()
        for f in files.values(): f.close()
    memory_events = dict((k, int(v)) for k,v in
        (line.split() for line in (workload/'memory.events').read_text().splitlines()))
    # The process can die between the last poll and EOF. Preserve that OOM too.
    if termination is None and memory_events['oom_kill']:
        termination = 'memory'
        events.append(run, stage, 'resource_limit', {'resource': termination})
    deadline = time.monotonic() + 5
    while 'populated 1' in (workload/'cgroup.events').read_text() and time.monotonic() < deadline:
        time.sleep(0.01)
    empty = 'populated 0' in (workload/'cgroup.events').read_text()
    stats = {'exit_code': code, 'resource_exhausted': termination,
             'wall_seconds': time.monotonic()-start, 'cgroup_cpu_usec': cpu()-cpu_start,
             'cgroup_memory_peak_bytes': int((workload/'memory.peak').read_text()),
             'memory_events': memory_events, 'monitor_error': monitor_error,
             'workload_empty_after_cleanup': empty,
             'output_bytes': total_bytes, 'accounting_scope': 'sandbox_process_tree'}
    (out/f'{stage}.process.json').write_text(json.dumps(stats, indent=2)+'\n')
    events.append(run, stage, 'stage_finished', stats)
    return code if code >= 0 and not monitor_error and empty and not termination else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1]))

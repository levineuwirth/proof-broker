"""Exercise the actual monitor at EOF with controlled cgroup counters.

Real EOF pipes and the real monitor control flow are used. No child is launched:
the cgroup files and successful child exit are simulated. This isolates the
last-poll-to-exit race from scheduler timing; native controls remain separate.
"""
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
import events
import run as r6
import supervise


def trial(module, name, final_cpu):
    with tempfile.TemporaryDirectory(prefix='r6-monitor-eof-') as temp:
        out=Path(temp)
        root=out/'cgroups'
        (root/'r6-fixture.scope').mkdir(parents=True)
        proc_cgroup=out/'proc-cgroup'
        proc_cgroup.write_text('0::/r6-fixture.scope\n')
        spec={'run':str(out),'stage':name,'records':str(out),'argv':['/unused'],
              'wall_seconds':150,'cpu_seconds':.008,'memory_bytes':192*1024**2,
              'output_bytes':128*1024,'capture_events':True}
        spec_path=out/'command.json'
        r6.write_json(spec_path,spec)
        pipes=[]
        for _ in range(2):
            reader,writer=os.pipe()
            os.close(writer)
            pipes.append(os.fdopen(reader,'rb'))
        child=SimpleNamespace(stdout=pipes[0],stderr=pipes[1],poll=lambda:0,wait=lambda:0)
        original_read=Path.read_text

        def path(value):
            return {'/sys/fs/cgroup':root,'/proc/self/cgroup':proc_cgroup}.get(str(value),Path(value))

        def read(p,*args,**kwargs):
            if p.is_relative_to(root):
                if p.name=='cpu.stat':
                    used=final_cpu if all(pipe.closed for pipe in pipes) else 0
                    return f'usage_usec {used}\n'
                if p.name=='memory.events': return 'oom_kill 0\n'
                if p.name=='memory.peak': return '4096\n'
                if p.name=='cgroup.events': return 'populated 0\n'
            return original_read(p,*args,**kwargs)

        try:
            with patch.object(module,'Path',path), patch.object(Path,'read_text',read), \
                 patch.object(module.subprocess,'Popen',return_value=child):
                status=module.main(str(spec_path))
        finally:
            for pipe in pipes: pipe.close()
        stats=r6.read_json(out/f'{name}.process.json')
        limits=[row['payload'] for row in events.read(out/'events.ndjson') if row['event']=='resource_limit']
        return {'case':name,'monitor_exit_code':status,'process':stats,'resource_limit_events':limits}


results=[trial(supervise,'below_budget_at_eof',7000),
         trial(supervise,'at_budget_at_eof',8000),
         trial(supervise,'over_budget_at_eof',9000)]
# Demonstrate that this exact controlled race exposes the archived implementation.
old_path=r6.ROOT/'runs/golden-broker-v1/provenance/harness/supervise.py'
spec=importlib.util.spec_from_file_location('archived_supervise',old_path)
old=importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
results.append(trial(old,'archived_over_budget_at_eof',9000))
print(json.dumps(results,indent=2))

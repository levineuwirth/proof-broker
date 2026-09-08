import ast
import copy
import json
from pathlib import Path
import shutil
import sys
import tempfile
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
import episode
import run as r6
import test_episode
from test_validation import Export

source=r6.ROOT/'runs/broker-conformance-v2'
tree=ast.parse((r6.ROOT/'test_episode.py').read_text())
functions={n.name:n for n in ast.walk(tree) if isinstance(n,ast.FunctionDef)}
results=[]
with tempfile.TemporaryDirectory(prefix='r6-stage-probe-') as temp:
    temp=Path(temp)
    solution=temp/'solution.ndjson'
    r6.unpack(r6.ROOT/'runs/golden-broker-v1/solution.ndjson.gz',solution)
    original=Export(solution)
    for kind,name,category in [
        ('cert_case','valid_certificate','supervisor_failure'),
        ('proof_case','broker_proof_local','stage_rejected'),
        ('proof_case','broker_proof_local','supervisor_failure'),
        ('cert_case','invalid_witness','resource_exhaustion'),
    ]:
        out=temp/(kind+'-'+name+'-'+category)
        out.mkdir()
        records=[]
        def record(name,expected,observed):
            if expected != observed: raise AssertionError('Observation mismatch')
            records.append(name)
        def failed_stage(run,stage,*args,**kwargs):
            target=run/'stages'/stage
            shutil.copytree(source/'stages'/name,target)
            stats=r6.read_json(target/f'{stage}.process.json')
            if category=='stage_rejected': stats['exit_code']=7
            if category=='supervisor_failure': stats['monitor_error']='injected monitor failure'
            if category=='resource_exhaustion': stats['resource_exhausted']='cpu_time'
            r6.write_json(target/f'{stage}.process.json',stats)
            raise episode.StageFailure(stage,category,'injected post-verdict failure',stats)
        namespace={**vars(test_episode),'out':out,'record':record,'original':original,
                   'verifier':Path('/unused'),'checker':Path('/unused'),'challenge':solution}
        exec(compile(ast.Module(body=[functions[kind]],type_ignores=[]),'<actual-case-function>','exec'),namespace)
        try:
            with patch.object(episode,'stage',failed_stage):
                if kind=='cert_case':
                    packet=r6.read_json(r6.ROOT/'runs/golden-broker-v1/evidence.json')
                    namespace[kind](name,packet,'certificate_verification',name=='valid_certificate')
                else:
                    namespace[kind](name,lambda _:None,episode.local_policy(r6.D1),'complete',True)
            counted=bool(records)
            error=None
        except Exception as exc:
            counted=False
            error=str(exc)
        results.append({'case':name,'injected_failure':category,'counted_as_pass':counted,'error':error})
print(json.dumps(results,indent=2))

import copy
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
import episode
import events
import run as r6

source = r6.ROOT/'runs/golden-broker-v1'
base = r6.read_json(source/'seal.json')
results = []

def trial(name, edit):
    with tempfile.TemporaryDirectory(prefix='r6-audit-probe-') as temp:
        out=Path(temp)
        for item in base['retained_sha256']:
            p=out/item
            p.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(source/item,p)
        rows=events.read(out/'events.ndjson')
        verdict=r6.read_json(out/'verdict.json')
        edit(out,rows,verdict)
        r6.write_json(out/'verdict.json',verdict)
        rows[-1]['payload']['verdict_sha256']=r6.sha(out/'verdict.json')
        previous=events.ZERO
        for i,row in enumerate(rows):
            row.pop('event_hash')
            row['sequence']=i
            row['previous_hash']=previous
            previous=events.digest(row)
            row['event_hash']=previous
        (out/'events.ndjson').write_bytes(b''.join(events.canonical(r)+b'\n' for r in rows))
        seal=copy.deepcopy(base)
        seal['event_count']=len(rows)
        seal['last_event_hash']=rows[-1]['event_hash']
        seal['retained_sha256']={n:r6.sha(out/n) for n in seal['retained_sha256']}
        r6.write_json(out/'seal.json',seal)
        try:
            episode.audit(out)
            accepted=True
            error=None
        except Exception as exc:
            accepted=False
            error=str(exc)
        results.append({'case':name,'audit_accepted':accepted,'error':error})

trial('wrong_recovery_branch',lambda out,rows,v:v.update(recovery_route='exact_support_bounded'))
trial('negative_certificate_verdict',lambda out,rows,v:v['certificate_validation'].update(accepted=False))
trial('missing_kernel_targets',lambda out,rows,v:v['final_validation']['local'].update(targets=[]))
trial('wrong_solution_hash',lambda out,rows,v:v.update(solution_sha256='0'*64))
trial('resource_error_in_verdict',lambda out,rows,v:v['resources']['search'].update(monitor_error='injected'))
trial('missing_independent_check_event',lambda out,rows,v:rows.__setitem__(slice(None),[r for r in rows if r['event']!='independent_certificate_verdict']))
trial('changed_source',lambda out,rows,v:(out/'input/Frozen.lean').write_text((out/'input/Frozen.lean').read_text().replace('(2:ℕ)^24 + 2 * Zmax ≤ P','(2:ℕ)^23 + 2 * Zmax ≤ P',1)))
trial('missing_recovery_start',lambda out,rows,v:rows.__setitem__(slice(None),[r for r in rows if r['event']!='recovery_started']))
print(json.dumps(results,indent=2))

#!/usr/bin/env python3
"""Retained-byte recount for the R6-013 review; no native execution."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import cohort_budget
import events
import site_task

def sha(data): return hashlib.sha256(data).hexdigest()
def read(path): return json.loads(path.read_bytes())

def differences(a, b, path=''):
    if a == b: return []
    if isinstance(a, dict) and isinstance(b, dict) and a.keys() == b.keys():
        return [p for k in a for p in differences(a[k], b[k], path+'/'+k)]
    if isinstance(a, list) and isinstance(b, list) and len(a) == len(b):
        return [p for i, (x, y) in enumerate(zip(a, b)) for p in differences(x, y, path+'/'+str(i))]
    return [path]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite')
    site_task.register_primary()
    result = {}
    for revision, count in [('v4', 13), ('v5', 16), ('v6', 16)]:
        runs = sorted(p for p in (ROOT/('cohort-runs-'+revision)).iterdir() if p.is_dir())
        assert len(runs) == count
        totals = dict(runs=count, events=0, sealed_entries=0, proofs=0, certificate_accepted=0)
        for run in runs:
            rows = events.read(run/'events.ndjson'); seal = read(run/'seal.json')
            assert seal['event_count'] == len(rows) and seal['last_event_hash'] == rows[-1]['event_hash']
            for name, digest in seal['retained_sha256'].items(): assert sha((run/name).read_bytes()) == digest, (run, name)
            totals['events'] += len(rows); totals['sealed_entries'] += len(seal['retained_sha256'])
            totals['proofs'] += (run/'verdict.json').exists()
            if (run/'certificate-verdict.json').exists():
                totals['certificate_accepted'] += read(run/'certificate-verdict.json')['accepted'] is True
        result[revision] = totals
    exports = {}
    for name in ['l069-draw1', 'l070-draw1', 'l071-draw1', 'l078-draw1', 'l096-draw1', 'l099-draw1']:
        old, new = [ROOT/('cohort-runs-'+v)/name for v in ['v5', 'v6']]
        data = (new/'solution.ndjson.gz').read_bytes()
        assert data == (old/'solution.ndjson.gz').read_bytes()
        v = read(new/'verdict.json'); prior = read(old/'verdict.json')
        assert v['axiom_delta'] == prior['axiom_delta'] and all(x == {'added': [], 'removed': []} for x in v['axiom_delta'].values())
        digest = sha(gzip.decompress(data)); assert digest == v['solution_sha256'] == prior['solution_sha256']
        exports[name] = dict(compressed_sha256=sha(data), export_sha256=digest, closer=v['closer'])
    result['proof_exports_v5_v6_identical'] = exports
    same = []; request_changes = {}
    for name in site_task.primary():
        old, new = [ROOT/'census-runs'/('representability-'+v)/name for v in ['v3', 'v4']]
        for f in ['input-ir.json', 'stages/preparation/output/reification.json', 'stages/preparation/output/context.json', 'prepared.json']:
            assert (old/f).exists() == (new/f).exists()
            if (old/f).exists(): assert (old/f).read_bytes() == (new/f).read_bytes(), (name, f)
        same.append(name)
        if name in ['bracket-l096', 'bracket-l099', 'bracket-l166', 'bracket-l170', 'bracket-l175', 'bracket-l204']:
            requests = [json.loads(cohort_budget.request(site_task.get(name), read(ROOT/'census-runs'/('representability-'+v)/name/'prepared.json'))[0]) for v in ['v2', 'v4']]
            request_changes[name] = differences(*requests)
    result['preparation_v3_v4_identical'] = same
    result['request_differing_fields_v2_v4'] = request_changes
    result['program_sha256'] = sha(Path(__file__).read_bytes())
    result['scope'] = 'retained-byte recomputation; no native or provider execution'
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ['v4', 'v5', 'v6']}, indent=2))

if __name__ == '__main__': main()

#!/usr/bin/env python3
"""Read-only inventory, source, retention and census checks for the 007 review."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parents[1]


def sha(raw): return hashlib.sha256(raw).hexdigest()
def read(p): return json.loads(p.read_bytes())
def git(*argv, cwd=REPO):
    return subprocess.run(['git', *argv], cwd=cwd, capture_output=True, check=True).stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--before', type=Path, required=True)
    parser.add_argument('--verinf-repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite')
    before = read(args.before)
    changed = [n for n,h in before.items() if not (REPO/n).is_file() or sha((REPO/n).read_bytes()) != h]
    assert not changed, changed
    run = ROOT/'pilot-runs/live-2'
    sources = read(run/'provenance/sources.json')
    for name, record in sources.items():
        assert sha(git('cat-file', 'blob', 'e627efe:'+name)) == record['base_sha256'], name
        relative = 'bridge/'+name[len('lean-bridge/'):] if name.startswith('lean-bridge/') else name
        overlay = ROOT/'.cache/proposal-instrumented'/relative
        assert sha(overlay.read_bytes()) == record['instrumented_sha256'], name
    binaries = read(run/'provenance/binaries.json')
    assert all(sha(Path(p).read_bytes()) == h for p,h in binaries.items())
    selected = [REPO/p.decode() for p in git('ls-files', '--cached', '--others', '--exclude-standard', '-z',
                '--', 'experiments/r6/pilot-runs').split(b'\0') if p]
    info = {p:(p.stat().st_size, sha(p.read_bytes())) for p in selected}
    def stats(ps):
        vals = [info[p] for p in ps]; unique = {h:n for n,h in vals}
        return {'files':len(vals), 'apparent_bytes':sum(n for n,h in vals),
                'unique_blobs':len(unique), 'unique_bytes':sum(unique.values())}
    all_six = stats(selected)
    three = stats([p for p in selected if p.relative_to(ROOT/'pilot-runs').parts[0] in ('live-1','live-2','rehearsal-4')])
    missing_required = {}
    for path in (ROOT/'pilot-runs').glob('*/seal.json'):
        wanted = set(read(path)['retained_sha256'])
        actual = {str(p.relative_to(path.parent)) for p in selected if p.is_relative_to(path.parent)}
        missing_required[path.parent.name] = sorted(wanted-actual)
    assert not any(missing_required.values())
    commit = 'c07e03c94884e9084ffaf7a7294fc0907672f6c2'
    path = 'lean/BracketSpike/BracketSpike/Bracket.lean'
    raw = git('cat-file','blob',commit+':'+path,cwd=args.verinf_repo)
    assert raw == (ROOT/'tasks/verinf-d1-70/Pristine.lean').read_bytes()
    sites = [{'line':i+1,'text':s.strip()} for i,s in enumerate(raw.decode().splitlines()) if re.search(r'\bomega\b',s)]
    assert len(sites) == 15
    proof_hashes = {name:read(ROOT/'runs'/name/'verdict.json')['solution_sha256'] for name in
                   ('golden-broker-v1','golden-broker-v2','golden-broker-v3','provider-checkpoint-v1/d1_valid')}
    result = {'passed':True, 'program_sha256':sha(Path(__file__).read_bytes()),
        'preservation':{'before_sha256':sha(args.before.read_bytes()),'files':len(before),'changed':changed},
        'source_binding':{'sdk_bridge_sources':len(sources),'git_base':'e627efe','commit_mismatches':0,
                          'current_overlay_mismatches':0,'recorded_binaries':len(binaries),'binary_mismatches':0},
        'retention':{'git_selected_all_six':all_six, 'git_selected_proposed_three':three,
                     'incremental_unique_bytes':all_six['unique_bytes']-three['unique_bytes'],
                     'ignored_required_paths':missing_required,'scope':'current Git selection; unique uncompressed blobs, not packed Git size'},
        'census':{'commit':commit,'path':path,'sha256':sha(raw),'pristine_matches':True,'sites':sites,
                  'scope':'15 textual omega occurrences, manually inspected as tactics; no extraction or admission attempted'},
        'comparison_proof_hashes':proof_hashes, 'live_model_calls':0,'credential_reads':0}
    args.output.write_text(json.dumps(result,sort_keys=True,indent=1)+'\n')
    print(json.dumps({'passed':True,'preserved':len(before),'census':len(sites),'incremental_unique_bytes':result['retention']['incremental_unique_bytes']}))


if __name__ == '__main__': main()

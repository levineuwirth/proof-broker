#!/usr/bin/env python3
"""R6-013 auditor revision 2: carried probes and additional boundary probes on copies."""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('v6_v2_controls_review', ROOT/'reviews/2026-09-22/cohort_v6_audit_controls.py')
c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
ADDITIONAL = ('refused_reconstruction_helper_changed', 'refused_reconstruction_source_changed', 'library_source_escapes_system_directory',
              'replay_challenge_unverified_location')
CASES = (*c.REVIEW_PROBES, *ADDITIONAL)

def mutate(name, paths):
    if name in c.REVIEW_PROBES:
        c.mutate(name, paths); return
    if name.startswith('refused_reconstruction_'):
        def change(run, rows):
            if name == 'refused_reconstruction_helper_changed':
                p = run/'input/ProposalCapture.lean'; s = p.read_text()
                old = 'evalTactic (← `(tactic| proof_broker_term [$adapter:ident]))'
                assert s.count(old) == 1
                p.write_text(s.replace(old, 'evalTactic (← `(tactic| omega))'))
            else:
                p = run/'input/Frozen.lean'; other = paths['runs']/c.NAT/'input/Frozen.lean'
                assert p.read_bytes() != other.read_bytes()
                p.write_bytes(other.read_bytes())
        c.refinalize(paths['runs']/c.REF, change)
    elif name == 'library_source_escapes_system_directory':
        changed = 0
        for run in sorted(paths['runs'].iterdir()):
            if not (run/'stages/reconstruct').is_dir(): continue
            def change(run, rows):
                def command(v):
                    argv = v['argv']; i = len(c.audit.SANDBOX)+12
                    assert argv[i:i+3] == ['--ro-bind', '/usr/lib/libc.so.6', '/usr/lib/libc.so.6']
                    argv[i:i] = ['--ro-bind', '/usr/lib/../../etc/hostname', '/usr/lib/review-extra-data']
                c.change_json(run, 'stages/reconstruct/command.json', command)
            c.refinalize(run, change); changed += 1
        assert changed == 10
    elif name == 'replay_challenge_unverified_location':
        def change(run, rows):
            for stage in ('validation-local', 'validation-whole'):
                def command(v):
                    argv=v['argv']; i=argv.index('/challenge.ndjson'); assert argv[i-2]=='--ro-bind'
                    assert argv[i-1] != '/etc/r6-campaign-challenge-review/challenge.ndjson'
                    argv[i-1]='/etc/r6-campaign-challenge-review/challenge.ndjson'
                c.change_json(run, 'stages/'+stage+'/command.json', command)
        c.refinalize(paths['runs']/c.NAT, change)
    else: raise AssertionError(name)

def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('--output',type=Path,required=True); args=parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite')
    results={}
    for name in CASES:
        with tempfile.TemporaryDirectory(prefix='r6-013-v2-review-') as tmp:
            tmp=Path(tmp); paths={k:tmp/k for k in ('runs','ledgers','representability','v4','v5')}
            sources={'runs':ROOT/c.audit.RUNS,'ledgers':ROOT/'ledgers/campaigns','representability':ROOT/c.audit.REPRESENTABILITY,
                     'v4':ROOT/c.audit.HISTORY_V4['runs'],'v5':ROOT/c.audit.HISTORY_V5['runs']}
            for k,p in sources.items(): shutil.copytree(p,paths[k])
            baseline=c.run_audit(paths); assert baseline['accepted'] is True and baseline['case_count']==655,baseline
            mutate(name,paths); observed=c.run_audit(paths)
            if name in c.REVIEW_PROBES: assert observed['accepted'] is False and observed['rejected_case']==c.EXPECTED[name],observed
            results[name]={'unmutated_copy_accepted':True,**observed}; print(name,json.dumps(observed),flush=True)
    assert tuple(results)==CASES
    args.output.write_text(json.dumps({'complete':True,'expected_cases':list(CASES),'results':results,
        'auditor_sha256':c.r6.sha(ROOT/'reviews/2026-09-22/cohort_v6_audit.py'),'program_sha256':c.r6.sha(Path(__file__)),
        'scope':'temporary copies; full 655-case audit before each mutation; auditor invokes build_tools; no episode, credential or provider execution'},indent=2)+'\n')

if __name__=='__main__': main()

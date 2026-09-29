#!/usr/bin/env python3
"""Copied census corruptions against the eleven non-native production controls.

The native exclusion is explicitly skipped, never counted as passed. No
production source or original artifact is modified; accepted corruptions are
findings, not conformance successes.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import census
import site_freeze as freeze
import test_census as tests

J = lambda p: json.loads(Path(p).read_bytes())
W = lambda p,v: Path(p).write_text(json.dumps(v,sort_keys=True,indent=2)+'\n')
SHA = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
SKIP = 'exclusion_records_failing_stage_and_stderr'
CASES = ('wrong_challenge_export', 'false_local_type', 'missing_required_artifact_binding')


class NonNativeSuite:
    def __init__(self, output, expected):
        self.results = []; self.expected = tuple(n for n in expected if n != SKIP); self.skipped = []
    def case(self, name, fn):
        if name == SKIP: self.skipped.append(name); return
        assert name not in self.results
        fn(); self.results.append(name)
    def finish(self):
        assert tuple(self.results) == self.expected and self.skipped == [SKIP]


def check(directory):
    try:
        with patch.object(freeze,'CENSUS_DIR',directory), patch.object(tests,'Suite',NonNativeSuite):
            suite = tests.controls(None)
    except Exception as e:
        return {'accepted':False,'error':type(e).__name__+': '+str(e)}
    return {'accepted':True,'checked_names':suite.results,'skipped_names':suite.skipped}


def mutate(directory, name):
    d=directory/'bracket-l069'; m=J(d/'manifest.json'); c=J(directory/'census.json'); expected=J(d/'expected.json')
    if name == 'wrong_challenge_export':
        original=SHA(d/'challenge.ndjson.gz')
        shutil.copyfile(directory/'bracket-l099/challenge.ndjson.gz', d/'challenge.ndjson.gz')
        assert SHA(d/'challenge.ndjson.gz') != original
        m['artifacts_sha256']['challenge.ndjson.gz']=SHA(d/'challenge.ndjson.gz')
    elif name == 'false_local_type':
        t=expected['targets'][0]; assert t['type_sha256'] != '0'*64; t['type_sha256']='0'*64
        next(r for r in c['results'] if r['site_id']=='bracket-l069')['local_type_sha256']='0'*64
        W(d/'expected.json',expected); m['artifacts_sha256']['expected.json']=SHA(d/'expected.json')
        W(directory/'census.json',c)
    elif name == 'missing_required_artifact_binding':
        del m['artifacts_sha256']['challenge.ndjson.gz']
        # Keep the schema's minimum property count while removing a required semantic member.
        m['artifacts_sha256']['context/../expected.json']=SHA(d/'expected.json')
    else: raise AssertionError(name)
    W(d/'manifest.json',m)
    membership=J(directory/'membership.json')
    membership['census_sha256']=SHA(directory/'census.json')
    membership['manifests_sha256']['bracket-l069']=SHA(d/'manifest.json')
    W(directory/'membership.json',membership)


def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--output',type=Path,required=True); args=p.parse_args()
    assert not args.output.exists(); result={'complete':False,'reviewed_commit':'51dd7ab','results':{},'expected_cases':list(CASES),
      'scope':'eleven non-native production controls on copies; native exclusion separately rerun on original frozen census',
      'program_sha256':SHA(Path(__file__)),'test_census_sha256':SHA(ROOT/'test_census.py'),'live_model_calls':0,'real_credentials_read':0}
    W(args.output,result)
    for name in CASES:
        with tempfile.TemporaryDirectory(prefix='r6-010-probe-') as temp:
            directory=Path(temp)/'census'; shutil.copytree(freeze.CENSUS_DIR,directory)
            baseline=check(directory); assert baseline['accepted'] is True,baseline
            mutate(directory,name); observed=check(directory)
            result['results'][name]={'unmutated':baseline,'mutated':observed}
            W(args.output,result); print(name,observed['accepted'],flush=True)
    assert tuple(result['results'])==CASES
    result['complete']=True; W(args.output,result)


if __name__=='__main__': main()

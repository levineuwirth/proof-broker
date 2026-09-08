#!/usr/bin/env python3
"""Remove or substitute recorded checks; a partial suite must never publish success.

Uses results of a real passing suite and its actual finalization function.
Does not rerun search, certificate verification, or kernel replay.
"""
import argparse
import copy
from pathlib import Path
import shutil
import time

import events
import run as r6
import test_episode


def mutants(rows):
    for i, row in enumerate(rows):
        yield 'missing_'+row['case'], rows[:i]+rows[i+1:], 'missing='
    yield 'duplicate_replacing_missing', [rows[1], *rows[1:]], 'duplicates='
    yield 'extra_duplicate', [*rows, rows[0]], 'duplicates='
    unexpected=copy.deepcopy(rows)
    unexpected.append({**rows[0], 'case':'unexpected_case'})
    yield 'unexpected_case', unexpected, "unexpected=['unexpected_case']"
    failed=copy.deepcopy(rows)
    failed[0]['passed']=False
    yield 'failed_check', failed, 'failed='


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite',type=Path,default=r6.ROOT/'runs/broker-conformance-v2')
    parser.add_argument('--run-dir',type=Path)
    args=parser.parse_args()
    source=args.suite.resolve()/'tests.json'
    suite=r6.read_json(source)
    if suite['passed'] is not True:
        raise AssertionError('The source suite must have passed')
    test_episode.require_complete_suite(suite['checks'])
    if r6.sha(r6.ROOT/'test_episode.py') != suite['artifact_sha256']['provenance/test_episode.py']:
        raise AssertionError('Completion code differs from the source suite')
    out=(args.run_dir or r6.ROOT/'runs'/f'suite-completion-{time.time_ns()}').resolve()
    out.mkdir(parents=True,exist_ok=False)
    provenance=out/'provenance'
    provenance.mkdir()
    for name in ['test_suite_completion.py','test_episode.py']:
        shutil.copyfile(r6.ROOT/name,provenance/name)
    expected_mutations={'missing_'+name for name in test_episode.EXPECTED_CASES} | {
        'duplicate_replacing_missing','extra_duplicate','unexpected_case','failed_check'}
    report={'source_suite':str(source), 'source_suite_sha256':r6.sha(source),
            'test_source_sha256':r6.sha(Path(__file__)),
            'completion_source_sha256':r6.sha(r6.ROOT/'test_episode.py'),
            'expected_mutations':sorted(expected_mutations), 'passed':False, 'checks':[]}
    r6.write_json(out/'tests.json',report)
    for name, rows, expected_error in mutants(suite['checks']):
        trial=out/name
        trial.mkdir()
        r6.write_json(trial/'tests.json',{'passed':False,'checks':rows})
        try:
            test_episode.finish_suite(trial,Path(suite['source_episode']),rows)
        except AssertionError as error:
            message=str(error)
            if not message.startswith('Incomplete conformance suite:') or expected_error not in message:
                raise
        else:
            raise AssertionError(f'{name}: incomplete suite published success')
        if r6.read_json(trial/'tests.json')['passed'] is not False:
            raise AssertionError(f'{name}: failure marker was overwritten')
        log=trial/'events.ndjson'
        if log.exists() and any(row['event']=='tests_finished' for row in events.read(log)):
            raise AssertionError(f'{name}: completion event was emitted')
        report['checks'].append({'case':name,'rejected':True,'error':message,
            'failure_marker_preserved':True,'completion_event_absent':True})
        r6.write_json(out/'tests.json',report)
    names=[row['case'] for row in report['checks']]
    if set(names) != expected_mutations or len(names) != len(expected_mutations):
        raise AssertionError('Completion mutation checks are incomplete or duplicated')
    report['passed']=True
    r6.write_json(out/'tests.json',report)
    print(f'{len(report["checks"])} incomplete-suite mutations rejected: {out}/tests.json')


if __name__=='__main__':
    main()

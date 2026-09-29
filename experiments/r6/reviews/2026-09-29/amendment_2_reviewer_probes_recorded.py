#!/usr/bin/env python3
"""The amendment 2 review's probes (`amendment_2_review_probes.py`, retained as the reviewer left it), reproduced against the revised auditor
(amendment 2, revision 2) and runner (revision 7), with their outcomes recorded here instead of in /tmp. SYNTHETIC only: the runner's sender
and ledger are mocked for the restart probes; the transport probes regenerate the synthetic fixture with the unchanged generator and the
production ledger in a temporary directory. No collected run or credential is read; nothing is sent.

Expected under the revision:
* restart: the review's baseline (release, sent retry) gates both attempts and launches only the next site; the extra attempt after the sent
  retry, the missing first attempt and the later incomplete run after a gap each stop before any sender invocation;
* transport: each of the review's three single-field contradictions is rejected by the auditor at `l096-draw2:failure:classified_and_finalized`
  and paused by the runner's gate on the pre-grant reason.
"""
import argparse
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent; R6 = HERE.parents[1]
sys.path.insert(0, str(R6))
import run as r6

def mod(name, path):
    s = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(s); s.loader.exec_module(m); return m

C = mod('reviewer_probes_runner_controls', R6/'reviews/2026-09-24/block2_runner_controls.py'); m = C.m
A = mod('reviewer_probes_amendment_controls', R6/'reviews/2026-09-28/cohort_v9_audit_amended_2_controls.py')
RESTART = {'baseline': ('launch', ['l070-draw2']), 'extra_attempt_after_sent': ('paused', []), 'gap_before_existing_retry': ('paused', []),
           'later_existing_bad_run': ('paused', [])}
TRANSPORT = [('body_sends_returned', 1), ('header_send_at_ns', 12345), ('tls_verified_at_ns', 12345)]


def restart(name):
    with tempfile.TemporaryDirectory(prefix='r6-a2-reviewer-runner-') as tmp:
        root = Path(tmp); runs = root/'runs'; runs.mkdir()
        first = runs/'l096-draw2'; second = runs/'l096-draw2-attempt2'
        C.build('release_is_retried', 'l096', first)
        view = C.build('_sent_retry', 'l096', second)
        if name == 'extra_attempt_after_sent': shutil.copytree(second, runs/'l096-draw2-attempt3')
        if name == 'gap_before_existing_retry': shutil.rmtree(first)
        if name == 'later_existing_bad_run': (runs/'l166-draw2').mkdir()
        launches = []; checked = []; original = m.gate
        def gate(run, *args): checked.append(run.name); return original(run, *args)
        def send(argv, **kwargs): launches.append(Path(argv[argv.index('--run-dir')+1]).name); raise C.NextLaunch()
        with patch.object(m, 'RUNS', runs), patch.object(m, 'ORDER', ('l096', 'l070', 'l166')), patch.object(m, 'DRAWS', (2,)), \
             patch.object(m, 'ledger_snapshot', lambda: view), patch.object(m, 'gate', gate), \
             patch.object(m, 'subprocess', SimpleNamespace(run=send)), patch.object(m.time, 'sleep', lambda _: None), \
             patch.object(sys, 'argv', ['runner', '--credential-file', str(root/'never-exists')]), contextlib.redirect_stdout(io.StringIO()):
            stop = None
            try: m.main(); outcome = 'completed'
            except C.NextLaunch: outcome = 'launch'
            except SystemExit as e: stop = str(e); outcome = 'paused' if stop.startswith('PAUSE') else stop
        return {'outcome': outcome, 'checked': checked, 'launches': launches, 'stop': stop}


def transport(field, value):
    original = A.change_source
    def change(name, run):
        original('regenerated_baseline', run)
        p = run/'stages/proposal-1/output/http.json'; h = C.J(p); h[field] = value; C.W(p, h)
    with tempfile.TemporaryDirectory(prefix='.r6-a2-reviewer-transport-', dir=R6/'fixtures') as tmp, patch.object(A, 'change_source', change):
        f, generated = A.regenerate(Path(tmp), 'regenerated_baseline')
        audit = A.audit_at(f, A.amended2)
        policy = C.J(f/'policies/farkas-cohort-v9.json'); campaign = policy['campaign']['id']
        raw, state = C.ledger.Ledger(f/'ledgers/campaigns'/campaign/'live', campaign).snapshot()
        with patch.object(m, 'ledger_snapshot', lambda: (C.ledger.parse(raw), state)):
            decision = m.gate(f/'runs/l096-draw2', 'bracket-l096', 2)
        return {'value': value, 'audit': audit, 'runner': decision, **generated}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    out = {'restart': {}, 'transport': {}}
    for name, (expected, launches) in RESTART.items():
        got = restart(name); assert got['outcome'] == expected and got['launches'] == launches, (name, got)
        out['restart'][name] = got; print('restart', name, got, flush=True)
    for field, value in TRANSPORT:
        got = transport(field, value)
        assert got['ledger_reconciled_release_as'] == 'release' and got['audit']['accepted'] is False
        assert got['audit']['rejected_case'] == 'l096-draw2:failure:classified_and_finalized', (field, got)
        assert got['runner'][0] == 'pause' and got['runner'][2] == [C.PRE_GRANT_REASON], (field, got)
        out['transport'][field] = got; print('transport', field, got['audit']['rejected_case'], got['runner'], flush=True)
    r6.write_json(args.output, {'passed': True, **out, 'review_probes_sha256': r6.sha(HERE/'amendment_2_review_probes.py'),
                                'auditor_sha256': r6.sha(R6/'reviews/2026-09-28/cohort_v9_audit_amended_2.py'), 'runner_sha256': r6.sha(R6/'reviews/2026-09-24/run_block2.py'),
                                'program_sha256': r6.sha(Path(__file__)), 'transmissions': 0, 'credentials_read': 0, 'collected_block_read': False})
    print(json.dumps({'passed': True, 'restart': len(out['restart']), 'transport': len(out['transport'])}))


if __name__ == '__main__':
    main()

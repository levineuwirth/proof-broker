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
R6 = Path('/home/jeans/Repos/research/proof-broker/experiments/r6')
def mod(name, path):
    s = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
C = mod('review_runner_controls', R6/'reviews/2026-09-24/block2_runner_controls.py')
m = C.m
result = {'controls': {}, 'restart': {}, 'transport': {}}
for name, (site, expected) in C.CASES.items():
    for mode in ('fresh', 'restart'):
        got = C.exercise(name, site, mode)
        assert got['observed'] == expected, (name, mode, got)
        result['controls'][name+':'+mode] = got
print('runner controls', len(result['controls']), flush=True)

for name in ('baseline', 'extra_attempt_after_sent', 'gap_before_existing_retry', 'later_existing_bad_run'):
    with tempfile.TemporaryDirectory(prefix='r6-a2-review-runner-') as tmp:
        root = Path(tmp); runs = root/'runs'; runs.mkdir()
        first = runs/'l096-draw2'; second = runs/'l096-draw2-attempt2'
        C.build('release_is_retried', 'l096', first)
        view = C.build('_sent_retry', 'l096', second)
        if name == 'extra_attempt_after_sent': shutil.copytree(second, runs/'l096-draw2-attempt3')
        if name == 'gap_before_existing_retry': shutil.rmtree(first)
        if name == 'later_existing_bad_run': (runs/'l166-draw2').mkdir()
        launches = []; checked = []; log = io.StringIO()
        original = m.gate
        def gate(run, *args):
            checked.append(run.name); return original(run, *args)
        def send(argv, **kwargs):
            launches.append(Path(argv[argv.index('--run-dir')+1]).name); raise C.NextLaunch()
        with patch.object(m, 'RUNS', runs), patch.object(m, 'ORDER', ('l096', 'l070', 'l166')), patch.object(m, 'DRAWS', (2,)), \
             patch.object(m, 'ledger_snapshot', lambda: view), patch.object(m, 'gate', gate), \
             patch.object(m, 'subprocess', SimpleNamespace(run=send)), patch.object(m.time, 'sleep', lambda _: None), \
             patch.object(sys, 'argv', ['runner', '--credential-file', str(root/'never-exists')]), contextlib.redirect_stdout(log):
            try: m.main(); outcome = 'completed'
            except C.NextLaunch: outcome = 'launch_attempted'
            except SystemExit as e: outcome = str(e)
        result['restart'][name] = {'outcome': outcome, 'checked': checked, 'launches': launches}
        print(name, result['restart'][name], flush=True)

A = mod('review_amendment_controls', R6/'reviews/2026-09-28/cohort_v9_audit_amended_2_controls.py')
for field, value in [('body_sends_returned', 1), ('header_send_at_ns', 12345), ('tls_verified_at_ns', 12345)]:
    original = A.change_source
    def change(name, run):
        original('regenerated_baseline', run)
        p = run/'stages/proposal-1/output/http.json'; h = C.J(p); h[field] = value; C.W(p, h)
    with tempfile.TemporaryDirectory(prefix='.review-a2-transport-', dir=R6/'fixtures') as tmp, patch.object(A, 'change_source', change):
        f, generated = A.regenerate(Path(tmp), 'regenerated_baseline')
        audit = A.audit_at(f, A.amended2)
        policy = C.J(f/'policies/farkas-cohort-v9.json'); campaign = policy['campaign']['id']
        raw, state = C.ledger.Ledger(f/'ledgers/campaigns'/campaign/'live', campaign).snapshot()
        with patch.object(m, 'ledger_snapshot', lambda: (C.ledger.parse(raw), state)):
            decision = m.gate(f/'runs/l096-draw2', 'bracket-l096', 2)
        result['transport'][field] = {'value': value, 'audit': audit, 'runner': decision, **generated}
        print(field, result['transport'][field], flush=True)
Path('/tmp/r6-amendment2-independent-probes.json').write_text(json.dumps(result, indent=2)+'\n')

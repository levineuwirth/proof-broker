#!/usr/bin/env python3
"""R6-015 analysis: tests before the lock. Nothing is replayed and no closer runs.

1. `classify` against real bridge error lines: those the synthetic rehearsal produced, those the bridge tests pin
   (`lean-bridge/Test/TermModeConstrained.lean`), and R6-014's own retained refusal line.
2. `analyse` end to end on the real 108-episode plan, with stand-in verdicts, events and control records per scenario
   (monkeypatched lock, binding, events and axioms), against the frozen outcome definitions and controls.

Run: `python3 r6-015/test_analysis.py` (or under pytest).
"""
import copy
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import run as r6  # noqa: E402
import analysis  # noqa: E402
import replay_campaign  # noqa: E402
import replay_lock  # noqa: E402

LINE = 'Frozen.lean:12:4: error: '
CASES = [  # (error line, expected stage, expected detail)
    ('proof_broker_term (constrained): the weighted sum does not cancel; its normal form is -1 * (↑n^1) + 7', 'constrained_final_step', 'does not cancel'),
    ('proof_broker_term (constrained): the weighted sum normalizes to 0, which is not positive', 'constrained_final_step', 'not positive'),
    ('proof_broker_term (constrained): the positivity proof reaches hypotheses [tag]', 'constrained_final_step', 'reaches hypotheses'),
    ('proof_broker_term (constrained): the kernel rejected the positivity proof: (kernel) declaration type mismatch', 'constrained_final_step', 'kernel rejected the step'),
    ("proof_broker_term: witness names hypothesis 'nope' which is not in scope", 'fact_assertion', 'name not in scope'),
    ("proof_broker_term: hypothesis 'h' has a shape the ℕ→ℤ lift cannot cast yet (x ∣ y)", 'fact_assertion', 'cast'),
    ("proof_broker_term: witness names _pb_nonneg_atom_9 but the extraction has no atom '_pb_atom_9'", 'fact_assertion', 'atom'),
    ('proof_broker_term (constrained): the extension fragment LRA is outside the constrained route (fail closed)', 'selection', 'outside the route'),
    ("proof_broker_term: hypothesis 'h' not in scope", 'fold', 'name not in scope'),
    ('proof_broker_term: hypothesis shape outside Int ≤/≥/</>/= (got type P; head ctor app)', 'fold', 'hypothesis shape'),
    ('R6 proposal input differs from freshly reified goal/context', 'packet_binding', 'input IR'),
    ('something else entirely', 'unclassified', 'no bridge error line'),
]


def test_classify():
    rehearsal = r6.read_json(R6/'reviews/2026-10-01/R6-015-HARNESS-REHEARSAL-SYNTHETIC.json')['results']
    refusal = r6.read_json(R6/'cohort-live-v9/l166-draw1/reconstruction-refusal.json')['error_line']
    real = [(rehearsal['invalid_injected']['errors'][0], 'constrained_final_step', 'does not cancel'),
            (rehearsal['invalid_checked']['errors'][0], 'bridge_gate', 'verifier'),
            (rehearsal['valid_pinned']['errors'][0], 'selection', 'goal shape'),
            (refusal, 'selection', 'goal shape')]
    for line, stage, detail in [(LINE + l, s, d) for l, s, d in CASES] + real:
        got = analysis.classify({'outcome': 'reconstruction_failed', 'detail': {'events': [], 'errors': [line]}})
        assert got[:2] == (stage, detail), (line, got)
    assert analysis.classify({'outcome': 'kernel_rejected', 'detail': 'x'})[0] == 'kernel'
    assert analysis.classify({'outcome': 'certificate_rejected'})[0] == 'checker'
    assert analysis.classify({'outcome': 'context_changed', 'detail': 'x'})[:2] == ('harness', 'context_changed')


PLAN = {s['id']: s for s in r6.read_json(HERE/'plan.json')['episodes']}
CERT = {'synthetic': True}
FROZEN = {'bridge_rev': 'B' * 40, 'instrumented_tactic_sha256': 'T' * 64, 'binaries_sha256': {'audit_tool': 'A' * 64},
          'python_sha256': {str(f.relative_to(R6)): 'P' * 64 for f in analysis.control3.SOURCES}}
PASSING_REPORT = {'exit': 0, 'audit': {'binding': 'matches_residual', 'local': {'locatable': True, 'hypotheses': []},
                                       'whole': {'locatable': True, 'hypotheses': []}}}
FAILS = {'reconstruction_failed'}


def digests(i):
    return {'seal_sha256': f'seal-{i}', 'verdict_sha256': f'verdict-{i}', 'solution_sha256': f'solution-{i}',
            'residual_sha256': f'residual-{i}', 'export_sha256': f'export-{i}'}


def failure(message):
    return {'outcome': 'reconstruction_failed', 'detail': {'events': [], 'errors': [LINE + message]}}


def scenario(fail=lambda i, s: None):
    """Stand-in evidence for every planned episode: everything as frozen, except where `fail` returns an override."""
    verdicts, observed = {}, {}
    for i, s in PLAN.items():
        site = s['site'].removeprefix('bracket-')
        nat = site in ('l069', 'l070', 'l071', 'l078')
        closer = 'term_mode_nat' if nat else 'term_mode_int'
        selected = ('closer_selected', {'closer': closer, 'comparison_type': 'ℕ' if nat else 'ℤ'})
        bypass = [('certificate_gate_bypassed', {'certificate': CERT})] if s['inject_unverified'] else []
        if site == 'l170' and not s['inject_unverified']:
            v = {'outcome': 'certificate_rejected', 'certificate_accepted': False}; ev = []
        elif s['inject_unverified']:
            message = ('proof_broker_term (constrained): the weighted sum normalizes to 0, which is not positive' if site == 'l170'
                       else 'proof_broker_term (constrained): the weighted sum does not cancel; x')
            v = {**failure(message), 'certificate_accepted': False}; ev = bypass + [selected]
        else:
            v = {'outcome': 'proved', 'certificate_accepted': True, 'closer': closer, 'final_step': 'constrained',
                 'local_validated': True, 'whole_validated': True, 'axiom_delta': {}}
            ev = [selected]
        override = fail(i, s)
        if override: v = {**v, **override}
        verdicts[i] = v; observed[i] = ev
    return verdicts, observed, control8_for(verdicts), control3_record()


def control8_for(verdicts, report=PASSING_REPORT):
    results = {}
    for i, v in verdicts.items():
        d = digests(i)
        if v['outcome'] == 'proved':
            results[i] = {'bound': True, 'outcome': 'proved', 'audited': True, 'unmet': [], 'report': copy.deepcopy(report),
                          'command': {'tool_sha256': FROZEN['binaries_sha256']['audit_tool'],
                                      'inputs': {'<tmp>/export.ndjson': {'sha256': d['export_sha256']},
                                                 '<tmp>/residual.txt': {'sha256': d['residual_sha256']}}},
                          **{k: d[k] for k in ('seal_sha256', 'verdict_sha256', 'solution_sha256', 'residual_sha256')}}
        else:
            results[i] = {'bound': True, 'outcome': v['outcome'], 'audited': False,
                          **{k: d[k] for k in ('seal_sha256', 'verdict_sha256')}}
    return {'schema_version': 'r6-015-control-8-1', 'passed': True, 'results': results}


def control3_record():
    results = {'checker': {'accepted': False},
               'constrained': {'exit': 1, 'events': ['certificate_gate_bypassed', 'term_route', 'closer_selected'],
                               'term_route': {'constrained': True}, 'closer_selected': {'closer': 'term_mode_int', 'route': 'constrained'},
                               'errors': [LINE + 'proof_broker_term (constrained): the weighted sum does not cancel; its normal form is x']},
               'pinned': {'exit': 0, 'events': ['certificate_gate_bypassed', 'term_route', 'closer_selected', 'reconstruction_finished'],
                          'term_route': {'constrained': False}, 'reconstruction_finished': {'residual_closer': 'omega'}, 'errors': []}}
    return {'schema_version': analysis.control3.SCHEMA, 'control': 3, 'passed': True, 'unmet': [], 'results': results,
            'evidence': {'coefficients': analysis.control3.PROBE}, 'bridge_rev': FROZEN['bridge_rev'],
            'instrumented_tactic_sha256': FROZEN['instrumented_tactic_sha256'],
            'sources_sha256': {k: v for k, v in FROZEN['python_sha256'].items()}}


def run_analysis(verdicts, observed, c8, c3):
    saved = (replay_lock.verify_lock, replay_lock.planned, replay_lock.LOCK, replay_campaign.bound, analysis.reconstruct_events,
             analysis.axioms, analysis.packet_certificate, analysis.current)
    with tempfile.TemporaryDirectory(prefix='r6-015-analysis-') as tmp:
        tmp = Path(tmp)
        lock = tmp/'lock.json'; lock.write_text('{"stand-in": true}\n'); sha = r6.sha(lock)
        c8 = {**c8, 'lock_sha256': c8.get('lock_sha256', sha)}; c3 = {**c3, 'lock_sha256': c3.get('lock_sha256', sha)}
        r6.write_json(tmp/'c8.json', c8); r6.write_json(tmp/'c3.json', c3)
        replay_lock.verify_lock = lambda: copy.deepcopy(FROZEN)
        replay_lock.planned = lambda frozen: copy.deepcopy(PLAN)
        replay_lock.LOCK = lock
        replay_campaign.bound = lambda run, spec, frozen, lock_sha: (None, verdicts[spec['id']])
        analysis.reconstruct_events = lambda run: observed[run.name]
        analysis.axioms = lambda run, verdict: True
        analysis.packet_certificate = lambda run: CERT
        analysis.current = lambda run, proved: {k: v for k, v in digests(run.name).items()
                                               if proved or k in ('seal_sha256', 'verdict_sha256')}
        try:
            return analysis.analyse(tmp/'runs', tmp/'c3.json', tmp/'c8.json')
        finally:
            (replay_lock.verify_lock, replay_lock.planned, replay_lock.LOCK, replay_campaign.bound, analysis.reconstruct_events,
             analysis.axioms, analysis.packet_certificate, analysis.current) = saved


def rejected(*args, needle):
    try:
        run_analysis(*args)
    except SystemExit as stop:
        assert needle in str(stop), str(stop)
        return
    raise AssertionError(f'accepted; expected a rejection mentioning {needle!r}')


def measured(i, s):
    return s['site'] in ('bracket-l166', 'bracket-l175', 'bracket-l178', 'bracket-l204') and s['coefficients'] is None and not s['inject_unverified']


def test_outcomes():
    a = run_analysis(*scenario())
    assert a['outcome'] == 'complete_success' and a['measurement']['consumed_and_validated'] == 36, a['outcome_reasons']
    assert all(a['controls'][c]['passed'] for c in ('control_1', 'control_2', 'control_3', 'control_4', 'control_5', 'control_6', 'control_8'))
    assert a['controls']['control_5']['expected_pass_met'] == a['controls']['control_5']['expected_pass'] == 10
    assert len(a['controls']['control_5']['diagnostic_only']) == 4
    assert len(a['measurement']['per_map']) == 6 and len(a['measurement']['per_class']) == 5

    fact = failure("proof_broker_term: witness names hypothesis 'hlt' which is not in scope")
    a = run_analysis(*scenario(lambda i, s: fact if measured(i, s) and s['site'] == 'bracket-l166' else None))
    assert a['outcome'] == 'partial' and a['measurement']['consumed_and_validated'] == 27
    assert a['measurement']['per_obligation']['l166']['learned'] == {'episodes': 8, 'consumed_and_validated': 0, 'stages': {'fact_assertion': 8}}
    assert run_analysis(*scenario(lambda i, s: fact if measured(i, s) else None))['outcome'] == 'none'
    a = run_analysis(*scenario(lambda i, s: fact if i == 'l204-learned-scaled_2' else None))
    assert a['controls']['control_2']['failures'] == ['l204-learned-scaled_2'] and a['outcome'] == 'partial'

    proved = {'outcome': 'proved', 'closer': 'term_mode_int', 'final_step': 'constrained', 'local_validated': True, 'whole_validated': True, 'axiom_delta': {}}
    a = run_analysis(*scenario(lambda i, s: proved if i == 'l166-learned-neg_goal_doubled' else None))
    assert 'l166-learned-neg_goal_doubled' in a['controls']['control_1']['failures'] and a['outcome'] == 'partial'

    # the review's first probe: the negative controls ending in harness failures, or refused before the final step
    harness = {'outcome': 'harness_failure', 'detail': 'synthetic'}
    a = run_analysis(*scenario(lambda i, s: harness if s['inject_unverified'] else None))
    assert len(a['controls']['control_1']['failures']) == 24 and a['controls']['control_4']['failures'] == ['l170-learned-draw1-injected']
    assert a['outcome'] == 'partial' and 'l170-learned-draw1-injected' in a['requires_diagnosis']
    a = run_analysis(*scenario(lambda i, s: fact if s['inject_unverified'] and s['site'] != 'bracket-l170' else None))
    assert len(a['controls']['control_1']['failures']) == 24 and a['outcome'] == 'partial'
    a = run_analysis(*scenario(lambda i, s: failure('proof_broker_term (constrained): the weighted sum does not cancel; x')
                               if i == 'l170-learned-draw1-injected' else None))
    assert a['controls']['control_4']['failures'] == ['l170-learned-draw1-injected']

    v, o, c8, c3 = scenario(); o['l069-control5-learned-draw1'] = [('closer_selected', {'closer': 'term_mode_int', 'comparison_type': 'ℕ'})]
    assert run_analysis(v, o, c8, c3)['controls']['control_6']['failures'] == ['l069-control5-learned-draw1']

    # control 5: an expected pass failing makes the outcome partial; a diagnostic-only entry does not
    a = run_analysis(*scenario(lambda i, s: {'closer': 'term_mode_int'} if i == 'l070-control5-learned-draw1' else None))
    assert a['controls']['control_5']['requires_diagnosis'] == ['l070-control5-learned-draw1'] and a['outcome'] == 'partial'
    a = run_analysis(*scenario(lambda i, s: fact if i == 'l071-control5-deterministic' else None))
    assert a['outcome'] == 'complete_success' and a['controls']['control_5']['requires_diagnosis'] == []

    # the review's second probe: control-8 summaries are not evidence
    v, o, c8, c3 = scenario()
    c8['results']['l166-learned-draw1']['report'] = {'exit': 1, 'refused': 'synthetic'}
    rejected(v, o, c8, c3, needle='does not support')
    v, o, c8, c3 = scenario()
    c8['results']['l166-learned-draw1']['report']['audit']['local']['hypotheses'] = [{'name': 'h'}]
    c8['results']['l166-learned-draw1']['unmet'] = ["local refers to ['h']"]; c8['passed'] = False
    a = run_analysis(v, o, c8, c3)
    assert a['outcome'] == 'partial' and a['measurement']['consumed_and_validated'] == 35 and not a['controls']['control_8']['passed']
    v, o, c8, c3 = scenario()
    for i in [i for i, r in c8['results'].items() if r['outcome'] != 'proved']: del c8['results'][i]
    rejected(v, o, c8, c3, needle='exactly the plan')
    v, o, c8, c3 = scenario(); c8['results']['l166-learned-draw1']['seal_sha256'] = 'stale'
    rejected(v, o, c8, c3, needle='differs from the run')
    v, o, c8, c3 = scenario(); c8['results']['l166-learned-draw1']['command']['inputs']['<tmp>/export.ndjson']['sha256'] = 'other'
    rejected(v, o, c8, c3, needle='locked program')
    v, o, c8, c3 = scenario(); del c8['results']['l166-learned-draw1']
    rejected(v, o, c8, c3, needle='exactly the plan')

    # ... and neither are control 3's
    v, o, c8, c3 = scenario(); c3['results']['constrained']['errors'] = []
    rejected(v, o, c8, c3, needle='contradicts')
    v, o, c8, c3 = scenario(); c3['dry_run'] = {'lock': 'stubbed'}
    rejected(v, o, c8, c3, needle='dry run')
    v, o, c8, c3 = scenario(); c3['sources_sha256'] = {k: '0' * 64 for k in c3['sources_sha256']}
    rejected(v, o, c8, c3, needle='locked programs')
    v, o, c8, c3 = scenario(); c3['results']['pinned']['exit'] = 1; c3['unmet'] = ['pinned: the documented difference did not reproduce']; c3['passed'] = False
    a = run_analysis(v, o, c8, c3)
    assert a['outcome'] == 'partial' and not a['controls']['control_3']['passed']


if __name__ == '__main__':
    test_classify(); print('test_classify passed')
    test_outcomes(); print('test_outcomes passed')

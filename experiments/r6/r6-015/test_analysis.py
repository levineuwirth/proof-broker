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


def scenario(fail=lambda i, s: None):
    """Stand-in evidence for every planned episode: everything as frozen, except where `fail` returns an outcome."""
    verdicts, observed, c8 = {}, {}, {}
    for i, s in PLAN.items():
        site = s['site'].removeprefix('bracket-')
        nat = site in ('l069', 'l070', 'l071', 'l078')
        closer = 'term_mode_nat' if nat else 'term_mode_int'
        selected = ('closer_selected', {'closer': closer, 'comparison_type': 'ℕ' if nat else 'ℤ'})
        bypass = [('certificate_gate_bypassed', {'certificate': CERT})] if s['inject_unverified'] else []
        if site == 'l170' and not s['inject_unverified']:
            v = {'outcome': 'certificate_rejected', 'certificate_accepted': False}; ev = []
        elif s['inject_unverified']:
            v = {'outcome': 'reconstruction_failed', 'certificate_accepted': False,
                 'detail': {'events': [], 'errors': [LINE + 'proof_broker_term (constrained): the weighted sum does not cancel; x']}}
            ev = bypass + [selected]
        else:
            v = {'outcome': 'proved', 'certificate_accepted': True, 'closer': closer, 'final_step': 'constrained',
                 'local_validated': True, 'whole_validated': True, 'axiom_delta': {}}
            ev = [selected]
        override = fail(i, s)
        if override: v = {**v, **override}
        verdicts[i] = v; observed[i] = ev
        if v['outcome'] == 'proved': c8[i] = {'bound': True, 'audited': True, 'unmet': []}
        else: c8[i] = {'bound': True, 'audited': False, 'outcome': v['outcome']}
    return verdicts, observed, c8


def run_analysis(verdicts, observed, c8, control3_passed=True):
    saved = (replay_lock.verify_lock, replay_lock.planned, replay_lock.LOCK, replay_campaign.bound, analysis.reconstruct_events,
             analysis.axioms_ok, analysis.packet_certificate)
    with tempfile.TemporaryDirectory(prefix='r6-015-analysis-') as tmp:
        lock = Path(tmp)/'lock.json'; lock.write_text('{"stand-in": true}\n'); sha = r6.sha(lock)
        replay_lock.verify_lock = lambda: {'stand-in': True}
        replay_lock.planned = lambda frozen: copy.deepcopy(PLAN)
        replay_lock.LOCK = lock
        replay_campaign.bound = lambda run, spec, frozen, lock_sha: (None, verdicts[spec['id']])
        analysis.reconstruct_events = lambda run: observed[run.name]
        analysis.axioms_ok = lambda run, verdict: True
        analysis.packet_certificate = lambda run: CERT
        try:
            return analysis.analyse(Path(tmp), {'lock_sha256': sha, 'passed': control3_passed, 'unmet': []},
                                    {'lock_sha256': sha, 'passed': all(r.get('unmet', []) == [] for r in c8.values()), 'results': c8})
        finally:
            (replay_lock.verify_lock, replay_lock.planned, replay_lock.LOCK, replay_campaign.bound, analysis.reconstruct_events,
             analysis.axioms_ok, analysis.packet_certificate) = saved


def measured(i, s):
    return s['site'] in ('bracket-l166', 'bracket-l175', 'bracket-l178', 'bracket-l204') and s['coefficients'] is None and not s['inject_unverified']


def test_outcomes():
    a = run_analysis(*scenario())
    assert a['outcome'] == 'complete_success' and a['measurement']['consumed_and_validated'] == 36, a['outcome']
    assert all(a['controls'][c]['passed'] for c in ('control_1', 'control_2', 'control_3', 'control_4', 'control_6', 'control_8'))
    assert a['controls']['control_5']['expected_pass_met'] == a['controls']['control_5']['expected_pass'] == 10
    assert len(a['measurement']['per_map']) == 6 and len(a['measurement']['per_class']) == 5

    fact = {'outcome': 'reconstruction_failed', 'detail': {'events': [], 'errors': [LINE + "proof_broker_term: witness names hypothesis 'hlt' which is not in scope"]}}
    a = run_analysis(*scenario(lambda i, s: fact if measured(i, s) and s['site'] == 'bracket-l166' else None))
    assert a['outcome'] == 'partial' and a['measurement']['consumed_and_validated'] == 27
    assert a['measurement']['per_obligation']['l166']['learned'] == {'episodes': 8, 'consumed_and_validated': 0, 'stages': {'fact_assertion': 8}}

    a = run_analysis(*scenario(lambda i, s: fact if measured(i, s) else None))
    assert a['outcome'] == 'none'

    a = run_analysis(*scenario(lambda i, s: fact if i == 'l204-learned-scaled_2' else None))
    assert a['outcome'] == 'partial' and a['controls']['control_2']['failures'] == ['l204-learned-scaled_2']

    a = run_analysis(*scenario(lambda i, s: {'outcome': 'proved', 'closer': 'term_mode_int', 'final_step': 'constrained', 'local_validated': True,
                                             'whole_validated': True, 'axiom_delta': {}} if i == 'l166-learned-neg_goal_doubled' else None))
    assert 'l166-learned-neg_goal_doubled' in a['controls']['control_1']['failures'] and a['outcome'] == 'partial'

    v, o, c8 = scenario(); o['l069-control5-learned-draw1'] = [('closer_selected', {'closer': 'term_mode_int', 'comparison_type': 'ℕ'})]
    a = run_analysis(v, o, c8)
    assert a['controls']['control_6']['failures'] == ['l069-control5-learned-draw1'] and a['outcome'] == 'partial'

    v, o, c8 = scenario(); v['l070-control5-learned-draw1'] = {**v['l070-control5-learned-draw1'], 'closer': 'term_mode_int'}
    a = run_analysis(v, o, c8)
    assert a['controls']['control_5']['requires_diagnosis'] == ['l070-control5-learned-draw1'] and a['outcome'] == 'complete_success'

    v, o, c8 = scenario(); c8['l166-learned-draw1'] = {'bound': True, 'audited': True, 'unmet': ['local refers to [h]']}
    a = run_analysis(v, o, c8)
    assert a['outcome'] == 'partial' and a['measurement']['consumed_and_validated'] == 35

    v, o, c8 = scenario(); del c8['l166-learned-draw1']
    try:
        run_analysis(v, o, c8)
    except SystemExit as stop:
        assert 'not audited' in str(stop)
    else:
        raise AssertionError('a proof without control 8 was accepted')

    a = run_analysis(*scenario(), control3_passed=False)
    assert a['outcome'] == 'partial'


if __name__ == '__main__':
    test_classify(); print('test_classify passed')
    test_outcomes(); print('test_outcomes passed')

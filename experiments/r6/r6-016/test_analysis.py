#!/usr/bin/env python3
"""R6-016 analysis: tests before the lock. R6-015's (`r6-015/test_analysis.py`), on R6-016's analysis, with probes for its
changes: the two axiom gates, control 9, the diagnosis's record, R6-016's control-5 labels (12 expected passes), and failures
after a proof. Nothing is replayed, no closer runs, and no retained export is read: the diagnosed export's digests are stand-ins.

1. `classify` against real bridge error lines: those the synthetic rehearsal produced, those the bridge tests pin
   (`lean-bridge/Test/TermModeConstrained.lean`), and R6-014's own retained refusal line.
2. `analyse` end to end on the real 108-episode plan, with stand-in verdicts, events and control records per scenario
   (monkeypatched lock, binding, events and axioms), against the frozen outcome definitions and controls.

Run: `python3 r6-016/test_analysis.py` (or under pytest).
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
import diagnose_l070  # noqa: E402
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
    dry = r6.read_json(R6/'reviews/2026-10-02/R6-016-CONTROL-9-DRY-RUN-2.json')['results']  # R6-016's bridge's own lines
    real = [(dry['c9b']['errors'][0], 'constrained_final_step', 'does not cancel'),
            (dry['c9e_without']['errors'][0], 'constrained_final_step', 'does not cancel'),
            (dry['c9f']['errors'][0], 'constrained_final_step', 'reaches hypotheses'),
            (rehearsal['invalid_injected']['errors'][0], 'constrained_final_step', 'does not cancel'),
            (rehearsal['invalid_checked']['errors'][0], 'bridge_gate', 'verifier'),
            (rehearsal['valid_pinned']['errors'][0], 'selection', 'goal shape'),
            (refusal, 'selection', 'goal shape')]
    for line, stage, detail in [(LINE + l, s, d) for l, s, d in CASES] + real:
        got = analysis.classify({'outcome': 'reconstruction_failed', 'detail': {'events': [], 'errors': [line]}})
        assert got[:2] == (stage, detail), (line, got)
    assert analysis.classify({'outcome': 'kernel_rejected', 'detail': 'x'})[0] == 'kernel'
    assert analysis.classify({'outcome': 'certificate_rejected'})[0] == 'checker'
    assert analysis.classify({'outcome': 'context_changed', 'detail': 'x'})[:2] == ('harness', 'context_changed')


PLAN = {s['id']: s for s in r6.read_json(R6/'r6-015/plan.json')['episodes']}
CERT = {'synthetic': True}
V2_LOCK = 'policies/qualification-audit-v2.sha256.json'
FROZEN = {'bridge_rev': 'B' * 40, 'instrumented_tactic_sha256': 'T' * 64,
          'binaries_sha256': {'audit_tool': 'A' * 64, 'diagnosis_tool': 'D' * 64},
          'python_sha256': {str(f.relative_to(R6)): 'P' * 64 for f in (*analysis.control3.SOURCES, *analysis.control9.SOURCES,
                                                                       diagnose_l070.SOURCES[0])},
          'data_sha256': {V2_LOCK: 'Q' * 64, 'r6-016/diagnosis/Diagnose.lean': 'L' * 64}}
EXPORT = {'packed': 'packed-l070-5', 'sealed': 'packed-l070-5', 'unpacked': 'unpacked-l070-5'}


def targets(site):
    return f'{site}.local', f'{site}.whole'


def residual_command(i):
    local, whole = targets(PLAN[i]['site'])
    return {'argv': [analysis.AUDIT_ARGV0, '--synthetic', '<tmp>/export.ndjson', local, whole, '-', 'residual/report.json'],
            'env': dict(analysis.AUDIT_ENV), 'exit_code': 0, 'tool_sha256': FROZEN['binaries_sha256']['audit_tool'],
            'audit_lock_sha256': FROZEN['data_sha256'][V2_LOCK],
            'inputs': {'<tmp>/export.ndjson': {'unpacked_from': 'solution.ndjson.gz', 'sha256': digests(i)['export_sha256']}}}
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
    return verdicts, observed, control8_for(verdicts), control3_record(), control9_record(), diagnosis_record()


def control8_for(verdicts, report=PASSING_REPORT):
    results = {}
    for i, v in verdicts.items():
        d = digests(i)
        if v['outcome'] == 'proved':
            local, whole = targets(PLAN[i]['site'])
            results[i] = {'bound': True, 'outcome': 'proved', 'audited': True, 'unmet': [], 'report': copy.deepcopy(report),
                          'command': {'argv': [analysis.AUDIT_ARGV0, '<tmp>/export.ndjson', local, whole, '<tmp>/residual.txt', '<tmp>/report.json'],
                                      'env': dict(analysis.AUDIT_ENV), 'exit_code': report['exit'],
                                      'tool_sha256': FROZEN['binaries_sha256']['audit_tool'],
                                      'inputs': {'<tmp>/export.ndjson': {'sha256': d['export_sha256']},
                                                 '<tmp>/residual.txt': {'sha256': d['residual_sha256']}}},
                          **{k: d[k] for k in ('seal_sha256', 'verdict_sha256', 'solution_sha256', 'residual_sha256')}}
        else:
            results[i] = {'bound': True, 'outcome': v['outcome'], 'audited': False,
                          **{k: d[k] for k in ('seal_sha256', 'verdict_sha256')}}
    return {'schema_version': 'r6-016-control-8-1', 'passed': True, 'results': results, 'audit_lock_sha256': FROZEN['data_sha256'][V2_LOCK]}


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
            'sources_sha256': {str(f.relative_to(R6)): 'P' * 64 for f in analysis.control3.SOURCES}}


def control9_record():
    """A control-9 record as `control9.py` writes it, every case as frozen."""
    results = {}
    for name, (_, _, _, checker, expectation) in analysis.control9.CASES.items():
        injected = checker is False
        closes = expectation == 'closes'
        r = {'prepared': True, 'checker': {'accepted': checker}, 'injected': injected, 'exit': 0 if closes else 1,
             'events': (['certificate_gate_bypassed'] if injected else []) + ['term_route', 'closer_selected'] + (['reconstruction_finished'] if closes else []),
             'term_route': {'constrained': True}, 'closer_selected': {'closer': 'term_mode_int', 'route': 'constrained'},
             'reconstruction_finished': {'closer': 'term_mode_int', 'final_step': 'constrained', 'residual_closer': 'constrained_normalization'} if closes else {},
             'errors': [] if closes else [LINE + f'proof_broker_term (constrained): {expectation}']}
        results[name] = r
    results['c9a']['axioms'] = {'c9a_whole': ['propext', 'Quot.sound'], 'c9a_omega': ['propext', 'Quot.sound'],
                                'ProofBroker.TermMode.posOfLinearNum': ['propext', 'Quot.sound']}
    cases = {n: {'statement': c[1], 'witness': c[2], 'checker': c[3], 'expectation': c[4]} for n, c in analysis.control9.CASES.items()}
    return {'schema_version': analysis.control9.SCHEMA, 'control': 9, 'passed': True, 'unmet': [], 'results': results,
            'evidence': {n: {'coefficients': c['witness']} for n, c in cases.items()}, 'cases': cases,
            'bridge_rev': FROZEN['bridge_rev'], 'instrumented_tactic_sha256': FROZEN['instrumented_tactic_sha256'],
            'sources_sha256': {str(f.relative_to(R6)): 'P' * 64 for f in analysis.control9.SOURCES}}


def attempt(outcome): return {'outcome': outcome, 'detail': 'stand-in'}


def pair(defeq=False, kernel=False, omega=False, cex=False):
    """A diagnosed pair, shaped as the program reports one."""
    return {'atoms': [0, 1], 'syntactic': {'equal_after_instantiation': False, 'equal_up_to_metadata': False, 'first_difference': None},
            'definitional': {'meta': [{'transparency': t, 'zeta_delta': z, **attempt('established' if defeq and t == 'default' else 'unsuccessful')}
                                      for t in ('reducible', 'instances', 'default') for z in (False, True)],
                             'kernel': attempt('established' if kernel else 'unsuccessful')},
            'arithmetic': {'omega': attempt('established' if omega else 'unsuccessful'), 'grobner': attempt('unsuccessful')},
            'counterexample': {**attempt('established' if cex else 'unsuccessful'), 'instance': [['x', 1]]}}


def diagnosis_record(pairs=None):
    pairs = [pair()] if pairs is None else pairs
    report = {'environment': {}, 'diagnosis': {'located': True, 'positivity': '0 < s', 'atoms': [{}, {}], 'pairs': pairs}}
    d = diagnose_l070
    return {'schema_version': d.SCHEMA, 'slot': d.SLOT, 'run': d.RUN, 'local': 'Bracket.lift_cell.r6_site_l070',
            'tool_sha256': FROZEN['binaries_sha256']['diagnosis_tool'],
            'sources_sha256': {'r6-016/diagnose_l070.py': 'P' * 64, 'r6-016/diagnosis/Diagnose.lean': 'L' * 64},
            'audit_source_sha256': r6.sha(d.AUDIT_SOURCE),
            'command': {'argv': [str(d.TOOL.relative_to(R6)), '<tmp>/export.ndjson', 'Bracket.lift_cell.r6_site_l070', '<tmp>/report.json'],
                        'env': dict(d.ENV), 'exit_code': 0, 'tool_sha256': FROZEN['binaries_sha256']['diagnosis_tool'],
                        'inputs': {'<tmp>/export.ndjson': {'sha256': EXPORT['unpacked'], 'packed_sha256': EXPORT['packed']}}},
            'report': report, 'pairs': d.classified(report)}


def gates_for(i, override=None):
    g = {k: {'target': k, 'kernel_accepted': True, 'axioms': ['propext', 'Quot.sound'], 'allowlist': True, 'unchanged': True,
             'delta': {'added': [], 'removed': []}} for k in ('local', 'whole')}
    for k, v in (override or {}).items(): g[k].update(v)
    return g


def run_analysis(verdicts, observed, c8, c3, c9, diag, residuals=None, changed_after=None, gates=None):
    saved = (replay_lock.verify_lock, replay_lock.planned, replay_lock.LOCK, replay_campaign.bound, analysis.reconstruct_events,
             analysis.axiom_gates, analysis.packet_certificate, analysis.current, analysis.targets, analysis.residual_command,
             analysis.revalidate, analysis.export_digests)
    with tempfile.TemporaryDirectory(prefix='r6-016-analysis-') as tmp:
        tmp = Path(tmp)
        lock = tmp/'lock.json'; lock.write_text('{"stand-in": true}\n'); sha = r6.sha(lock)
        c8 = {**c8, 'lock_sha256': c8.get('lock_sha256', sha)}; c3 = {**c3, 'lock_sha256': c3.get('lock_sha256', sha)}
        c9 = {**c9, 'lock_sha256': c9.get('lock_sha256', sha)}; diag = {**diag, 'lock_sha256': diag.get('lock_sha256', sha)}
        r6.write_json(tmp/'c8.json', c8); r6.write_json(tmp/'c3.json', c3); r6.write_json(tmp/'c9.json', c9); r6.write_json(tmp/'d.json', diag)
        replay_lock.verify_lock = lambda: copy.deepcopy(FROZEN)
        replay_lock.planned = lambda frozen: copy.deepcopy(PLAN)
        replay_lock.LOCK = lock
        replay_campaign.bound = lambda run, spec, frozen, lock_sha: (None, verdicts[spec['id']])
        analysis.reconstruct_events = lambda run: observed[run.name]
        analysis.axiom_gates = lambda run, verdict, site: gates_for(run.name, (gates or {}).get(run.name))
        analysis.export_digests = lambda: dict(EXPORT)
        analysis.packet_certificate = lambda run: CERT
        analysis.current = lambda run, proved: {k: v for k, v in digests(run.name).items()
                                               if proved or k in ('seal_sha256', 'verdict_sha256')}
        analysis.targets = targets
        analysis.residual_command = lambda run: (residuals or {}).get(run.name) or residual_command(run.name)
        def revalidate(run):  # the after-check: a file sealed in the run changed, its seal file unchanged
            if run.name == changed_after: raise ValueError('solution.ndjson.gz differs from the seal')
            return digests(run.name)['seal_sha256']
        analysis.revalidate = revalidate
        try:
            return analysis.analyse(tmp/'runs', tmp/'c3.json', tmp/'c9.json', tmp/'c8.json', tmp/'d.json')
        finally:
            (replay_lock.verify_lock, replay_lock.planned, replay_lock.LOCK, replay_campaign.bound, analysis.reconstruct_events,
             analysis.axiom_gates, analysis.packet_certificate, analysis.current, analysis.targets, analysis.residual_command,
             analysis.revalidate, analysis.export_digests) = saved


def rejected(*args, needle, **kw):
    try:
        run_analysis(*args, **kw)
    except SystemExit as stop:
        assert needle in str(stop), str(stop)
        return
    raise AssertionError(f'accepted; expected a rejection mentioning {needle!r}')


def measured(i, s):
    return s['site'] in ('bracket-l166', 'bracket-l175', 'bracket-l178', 'bracket-l204') and s['coefficients'] is None and not s['inject_unverified']


def test_outcomes():
    a = run_analysis(*scenario())
    assert a['outcome'] == 'complete_success' and a['measurement']['consumed_and_validated'] == 36, a['outcome_reasons']
    assert all(a['controls'][c]['passed'] for c in ('control_1', 'control_2', 'control_3', 'control_4', 'control_5', 'control_6',
                                                    'control_8', 'control_9'))
    assert a['controls']['control_5']['expected_pass_met'] == a['controls']['control_5']['expected_pass'] == 12
    assert sorted(a['controls']['control_5']['diagnostic_only']) == ['l070-control5-learned-draw5', 'l071-control5-deterministic']
    assert a['failures_after_proof'] == {} and a['l070_diagnosis']['pairs'] == [{'atoms': [0, 1], 'classification': 'equality_not_established',
                                                                                  'basis': 'no attempt established equality or a counterexample'}]
    assert len(a['measurement']['per_map']) == 6 and len(a['measurement']['per_class']) == 5

    fact = failure("proof_broker_term: witness names hypothesis 'hlt' which is not in scope")
    a = run_analysis(*scenario(lambda i, s: fact if measured(i, s) and s['site'] == 'bracket-l166' else None))
    assert a['outcome'] == 'partial' and a['measurement']['consumed_and_validated'] == 27
    assert a['measurement']['per_obligation']['l166']['learned'] == {'episodes': 8, 'consumed_and_validated': 0, 'stages': {'fact_assertion': 8},
                                                                  'proofs': 0, 'allowlist_failed': 0, 'unchanged_failed': 0,
                                                                  'control_8_failed': 0}
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

    v, o, c8, c3, c9, dg = scenario(); o['l069-control5-learned-draw1'] = [('closer_selected', {'closer': 'term_mode_int', 'comparison_type': 'ℕ'})]
    assert run_analysis(v, o, c8, c3, c9, dg)['controls']['control_6']['failures'] == ['l069-control5-learned-draw1']

    # control 5: an expected pass failing makes the outcome partial; a diagnostic-only entry does not
    a = run_analysis(*scenario(lambda i, s: {'closer': 'term_mode_int'} if i == 'l070-control5-learned-draw1' else None))
    assert a['controls']['control_5']['requires_diagnosis'] == ['l070-control5-learned-draw1'] and a['outcome'] == 'partial'
    a = run_analysis(*scenario(lambda i, s: fact if i == 'l071-control5-deterministic' else None))
    assert a['outcome'] == 'complete_success' and a['controls']['control_5']['requires_diagnosis'] == []

    # the review's second probe: control-8 summaries are not evidence
    v, o, c8, c3, c9, dg = scenario()
    c8['results']['l166-learned-draw1']['report'] = {'exit': 1, 'refused': 'synthetic'}
    rejected(v, o, c8, c3, c9, dg, needle='targets and environment')  # the command's exit disagrees with the report
    c8['results']['l166-learned-draw1']['command']['exit_code'] = 1  # agreeing: the recomputed predicate rejects the summary
    rejected(v, o, c8, c3, c9, dg, needle='does not support')
    v, o, c8, c3, c9, dg = scenario()
    c8['results']['l166-learned-draw1']['report']['audit']['local']['hypotheses'] = [{'name': 'h'}]
    c8['results']['l166-learned-draw1']['unmet'] = ["local refers to ['h']"]; c8['passed'] = False
    a = run_analysis(v, o, c8, c3, c9, dg)
    assert a['outcome'] == 'partial' and a['measurement']['consumed_and_validated'] == 35 and not a['controls']['control_8']['passed']
    v, o, c8, c3, c9, dg = scenario()
    for i in [i for i, r in c8['results'].items() if r['outcome'] != 'proved']: del c8['results'][i]
    rejected(v, o, c8, c3, c9, dg, needle='exactly the plan')
    v, o, c8, c3, c9, dg = scenario(); c8['results']['l166-learned-draw1']['seal_sha256'] = 'stale'
    rejected(v, o, c8, c3, c9, dg, needle='differs from the run')
    v, o, c8, c3, c9, dg = scenario(); c8['results']['l166-learned-draw1']['command']['inputs']['<tmp>/export.ndjson']['sha256'] = 'other'
    rejected(v, o, c8, c3, c9, dg, needle='locked program')
    v, o, c8, c3, c9, dg = scenario(); del c8['results']['l166-learned-draw1']
    rejected(v, o, c8, c3, c9, dg, needle='exactly the plan')

    # ... and neither are control 3's
    v, o, c8, c3, c9, dg = scenario(); c3['results']['constrained']['errors'] = []
    rejected(v, o, c8, c3, c9, dg, needle='contradicts')
    v, o, c8, c3, c9, dg = scenario(); c3['dry_run'] = {'lock': 'stubbed'}
    rejected(v, o, c8, c3, c9, dg, needle='dry run')
    v, o, c8, c3, c9, dg = scenario(); c3['sources_sha256'] = {k: '0' * 64 for k in c3['sources_sha256']}
    rejected(v, o, c8, c3, c9, dg, needle='locked programs')
    v, o, c8, c3, c9, dg = scenario(); c3['results']['pinned']['exit'] = 1; c3['unmet'] = ['pinned: the documented difference did not reproduce']; c3['passed'] = False
    a = run_analysis(v, o, c8, c3, c9, dg)
    assert a['outcome'] == 'partial' and not a['controls']['control_3']['passed']

    # the review of revision 2: the after-check, and execution metadata
    rejected(*scenario(), needle='changed during the analysis', changed_after='l166-learned-draw1')
    v, o, c8, c3, c9, dg = scenario(); del c3['results']['constrained']['exit']
    rejected(v, o, c8, c3, c9, dg, needle='contradicts')
    v, o, c8, c3, c9, dg = scenario(); c3['results']['pinned']['exit'] = False
    rejected(v, o, c8, c3, c9, dg, needle='contradicts')
    for change in (lambda c: c['argv'].insert(1, '--synthetic'), lambda c: c['argv'].__setitem__(0, 'other-binary'),
                   lambda c: c['argv'].__setitem__(2, 'wrong.local'), lambda c: c['env'].__setitem__('LEAN_SYSROOT', '/elsewhere'),
                   lambda c: c.__setitem__('exit_code', 1), lambda c: c.pop('exit_code')):
        v, o, c8, c3, c9, dg = scenario(); change(c8['results']['l166-learned-draw1']['command'])
        rejected(v, o, c8, c3, c9, dg, needle='targets and environment')
    for change in (lambda c: c.__setitem__('exit_code', 1), lambda c: c['argv'].remove('--synthetic'),
                   lambda c: c['inputs']['<tmp>/export.ndjson'].__setitem__('sha256', 'other'),
                   lambda c: c.__setitem__('audit_lock_sha256', 'other')):
        bad = residual_command('l166-learned-draw1'); change(bad)
        rejected(*scenario(), needle='residual not printed', residuals={'l166-learned-draw1': bad})

    # R6-016: the two axiom gates, reported separately; a proof failing either is not consumed, and is listed for diagnosis
    a = run_analysis(*scenario(), gates={'l166-learned-draw1': {'whole': {'unchanged': False, 'delta': {'added': ['Classical.choice'], 'removed': []}}}})
    e = a['episodes']['l166-learned-draw1']
    assert e['allowlist'] is True and e['unchanged'] is False and not e['consumed_and_validated'] and a['outcome'] == 'partial'
    assert a['failures_after_proof'] == {'l166-learned-draw1': ['unchanged']} and 'l166-learned-draw1' in a['requires_diagnosis']
    assert a['measurement']['per_obligation']['l166']['learned']['unchanged_failed'] == 1
    a = run_analysis(*scenario(), gates={'l204-deterministic': {'local': {'allowlist': False, 'axioms': ['sorryAx']}}})
    assert a['failures_after_proof'] == {'l204-deterministic': ['allowlist']} and a['episodes']['l204-deterministic']['unchanged'] is True
    v, o, c8, c3, c9, dg = scenario()
    c8['results']['l175-learned-draw1']['report']['audit']['whole'] = {'locatable': False}
    c8['results']['l175-learned-draw1']['unmet'] = ['whole not locatable', 'whole.hypotheses missing']; c8['passed'] = False
    a = run_analysis(v, o, c8, c3, c9, dg)
    assert a['failures_after_proof'] == {'l175-learned-draw1': ['control_8']} and a['outcome'] == 'partial'

    # control 5: l096's and l099's learned maps are expected passes now
    a = run_analysis(*scenario(lambda i, s: fact if i == 'l096-control5-learned-draw1' else None))
    assert a['controls']['control_5']['requires_diagnosis'] == ['l096-control5-learned-draw1'] and a['outcome'] == 'partial'

    # control 9: recomputed, as control 3 is
    v, o, c8, c3, c9, dg = scenario(); c9['results']['c9b']['errors'] = []
    rejected(v, o, c8, c3, c9, dg, needle='control 9: the record contradicts')
    v, o, c8, c3, c9, dg = scenario(); c9['dry_run'] = 'pre-lock'
    rejected(v, o, c8, c3, c9, dg, needle='dry run')
    v, o, c8, c3, c9, dg = scenario(); c9['cases']['c9b']['checker'] = True
    rejected(v, o, c8, c3, c9, dg, needle='frozen cases')
    v, o, c8, c3, c9, dg = scenario(); c9['sources_sha256'] = {k: '0' * 64 for k in c9['sources_sha256']}
    rejected(v, o, c8, c3, c9, dg, needle='control 9: not run by the locked programs')
    v, o, c8, c3, c9, dg = scenario(); c9['results']['c9a']['axioms']['c9a_whole'].append('Classical.choice')
    c9['unmet'] = analysis.control9.evaluate(c9['results']); c9['passed'] = False
    a = run_analysis(v, o, c8, c3, c9, dg)
    assert a['outcome'] == 'partial' and not a['controls']['control_9']['passed'] and 'control_9 not as frozen' in a['outcome_reasons']

    # the diagnosis: bound to the sealed export and the locked program; its classifications recomputed
    for p, want in ((pair(defeq=True, kernel=True), 'printed_only'), (pair(kernel=True), 'printed_only'),
                    (pair(omega=True), 'arithmetically_equal'), (pair(cex=True), 'distinct')):
        v, o, c8, c3, c9, dg = scenario(); dg = diagnosis_record([p])
        assert run_analysis(v, o, c8, c3, c9, dg)['l070_diagnosis']['pairs'][0]['classification'] == want
    # the harness review's probes: inconsistent or contradictory evidence is rejected, not classified
    syntactic = pair(cex=True); syntactic['syntactic']['equal_after_instantiation'] = True
    for p in (pair(defeq=True, kernel=False), pair(omega=True, cex=True), syntactic):
        v, o, c8, c3, c9, dg = scenario(); dg = diagnosis_record([p])
        rejected(v, o, c8, c3, c9, dg, needle='evidence is inconsistent')
    # ... and the target is the locked selection's, not the record's
    v, o, c8, c3, c9, dg = scenario(); dg['local'] = 'Wrong.local'; dg['command']['argv'][2] = 'Wrong.local'
    rejected(v, o, c8, c3, c9, dg, needle='diagnosis: identity')
    v, o, c8, c3, c9, dg = scenario(); dg['command']['argv'][2] = 'Wrong.local'
    rejected(v, o, c8, c3, c9, dg, needle='sealed export')
    v, o, c8, c3, c9, dg = scenario(); dg['pairs'][0]['classification'] = 'distinct'
    rejected(v, o, c8, c3, c9, dg, needle='contradicts its attempts')
    v, o, c8, c3, c9, dg = scenario(); dg['command']['inputs']['<tmp>/export.ndjson']['packed_sha256'] = 'other'
    rejected(v, o, c8, c3, c9, dg, needle='sealed export')
    v, o, c8, c3, c9, dg = scenario(); dg['command']['exit_code'] = 1
    rejected(v, o, c8, c3, c9, dg, needle='sealed export')
    v, o, c8, c3, c9, dg = scenario(); dg['tool_sha256'] = 'other'
    rejected(v, o, c8, c3, c9, dg, needle='locked programs')
    v, o, c8, c3, c9, dg = scenario(); dg['report']['diagnosis']['located'] = False
    rejected(v, o, c8, c3, c9, dg, needle='no located report')


if __name__ == '__main__':
    test_classify(); print('test_classify passed')
    test_outcomes(); print('test_outcomes passed')

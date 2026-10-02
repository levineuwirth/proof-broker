#!/usr/bin/env python3
"""R6-016 harness: tests of what is new against R6-015's, before the lock. No Lean runs, no closer runs, and no retained
export is read.

1. **The observations are R6-015's.** `replay_bridge`'s edits, receipt and option setting equal R6-015's module's, byte for byte,
   and apply to R6-016's `Tactic.lean` (`source_record`, without building).
2. **Admission** refuses every pinned episode, and every planned one without the lock.
3. **Control 5's labels** (`labels.py`): the rule over classifications, on synthetic slots; and the record, which changes R6-015's
   labels only at l096's and l099's learned maps.
4. **The diagnosis's classification** (`diagnose_l070.classify`), on stand-in pairs: every class, including `identical` and
   `arithmetically_equal`, which the synthetic exports cannot produce; only `established` counts; incomplete, inconsistent and
   contradictory records (harness review, finding 3).
5. **`AuditCore`** is the locked `Audit.lean` cut before its `main`; an `Audit.lean` the lock does not record is refused.
6. **Control 9's expectations** (`control9.evaluate`): a passing stand-in record passes, and each deviation is caught.
7. **The axiom gates** (`analysis.axiom_gates`, the real function; harness review, finding 1): on written kernel reports against
   stand-in frozen targets, the review's probe first; and on R6-015's 74 sealed proofs against the sites' frozen targets, where it
   reproduces R6-015's acceptance-4 result.

Run: `python3 r6-016/test_harness.py` (or under pytest).
"""
import copy
import gzip
import importlib.util
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import run as r6  # noqa: E402
import analysis  # noqa: E402
import control9  # noqa: E402
import diagnose_l070  # noqa: E402
import labels  # noqa: E402
import replay_bridge  # noqa: E402
import replay_lock  # noqa: E402


def r6015(name):
    spec = importlib.util.spec_from_file_location(f'r6015_{name}', R6/'r6-015'/f'{name}.py')
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def test_observations_are_r6015s():
    old = r6015('replay_bridge')
    for attr in ('EDITS', 'SELECTED', 'RECEIPT', 'PINNED_CALL', 'CONSTRAINED_CALL', 'MODULES'):
        assert getattr(old, attr) == getattr(replay_bridge, attr), attr
    assert (old.BRIDGE_REV, replay_bridge.BRIDGE_REV) == ('476fab317e6633511b2a73b36313457d762e3a9c', '64585867afa1194be2b0832b77fd62bbefc2462b')
    sources, patch = replay_bridge.source_record()
    tactic = sources['lean-bridge/ProofBroker/Tactic.lean']
    assert tactic['base'] == replay_bridge.BRIDGE_REV and tactic['base_sha256'] != tactic['instrumented_sha256']
    assert '"constrained_normalization"' in patch and 'r6015CloserSelected "term_mode_nat"' in patch


def test_admission():
    pinned = {'id': 'x', 'site': 'bracket-l069', 'source': {'arm': 'learned', 'run': 'cohort-live-v9/l069-draw1'},
              'coefficients': None, 'inject_unverified': False, 'route': 'pinned'}
    for spec, needle in ((pinned, 'no pinned episode'), ({**pinned, 'route': 'constrained'}, 'does not exist')):
        saved = replay_lock.LOCK
        with tempfile.TemporaryDirectory() as tmp:
            replay_lock.LOCK = Path(tmp)/'absent.json'
            try:
                replay_lock.admit(spec)
            except replay_lock.Refused as refused:
                assert needle in str(refused), str(refused)
            else:
                raise AssertionError(f'admitted: {spec}')
            finally:
                replay_lock.LOCK = saved


def test_labels():
    e = labels.expectation
    assert e('l096', [1], {'s': 'unbound_residual_mismatch'}) == 'no_expectation: not classified by the audit'
    assert e('l096', [1], {'s': None}) == 'no_expectation: not classified by the audit'
    assert e('l096', [1], {'s': 'sufficient_but_context_referenced'}) == 'expected_pass'
    assert e('l070', [5], {'s': 'sufficiency_not_established'}) == 'no_fixed_prediction: sufficiency not established (draw 5)'
    assert e('l070', [1, 4], {'a': 'certificate_alone', 'b': 'sufficient_but_context_referenced'}) == 'expected_pass'
    assert e('l071', [1], {'a': 'certificate_alone', 'b': 'sufficiency_not_established'}) == 'no_expectation'
    record = labels.verify()
    step3 = r6.read_json(labels.STEP3)['control_5']
    assert len(record['control_5']) == len(step3) == 16 and record['expected_pass'] == 12
    for new, old in zip(record['control_5'], step3):
        assert (new['site'], new['source']) == (old['site'], old['source'])
        if old.get('retained') is False: assert new.get('retained') is False; continue
        changed = new['expectation'] != old['expectation']
        assert changed == (new['site'] in ('l096', 'l099') and new['source']['arm'] == 'learned'), new['site']
        if changed: assert new['expectation'] == 'expected_pass' and set(new['classified_by'].values()) == {'addendum_2'}


def pair(**kw):
    p = {'syntactic': {'equal_after_instantiation': False, 'equal_up_to_metadata': False},
         'definitional': {'meta': [{'transparency': t, 'zeta_delta': z, 'outcome': 'unsuccessful'}
                                   for t in ('reducible', 'instances', 'default') for z in (False, True)],
                          'kernel': {'outcome': 'unsuccessful'}},
         'arithmetic': {'omega': {'outcome': 'unsuccessful'}, 'grobner': {'outcome': 'unsuccessful'}},
         'counterexample': {'outcome': 'unsuccessful'}}
    for path, value in kw.items():
        *keys, last = path.split('.'); target = p
        for k in keys: target = target[int(k)] if k.isdigit() else target[k]
        target[int(last) if last.isdigit() else last] = value
    return p


def test_classify():
    c = diagnose_l070.classify
    est = {'outcome': 'established'}
    assert c(pair(**{'syntactic.equal_up_to_metadata': True})) == ('identical', 'equal up to metadata')
    assert c(pair(**{'definitional.meta.2': {'transparency': 'instances', 'zeta_delta': False, 'outcome': 'established'},
                     'definitional.kernel': est})) == ('printed_only', 'definitionally equal: instances, zeta_delta False')
    assert c(pair(**{'definitional.kernel': est})) == ('printed_only', 'definitionally equal: the kernel')
    assert c(pair(**{'arithmetic.grobner': est})) == ('arithmetically_equal', 'proved by grobner')
    assert c(pair(**{'counterexample': {'outcome': 'established', 'instance': [['x', 1]]}}))[0] == 'distinct'
    for outcome in ('refused', 'resource_exhausted', 'unsuccessful'):  # only established counts
        assert c(pair(**{'definitional.kernel': {'outcome': outcome}, 'arithmetic.omega': {'outcome': outcome},
                         'counterexample': {'outcome': outcome}}))[0] == 'equality_not_established'
    # contradictions are checked first, the syntactic ones included (the review's probe)
    for equal in ({'syntactic.equal_after_instantiation': True}, {'syntactic.equal_up_to_metadata': True},
                  {'definitional.kernel': est}, {'arithmetic.omega': est}):
        assert c(pair(**equal, counterexample=est))[0] == 'contradictory_evidence', equal
    # inconsistent: a meta-level equality the kernel did not confirm (the review's probe); a pair the selection excludes
    meta = {'transparency': 'default', 'zeta_delta': False, 'outcome': 'established'}
    assert c(pair(**{'definitional.meta.4': meta})) == ('inconsistent_evidence', 'a meta-level equality the kernel did not confirm')
    assert c(pair(**{'syntactic.equal_after_instantiation': True}))[0] == 'inconsistent_evidence'
    # incomplete: a missing attempt, an unknown outcome, the meta-level attempts out of order, a missing flag
    for change in ({'arithmetic.grobner': None}, {'counterexample': {'outcome': 'maybe'}},
                   {'definitional.meta.0': {'transparency': 'default', 'zeta_delta': False, 'outcome': 'unsuccessful'}},
                   {'syntactic.equal_up_to_metadata': None}):
        assert c(pair(**change)) == ('inconsistent_evidence', 'the record is incomplete'), change
    p = pair(); p['definitional']['meta'].pop()
    assert c(p) == ('inconsistent_evidence', 'the record is incomplete')


def test_audit_core():
    core = diagnose_l070.audit_core()
    text = diagnose_l070.AUDIT_SOURCE.read_text()
    assert text.startswith(core.rstrip('\n')) and 'def main' not in core and text[len(core) - 1:].lstrip('\n').startswith('def main')
    # a lock recording another digest for Audit.lean: the cut is refused
    saved = replay_lock.AUDIT_LOCK
    with tempfile.TemporaryDirectory() as tmp:
        lock = r6.read_json(saved); key = str(diagnose_l070.AUDIT_SOURCE.relative_to(R6.parents[1]))
        assert key in lock['sources_sha256']
        lock['sources_sha256'][key] = '0' * 64
        replay_lock.AUDIT_LOCK = Path(tmp)/'lock.json'; r6.write_json(replay_lock.AUDIT_LOCK, lock)
        try:
            diagnose_l070.audit_core()
        except ValueError as refused:
            assert "differs from qualification-audit-v2's lock" in str(refused), str(refused)
        else:
            raise AssertionError("an Audit.lean the lock does not record was accepted")
        finally:
            replay_lock.AUDIT_LOCK = saved


def passing_control9():
    results = {}
    for name, (_, _, _, checker, expectation) in control9.CASES.items():
        closes = expectation == 'closes'
        results[name] = {'prepared': True, 'checker': {'accepted': checker}, 'injected': checker is False, 'exit': 0 if closes else 1,
                         'events': (['certificate_gate_bypassed'] if checker is False else []) + ['term_route', 'closer_selected'],
                         'term_route': {'constrained': True}, 'closer_selected': {'closer': 'term_mode_int', 'route': 'constrained'},
                         'reconstruction_finished': {'closer': 'term_mode_int', 'final_step': 'constrained',
                                                     'residual_closer': 'constrained_normalization'} if closes else {},
                         'errors': [] if closes else [f'Synthetic.lean:4:2: error: proof_broker_term (constrained): {expectation}']}
    results['c9a']['axioms'] = {'c9a_whole': ['propext', 'Quot.sound'], 'c9a_omega': ['propext', 'Quot.sound'],
                                'ProofBroker.TermMode.posOfLinearNum': ['propext', 'Quot.sound']}
    return results


def test_control9_evaluate():
    assert control9.evaluate(passing_control9()) == []
    probes = {
        'a closing case fails': lambda r: r['c9c_cast'].update(exit=1),
        'a failing case closes': lambda r: r['c9b'].update(exit=0),
        'the wrong failure': lambda r: r['c9f'].update(errors=['proof_broker_term (constrained): the weighted sum does not cancel']),
        'another checker verdict': lambda r: r['c9d_zero'].update(checker={'accepted': False}, injected=True),
        'injected though accepted': lambda r: r['c9a'].update(injected=True),
        'injection unrecorded': lambda r: r['c9e_without'].update(events=['term_route', 'closer_selected']),
        'the pinned route': lambda r: r['c9c_order'].update(term_route={'constrained': False}),
        'a boolean exit': lambda r: r['c9b'].update(exit=True),
        'not prepared': lambda r: r.update(c9f={'prepared': False, 'errors': []}),
        'Classical.choice added': lambda r: r['c9a']['axioms']['c9a_whole'].append('Classical.choice'),
        'the omega proof uses Classical.choice': lambda r: [r['c9a']['axioms'][k].append('Classical.choice') for k in ('c9a_whole', 'c9a_omega')],
        'posOfLinearNum gains an axiom': lambda r: r['c9a']['axioms']['ProofBroker.TermMode.posOfLinearNum'].append('Classical.choice'),
        'the receipt names another step': lambda r: r['c9d_power']['reconstruction_finished'].update(final_step='pinned'),
    }
    for name, change in probes.items():
        r = copy.deepcopy(passing_control9()); change(r)
        assert control9.evaluate(r), f'not caught: {name}'


def write_reports(run, local, whole, names=('L', 'W'), accepted=True, extra=()):
    for kind, name, axioms in (('local', names[0], local), ('whole', names[1], whole)):
        report = {'accepted': accepted, 'targets': [{'name': name, 'axioms': axioms}, *extra]}
        (run/f'validation-{kind}.raw.json.gz').write_bytes(gzip.compress(json.dumps(report).encode()))


def delta(added=(), removed=()): return {'added': list(added), 'removed': list(removed)}


def stops(run, recorded, needle):
    try:
        analysis.axiom_gates(run, {'axiom_delta': recorded}, 'synthetic')
    except SystemExit as stop:
        assert needle in str(stop), str(stop)
        return
    raise AssertionError(f'accepted {recorded}; expected a stop mentioning {needle!r}')


def test_axiom_gates():
    saved = analysis.targets, analysis.original_axioms
    analysis.targets = lambda site: ('L', 'W')
    analysis.original_axioms = lambda site: {'L': ('Quot.sound', 'propext'), 'W': ('Classical.choice', 'Quot.sound', 'propext')}
    try:
        with tempfile.TemporaryDirectory() as tmp:
            run = Path(tmp)
            all3 = ['propext', 'Quot.sound', 'Classical.choice']
            write_reports(run, all3, all3)
            stops(run, {'L': {}, 'W': {}}, 'disagrees')                 # the review's probe: empty deltas
            stops(run, {'L': delta(), 'W': delta()}, 'disagrees')       # recorded unchanged, though the local target gained one
            stops(run, {'L': {'added': ['Classical.choice']}, 'W': delta()}, 'disagrees')
            stops(run, {'L': {**delta(['Classical.choice']), 'extra': []}, 'W': delta()}, 'disagrees')
            stops(run, {'L': delta(['Classical.choice'])}, 'exactly the local and whole')
            stops(run, None, 'exactly the local and whole')
            stops(run, {'L': delta(['Classical.choice']), 'W': delta(), 'X': delta()}, 'exactly the local and whole')
            g = analysis.axiom_gates(run, {'axiom_delta': {'L': delta(['Classical.choice']), 'W': delta()}}, 'synthetic')
            assert [(g[k]['allowlist'], g[k]['unchanged']) for k in ('local', 'whole')] == [(True, False), (True, True)]
            write_reports(run, ['propext', 'sorryAx'], all3)          # a foreign axiom, its delta recorded correctly
            g = analysis.axiom_gates(run, {'axiom_delta': {'L': delta(['sorryAx'], ['Quot.sound']), 'W': delta()}}, 'synthetic')
            assert (g['local']['allowlist'], g['local']['unchanged']) == (False, False)
            write_reports(run, ['propext'], all3)                     # a removal alone changes nothing
            g = analysis.axiom_gates(run, {'axiom_delta': {'L': delta((), ['Quot.sound']), 'W': delta()}}, 'synthetic')
            assert g['local']['allowlist'] and g['local']['unchanged'] and g['local']['delta'] == delta((), ['Quot.sound'])
            good = {'L': delta((), ['Quot.sound']), 'W': delta()}
            for kw in ({'accepted': False}, {'names': ('L', 'X')}, {'extra': [{'name': 'L2', 'axioms': []}]}):
                write_reports(run, ['propext'], all3, **kw); stops(run, good, 'kernel report')
            write_reports(run, 'propext', all3); stops(run, good, 'kernel report')
    finally:
        analysis.targets, analysis.original_axioms = saved


def test_axiom_gates_on_r6015_runs():
    """R6-015's sealed proofs (its records, not certificates), against the sites' frozen targets: none stops the function, and
    the unchanged gate fails exactly where R6-015 recorded acceptance 4 failing, at the targets whose originals lack
    `Classical.choice` (R6-016's proposal, section 2): the local target at l166 and l175, both targets at l096 and l099. The
    allowlist holds everywhere."""
    runs = R6/'r6-015-runs'
    proofs = 0
    for run in sorted(p for p in runs.iterdir() if p.is_dir()):
        verdict = r6.read_json(run/'verdict.json')
        if verdict['outcome'] != 'proved': continue
        proofs += 1
        g = analysis.axiom_gates(run, verdict, verdict['site'])
        site = verdict['site'].removeprefix('bracket-')
        assert all(x['allowlist'] for x in g.values()), run.name
        assert g['local']['unchanged'] is (site not in ('l096', 'l099', 'l166', 'l175')), (run.name, g['local'])
        assert g['whole']['unchanged'] is (site not in ('l096', 'l099')), (run.name, g['whole'])
    assert proofs == 74, proofs


if __name__ == '__main__':
    for test in (test_observations_are_r6015s, test_admission, test_labels, test_classify, test_audit_core, test_control9_evaluate,
                 test_axiom_gates, test_axiom_gates_on_r6015_runs):
        test(); print(test.__name__, 'passed')

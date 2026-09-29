#!/usr/bin/env python3
"""R6-014 controls for the deterministic comparison arm (`site_broker.py`).

Static: the bridge overlay is the R6-000 overlay plus only the listed observations; both capture helpers are the census helper with one
tactic line changed; the reference route's validation is the site validation with its one policy line changed; the frozen policy equals
its recomputation. Classifier: synthetic search records reach each outcome, first boundary first, and a process that was not clean is
never read as a mathematical outcome. Retained runs: every run is sealed and chained, bound to the frozen policy, its search outcome and
cost recomputed from its own evidence, and every proof's certificate check, closer receipt and both replays recomputed.
"""
import argparse
import difflib
import inspect
import json
from pathlib import Path
import shutil
import tempfile

import consumption_overlay
import events
import instrument
import run as r6
import site_broker as broker
import site_freeze
import site_network
import site_task
from test_proposals import Suite, require

CASES = '''overlay_is_observation_only helpers_change_one_tactic_line reference_validation_changes_one_policy_line policy_recomputes
classifier_reaches_each_outcome runs_bound_to_frozen_policy outcomes_and_costs_recomputed proofs_recomputed'''.split()


def controls(output):
    suite = Suite(output, CASES)

    def overlay():
        base = instrument.original('lean-bridge/ProofBroker/Tactic.lean').decode()
        frozen = instrument.lean_edits(base); ours = broker.lean_edits(base); undone = ours
        for old, new in (*consumption_overlay.EDITS, broker.REFERENCE_EDIT):
            require(undone.count(new) == 1 and frozen.count(old) == 1, 'edit applied once'); undone = undone.replace(new, old)
        require(undone == frozen, 'undoing the listed edits recovers the R6-000 overlay')
        added = [l[1:] for l in difflib.unified_diff(frozen.splitlines(), ours.splitlines(), lineterm='', n=0) if l.startswith('+') and not l.startswith('+++')]
        allowed = set(consumption_overlay.SELECTED.splitlines())
        calls = {'ext.polyFarkasCloser cert path.ir', 'ext.tier2CaseSplitCloser cert path.ir', 'pure (path, "term_mode_case_split")', 'ext.tier1FarkasCloser cert path.ir',
                 'pure (path, "term_mode_ext")', 'closeViaTermMode goal goalType cert', 'pure (path, "term_mode_int")', '| some ext =>',
                 'let closer ← closeOrFail goal goalType path', 'reportIfRequested "proof_broker" t0 path closer'}
        ok = lambda l: (l in allowed or l.strip() in calls or l.strip().startswith(('r6CloserSelected "', 'episodeEvent "closer_returned"', 'episodeEvent "reconstruction_finished"',
                        'episodeEvent "broker_closer_returned"', '("closer", toJson "term_mode_int")', '("derivation_replayed", toJson false)')))
        require(all(ok(l) for l in added), 'an added line is not an observation or a split existing call')
        require((broker.DEST/'bridge/ProofBroker/Tactic.lean').read_text() == ours, 'the built bridge is this text')
        for path in ('farkas_search.ml', 'adapter_cvc4.ml', 'dispatch.ml'):
            name = [p for p in r6.command(['git', '-C', instrument.REPO, 'ls-tree', '-r', '--name-only', instrument.BASE, 'sdk/lib']).splitlines() if p.endswith('/'+path)][0]
            require((broker.DEST/name).read_text() == instrument.sdk_edits(path, instrument.original(name).decode()), path+': the R6-000 SDK observations')
        return {'edits': len(consumption_overlay.EDITS)+1, 'added_lines': len(added)}
    suite.case('overlay_is_observation_only', overlay)

    def helpers():
        capture = site_freeze.CAPTURE.read_text(); out = {}
        for route, (name, tactic) in broker.ROUTES.items():
            helper = broker.capture_source(route)
            diff = [l for l in difflib.unified_diff(capture.splitlines(), helper.splitlines(), lineterm='', n=0) if l[:1] in '+-' and l[:3] not in ('+++', '---')]
            require(sorted(diff) == sorted(['+import ProofBroker', '-elab "r6_capture_human" savedName:str siteId:str : tactic => withMainContext do',
                             f'+elab "{name}" savedName:str siteId:str : tactic => withMainContext do', '-  evalTactic (← `(tactic| omega))',
                             '+  let adapter := mkIdent (Name.mkSimple "cvc4")', f'+  evalTactic (← `(tactic| {tactic} [$adapter:ident]))',
                             '-  unless (← getGoals).isEmpty do throwError "R6 human proof left goals"',
                             '+  unless (← getGoals).isEmpty do throwError "R6 broker proof left goals"']), f'{route}: {diff}')
            out[route] = tactic
        return out
    suite.case('helpers_change_one_tactic_line', helpers)

    def reference_line():
        frozen = inspect.getsource(site_network.final_validation).splitlines(); ours = inspect.getsource(broker.reference_validation).splitlines()
        diff = [l for l in difflib.unified_diff(frozen, ours, lineterm='', n=0) if l[:1] in '+-' and l[:3] not in ('+++', '---')]
        require(sorted(diff) == sorted(['-def final_validation(run, challenge, solution, checker, expected, task):',
                                        '+def reference_validation(run, challenge, solution, checker, expected, task):',
                                        "-    for name, config in [('local', local_policy(task)), ('whole', r6.policy([task.whole], True,task=task))]:",
                                        "+    for name, config in [('local', r6.policy([task.local], task=task)), ('whole', r6.policy([task.whole], True,task=task))]:"]), str(diff))
        return {'changed': diff}
    suite.case('reference_validation_changes_one_policy_line', reference_line)

    def policy():
        frozen = broker.verify()
        require(frozen['arm'] == broker.ARM and frozen['manifest_order'] == ['cvc4'] and frozen['attempt_limit'] == 1 and frozen['solver']['argv'] == broker.SOLVER_ARGV
                and frozen['budgets'] == broker.BUDGETS and frozen['sites'] == list(site_task.primary()) and frozen['model_calls'] == 0)
        return {'policy_sha256': r6.sha(broker.POLICY), 'solver': frozen['solver']['version'].split('\n')[0]}
    suite.case('policy_recomputes', policy)

    def synthetic():
        """Each branch of `classify`, from records that reach exactly that boundary."""
        site = site_task.get('bracket-l070'); results = {}
        chain = ['reification_started', 'reification_finished', 'dispatch_started', 'solver_started', 'solver_finished', 'recovery_started', 'recovery_finished',
                 'certificate_created', 'certificate_bound', 'selection_decided', 'dispatch_returned', 'dispatch_received', 'certificate_verification_started',
                 'certificate_verification_finished', 'reconstruction_started', 'closer_selected', 'residual_started', 'residual_finished', 'reconstruction_finished']
        cert = {'tier': 1, 'format': 'farkas', 'payload': {'witness_data': {}}}
        data = {'solver_finished': {'stdout': 'unsat\n', 'exit_code': 0}, 'dispatch_received': {'certificate': cert, 'final_ir': {}, 'trace': {}},
                'certificate_verification_finished': {'ok': True, 'envelope_ok': True, 'certificate': cert}, 'closer_selected': {'closer': 'term_mode_nat', 'certificate': cert, 'goal': 'g', 'comparison_type': 'ℕ'},
                'reconstruction_finished': {'closer': 'term_mode_nat', 'certificate': cert, 'certificate_consumed': True}, 'recovery_finished': {'route': 'bounded_enumeration', 'ok': True},
                'selection_decided': {'attempts': []}, 'broker_closer_returned': {'closer': 'gated_omega', 'certificate': cert}}
        clean = {'exit_code': 0, 'resource_exhausted': None, 'resource_violations': [], 'monitor_error': None, 'observation_error': None}
        def record(name, stop, route=broker.ARM, changes=None, process=None, failed=False, log=''):
            with tempfile.TemporaryDirectory(prefix='r6-014-classify-') as temp:
                run = Path(temp)/'run'; run.mkdir(); (run/'stages/search').mkdir(parents=True)
                events.append(run, 'episode', 'episode_started', {}, task_id=site.id)
                names = chain[:chain.index(stop)+1] if stop else []
                if route == broker.REFERENCE: names = [n for n in names if n not in ('reconstruction_started', 'closer_selected', 'residual_started', 'residual_finished', 'reconstruction_finished')] + (['broker_closer_returned'] if stop == 'reconstruction_finished' else [])
                for n in names:
                    events.append(run, 'search', n, {'component': 'lean_bridge', 'data': {**data.get(n, {}), **(changes or {}).get(n, {})}}, 'child_report')
                r6.write_json(run/'stages/search/search.process.json', {**clean, **(process or {})}); (run/'stages/search/search.stderr').write_text(log)
                got = broker.classify(run, route, failed)['outcome']
                require(got == name, f'{name}: classified {got}'); results[name] = got
        record('search_resources_or_monitor', 'reconstruction_finished', process={'resource_exhausted': 'wall'})
        record('reification_failed', None, failed=True, log='/input/Frozen.lean:1:1: error: reify\n')
        record('not_dispatched', 'reification_finished', failed=True)
        record('backend_not_invoked', 'dispatch_started', failed=True)
        record('solver_did_not_refute', 'solver_finished', changes={'solver_finished': {'stdout': 'sat\n'}}, failed=True)
        record('witness_not_recovered', 'reconstruction_finished', changes={'dispatch_received': {'certificate': {**cert, 'tier': 0}}}, failed=True)
        record('certificate_not_verified', 'certificate_verification_finished', changes={'certificate_verification_finished': {'ok': False}}, failed=True)
        record('reconstruction_not_started', 'reconstruction_started', failed=True)
        record('reconstruction_refused', 'closer_selected', failed=True)
        record('consumption_receipt_inconsistent', 'reconstruction_finished', changes={'reconstruction_finished': {'closer': 'term_mode_int'}})
        record('consumed', 'reconstruction_finished')
        record('closed', 'reconstruction_finished', route=broker.REFERENCE)
        record('closer_failed', 'certificate_verification_finished', route=broker.REFERENCE, failed=True)
        return results
    suite.case('classifier_reaches_each_outcome', synthetic)

    summary = r6.read_json(broker.RUNS/'deterministic.json'); frozen = r6.read_json(broker.POLICY)
    runs = [(route, site, broker.RUNS/route/site) for route in (broker.ARM, broker.REFERENCE) for site in summary['sites']]

    def bound():
        for route, site, run in runs:
            rows = events.read(run/'events.ndjson'); seal = r6.read_json(run/'seal.json')
            require(seal['event_count'] == len(rows) and seal['last_event_hash'] == rows[-1]['event_hash'] and all(r6.sha(run/k) == v for k, v in seal['retained_sha256'].items()), f'{site}: seal')
            require(rows[0]['payload']['policy_sha256'] == summary['policy_sha256'] == r6.sha(broker.POLICY) and (run/'provenance'/broker.POLICY.name).read_bytes() == broker.POLICY.read_bytes()
                    and r6.read_json(run/'search-policy.json')['lock_sha256'] == r6.sha(broker.LOCK), f'{site}: policy binding')
            require((run/'input/BrokerCapture.lean').read_text() == broker.capture_source(route)
                    and (run/'input/Frozen.lean').read_text() == site_task.instrumented(site_task.get(site), 'BrokerCapture', broker.ROUTES[route][0]), f'{site}: inputs')
            require(sorted(summary['sites']) == sorted(site_task.primary()), 'all fifteen sites')
        return {'runs': len(runs), 'sites': len(summary['sites'])}
    suite.case('runs_bound_to_frozen_policy', bound)

    def outcomes():
        table = {}
        for route, site, run in runs:
            outcome = r6.read_json(run/'outcome.json'); process = r6.read_json(run/'stages/search/search.process.json')
            failed = not (process['exit_code'] == 0 and not process['resource_exhausted'] and not process['resource_violations'] and not process['monitor_error'] and not process['observation_error'])
            again = broker.classify(run, route, failed)
            downstream = {'proof', 'closed_and_validated', 'independent_check_rejected'} | {f'{s}_failed' for s in ('certificate-check', 'export', 'validation-local', 'validation-whole')}
            require(again['outcome'] == outcome['outcome'] or (outcome['outcome'] in downstream and again['outcome'] in ('consumed', 'closed')), f'{route}/{site}: {again["outcome"]} vs {outcome["outcome"]}')
            require({k: v for k, v in again.items() if k not in ('outcome', 'certificate')} == {k: outcome[k] for k in again if k not in ('outcome', 'certificate')}, f'{site}: outcome fields')
            require(outcome['resources'] == broker.resources(run) and summary['results'][route][site] == outcome, f'{site}: cost and summary')
            table.setdefault(route, {}).setdefault(outcome['outcome'], []).append(site)
        return table
    suite.case('outcomes_and_costs_recomputed', outcomes)

    def proofs():
        checked = []
        for route, site, run in runs:
            outcome = r6.read_json(run/'outcome.json')
            if outcome['outcome'] not in ('proof', 'closed_and_validated'): continue
            verdict = r6.read_json(run/'verdict.json'); task = site_task.get(site); _, expected = site_task.frozen_site(task)
            observed = {r['event']: r['payload']['data'] for r in broker.children(run)}
            for kind, target in (('local', task.local), ('whole', task.whole)):
                report = verdict['final_validation'][kind]
                require(report['accepted'] is True and report['targets'][0]['name'] == target and verdict['axiom_delta'][target] == {'added': [], 'removed': []}, f'{site}: {kind}')
            if route == broker.ARM:
                packet = r6.read_json(run/'evidence.json')
                require(observed['reconstruction_finished'] == {'certificate': packet['certificate'], 'closer': verdict['closer'], 'certificate_consumed': True,
                                                               'derivation_replayed': False, 'residual_closer': 'omega'} and verdict['certificate_validation']['accepted'] is True
                        and r6.read_json(run/'certificate-verdict.json') == verdict['certificate_validation'], f'{site}: consumption and independent check')
            else:
                require(observed['broker_closer_returned']['closer'] == verdict['closer'], f'{site}: reference closer')
            checked.append(f'{route}/{site}')
        return {'validated': checked}
    suite.case('proofs_recomputed', proofs)
    suite.finish()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    controls(args.output)


if __name__ == '__main__':
    main()

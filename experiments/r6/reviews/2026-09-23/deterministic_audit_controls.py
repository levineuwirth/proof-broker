#!/usr/bin/env python3
"""Controls for the R6-014 deterministic-arm artifact auditor (`deterministic_audit.py`).

Each control mutates a fresh copy of the retained runs (`census-runs/deterministic-v1`) in one relationship and, where the relationship is
guarded by the chain and seal, re-chains and re-seals the copy with the production `site_network.seal`, as a coherent forger would; the
copy must be rejected at exactly the named case. The baseline copy must be accepted. Included: the review's two probes (an empty population;
l070's local type digest zeroed with the verdict, outcome, summary, terminal event and seal re-bound) and a raw report changed coherently.

Revision 2 (R6-014 revision 2 review): the review's probes — a zero witness at every certificate-bearing observation of a refused run
(whose packet the independent checker is first shown to reject), a relabelled closer on a refused run, a verification observation carrying
another certificate on a proof, a non-empty search workload, a proof exit code other than zero, and another site's export substituted
for a proof's solution — each coherently re-chained and re-sealed.

Revision 3 (R6-014 revision 3 review): every export stdout removed (the state of a clean checkout) must be accepted; under that same
retained-only condition another site's substituted solution must still be rejected; the zero-witness control now also rewrites the nested
certificate copies in `certificate_bound`, so that its only failure is the independent checker's.
"""
import argparse
import gzip
import json
from pathlib import Path
import shutil
import sys
import tempfile
from unittest.mock import patch
import importlib.util

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import events
import run as r6
import site_broker as broker
import site_network

spec = importlib.util.spec_from_file_location('r6_014_deterministic_audit', Path(__file__).with_name('deterministic_audit.py'))
audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
ARM, REF = broker.ARM, broker.REFERENCE
PROOF, REFUSED, REF_PROOF = f'{ARM}/bracket-l070', f'{ARM}/bracket-l166', f'{REF}/bracket-l069'
EXPECTED = {
    'empty_population': 'population:exactly_fifteen_sites_by_two_routes',
    'summary_sites_emptied': 'population:summary_bound',
    'run_missing': 'population:exactly_fifteen_sites_by_two_routes',
    'extra_run': 'population:exactly_fifteen_sites_by_two_routes',
    'local_type_zeroed_resealed': f'{PROOF}:kernel:derived_from_raw_reports',
    'raw_type_changed_coherently': f'{PROOF}:kernel:derived_from_raw_reports',
    'raw_axiom_added_coherently': f'{PROOF}:kernel:derived_from_raw_reports',
    'validation_policy_unbound_resealed': f'{PROOF}:kernel:derived_from_raw_reports',
    'certificate_verdict_forged_resealed': f'{PROOF}:proof:certificate_check_reexecuted',
    'evidence_packet_altered_resealed': f'{PROOF}:proof:evidence_rebuilt_from_observations',
    'consumption_receipt_altered_resealed': f'{PROOF}:proof:consumption_receipt',
    'reference_closer_relabelled_resealed': f'{REF_PROOF}:search:fields_recomputed',
    'search_outcome_relabelled_resealed': f'{REFUSED}:search:outcome_recomputed',
    'stage_budget_raised_resealed': f'{PROOF}:commands:rebuilt_by_the_stage_function',
    'sandbox_flag_removed_resealed': f'{REFUSED}:commands:rebuilt_by_the_stage_function',
    'stage_receipt_differs_from_process': f'{REFUSED}:commands:rebuilt_by_the_stage_function',
    'manifest_altered_resealed': f'{REFUSED}:inputs:recomputed',
    'harness_copy_altered_resealed': f'{REFUSED}:provenance:locked_sources_and_overlay',
    'binary_digest_altered_resealed': f'{REFUSED}:provenance:binaries_at_current_tool_digests',
    'verdict_on_rejected_run_resealed': f'{REFUSED}:search:downstream_exactly_when_proved',
    'rejected_run_terminal_finished': f'{REFUSED}:chain:expected_sequence',
    'retained_file_changed_unsealed': f'{REFUSED}:seal:every_retained_file_at_its_digest',
    'unlisted_file_added': f'{REFUSED}:seal:every_retained_file_at_its_digest',
    'solution_replaced_resealed': f'{PROOF}:proof:solution_bound',
    'summary_cost_changed': f'{PROOF}:outcome:record_bound',
    # revision 2
    'refused_zero_witness_resealed': f'{REFUSED}:search:observations_bound',
    'refused_closer_relabelled_resealed': f'{REFUSED}:search:observations_bound',
    'verification_observation_certificate_altered_resealed': f'{PROOF}:search:observations_bound',
    'search_workload_not_emptied_resealed': f'{PROOF}:search:terminated_cleanly',
    'proof_search_exit_nonzero_resealed': f'{PROOF}:search:terminated_cleanly',
    'solution_from_other_site_resealed': f'{PROOF}:proof:solution_bound',
    # revision 3
    'solution_from_other_site_stdout_absent_resealed': f'{PROOF}:proof:solution_bound',
}
ACCEPTED = ('export_stdout_absent',)  # must be accepted
ZERO_WITNESS = [{'hypothesis': 'neg_goal', 'coefficient': '0'}]
PRECONDITIONS = {}  # recorded positive preconditions of the controls that need one
CONTROLS = ('baseline', *EXPECTED)
TOOLS = []


def J(p): return json.loads(Path(p).read_bytes())
def W(p, v): r6.write_json(p, v)


def rechain(run, rows):
    previous = events.ZERO
    for row in rows:
        row.pop('event_hash', None); row['previous_hash'] = previous; row['event_hash'] = events.digest(row); previous = row['event_hash']
    (run/'events.ndjson').write_bytes(b''.join(events.canonical(row)+b'\n' for row in rows))


def rebind(root, name, change_rows=None):
    """After a change inside `name`: the outcome's digests, the summary entry, the terminal receipt, the chain and the seal, re-bound."""
    run = root/name; route, site = name.split('/')
    rows = events.read(run/'events.ndjson')
    if change_rows: change_rows(rows)
    outcome = J(run/'outcome.json')
    if outcome.get('verdict_sha256'): outcome['verdict_sha256'] = r6.sha(run/'verdict.json')
    W(run/'outcome.json', outcome)
    summary = J(root/'deterministic.json'); summary['results'][route][site] = outcome; W(root/'deterministic.json', summary)
    rows[-1]['payload'] = {'outcome_sha256': r6.sha(run/'outcome.json'), 'outcome': outcome['outcome']}
    rechain(run, rows); accepted = J(run/'seal.json')['accepted']; site_network.seal(run, accepted)


def receipt(rows, stage, event):
    return next(r for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event)


def child(rows, event):
    return next(r for r in rows if r['source'] == 'child_report' and r['event'] == event)


def raw_change(root, name, kind, change):
    """Rewrite a raw replay report, then carry it coherently into the verdict and its kernel receipt, as `final_validation` would."""
    import hashlib
    run = root/name; path = run/f'validation-{kind}.raw.json.gz'
    report = json.loads(gzip.open(path).read()); change(report)
    with gzip.open(path, 'wb') as f: f.write(json.dumps(report).encode())
    normalized = json.loads(json.dumps(report)); t = normalized['targets'][0]
    t['type_sha256'] = hashlib.sha256(t.pop('type_repr').encode()).hexdigest(); t['type_hash_format'] = 'Lean-4.32.2-reprStr-Expr-UTF8'
    verdict = J(run/'verdict.json'); verdict['final_validation'][kind] = normalized
    W(run/'verdict.json', verdict)
    def rows_change(rows): receipt(rows, 'validation-'+kind, 'kernel_verdict')['payload'] = normalized
    return rows_change


def mutate(name, root):
    if name == 'empty_population':  # the review's probe: an empty summary and no run trees
        summary = J(root/'deterministic.json'); summary['sites'] = []; summary['results'] = {}; W(root/'deterministic.json', summary)
        shutil.rmtree(root/ARM); shutil.rmtree(root/REF)
    elif name == 'summary_sites_emptied':
        summary = J(root/'deterministic.json'); summary['sites'] = []; W(root/'deterministic.json', summary)
    elif name == 'run_missing': shutil.rmtree(root/ARM/'bracket-l204')
    elif name == 'extra_run': shutil.copytree(root/ARM/'bracket-l204', root/ARM/'bracket-l205')
    elif name == 'local_type_zeroed_resealed':  # the review's probe, verbatim in effect
        run = root/PROOF; verdict = J(run/'verdict.json'); verdict['final_validation']['local']['targets'][0]['type_sha256'] = '0'*64; W(run/'verdict.json', verdict)
        rebind(root, PROOF)
    elif name == 'raw_type_changed_coherently':
        def change(report): report['targets'][0]['type_repr'] = report['targets'][0]['type_repr'].replace('Nat', 'Int', 1)
        rebind(root, PROOF, raw_change(root, PROOF, 'local', change))
    elif name == 'raw_axiom_added_coherently':
        def change(report): report['targets'][0]['axioms'] = report['targets'][0]['axioms']+['sorryAx']
        rows_change = raw_change(root, PROOF, 'whole', change)
        verdict = J(root/PROOF/'verdict.json'); target = verdict['final_validation']['whole']['targets'][0]['name']
        verdict['axiom_delta'][target] = {'added': ['sorryAx'], 'removed': []}; W(root/PROOF/'verdict.json', verdict)
        rebind(root, PROOF, rows_change)
    elif name == 'validation_policy_unbound_resealed':
        p = root/PROOF/'validation-input/local/policy.json'; value = J(p); value['required_dependency'] = None; W(p, value); rebind(root, PROOF)
    elif name == 'certificate_verdict_forged_resealed':
        run = root/PROOF; forged = {**J(run/'certificate-verdict.json'), 'checked_rows': 999}
        W(run/'certificate-verdict.json', forged); verdict = J(run/'verdict.json'); verdict['certificate_validation'] = forged; W(run/'verdict.json', verdict)
        rebind(root, PROOF, lambda rows: receipt(rows, 'certificate-check', 'independent_certificate_verdict').__setitem__('payload', forged))
    elif name == 'evidence_packet_altered_resealed':
        run = root/PROOF; packet = J(run/'evidence.json'); packet['trace'] = {'altered': True}; W(run/'evidence.json', packet); rebind(root, PROOF)
    elif name == 'consumption_receipt_altered_resealed':
        rebind(root, PROOF, lambda rows: child(rows, 'reconstruction_finished')['payload']['data'].__setitem__('residual_closer', 'none'))
    elif name == 'reference_closer_relabelled_resealed':
        rebind(root, REF_PROOF, lambda rows: child(rows, 'broker_closer_returned')['payload']['data'].__setitem__('closer', 'term_mode_nat'))
    elif name == 'search_outcome_relabelled_resealed':
        run = root/REFUSED; outcome = J(run/'outcome.json'); outcome['outcome'] = 'backend_not_invoked'; W(run/'outcome.json', outcome); rebind(root, REFUSED)
    elif name == 'stage_budget_raised_resealed':
        p = root/PROOF/'stages/search/command.json'; value = J(p); value['wall_seconds'] = 1500; W(p, value); rebind(root, PROOF)
    elif name == 'sandbox_flag_removed_resealed':
        p = root/REFUSED/'stages/search/command.json'; value = J(p); value['argv'].remove('--unshare-all'); W(p, value); rebind(root, REFUSED)
    elif name == 'stage_receipt_differs_from_process':
        p = root/REFUSED/'stages/search/search.process.json'; value = J(p); value['wall_seconds'] += 1; W(p, value)
        outcome = J(root/REFUSED/'outcome.json'); outcome['resources'] = broker.resources(root/REFUSED); W(root/REFUSED/'outcome.json', outcome); rebind(root, REFUSED)
    elif name == 'manifest_altered_resealed':
        p = root/REFUSED/'manifests/manifest-cvc4.json'; value = J(p); value['altered'] = True; W(p, value); rebind(root, REFUSED)
    elif name == 'harness_copy_altered_resealed':
        p = root/REFUSED/'provenance/harness/site_task.py'; p.write_text(p.read_text()+'\n# altered\n'); rebind(root, REFUSED)
    elif name == 'binary_digest_altered_resealed':
        p = root/REFUSED/'provenance/binaries.json'; value = J(p); key = next(k for k in value if k.endswith('/cvc4')); value[key] = '0'*64; W(p, value); rebind(root, REFUSED)
    elif name == 'verdict_on_rejected_run_resealed':
        shutil.copyfile(root/PROOF/'verdict.json', root/REFUSED/'verdict.json'); rebind(root, REFUSED)
    elif name == 'rejected_run_terminal_finished':
        def finished(rows): rows[-1]['event'] = 'episode_finished'
        rebind(root, REFUSED, finished)
    elif name == 'retained_file_changed_unsealed':
        p = root/REFUSED/'input/source.patch'; p.write_text(p.read_text()+'\n')
    elif name == 'unlisted_file_added':
        (root/REFUSED/'note.txt').write_text('unlisted\n')
    elif name == 'solution_replaced_resealed':
        p = root/PROOF/'solution.ndjson.gz'
        with gzip.open(p, 'ab') as f: f.write(b'\n')
        rebind(root, PROOF)
    elif name == 'refused_zero_witness_resealed':
        def change(rows):
            count = 0
            for row in rows:
                cert = row['payload'].get('data', {}).get('certificate')
                if cert and cert.get('tier') == 1 and cert.get('format') == 'farkas':
                    cert['payload']['witness_data']['coefficients'] = ZERO_WITNESS; count += 1
                if row['event'] == 'certificate_bound':  # revision 3: the nested copies too, so that only the checker can object
                    for side in ('before', 'after'): row['payload']['data'][side]['payload']['witness_data']['coefficients'] = ZERO_WITNESS
            assert count >= 3
        rebind(root, REFUSED, change)
        rows = events.read(root/REFUSED/'events.ndjson'); data = {r['event']: r['payload']['data'] for r in rows if r['source'] == 'child_report'}
        packet = {'certificate': data['dispatch_received']['certificate'], 'input_ir': data['dispatch_started']['ir'],
                  'final_ir': data['dispatch_received']['final_ir'], 'trace': data['dispatch_received']['trace']}
        check = audit.verifier_on_packet(TOOLS[0], packet); assert check['accepted'] is False, check  # the precondition: the checker rejects it
        PRECONDITIONS[name] = {'independent_check_accepted': check['accepted'], 'reason': check.get('reason') or check.get('error')}
    elif name == 'refused_closer_relabelled_resealed':
        outcome = J(root/REFUSED/'outcome.json'); outcome['closer'] = 'term_mode_int'; W(root/REFUSED/'outcome.json', outcome)
        rebind(root, REFUSED, lambda rows: child(rows, 'closer_selected')['payload']['data'].__setitem__('closer', 'term_mode_int'))
    elif name == 'verification_observation_certificate_altered_resealed':
        rebind(root, PROOF, lambda rows: child(rows, 'certificate_verification_finished')['payload']['data']['certificate']['payload']['witness_data'].__setitem__('coefficients', ZERO_WITNESS))
    elif name in ('search_workload_not_emptied_resealed', 'proof_search_exit_nonzero_resealed'):
        p = root/PROOF/'stages/search/search.process.json'; process = J(p)
        if name == 'search_workload_not_emptied_resealed': process['workload_empty_after_cleanup'] = False
        else: process['exit_code'] = 7
        W(p, process); rebind(root, PROOF, lambda rows: receipt(rows, 'search', 'stage_finished').__setitem__('payload', process))
    elif name in ('export_stdout_absent', 'solution_from_other_site_stdout_absent_resealed'):
        for stdout in root.glob('*/*/stages/export/export.stdout'): stdout.unlink()  # a clean checkout: the ignored file is absent
        if name == 'solution_from_other_site_stdout_absent_resealed':
            import hashlib
            with gzip.open(broker.RUNS/ARM/'bracket-l069/solution.ndjson.gz', 'rb') as f: other = f.read()
            with gzip.open(root/PROOF/'solution.ndjson.gz', 'wb') as f: f.write(other)
            verdict = J(root/PROOF/'verdict.json'); verdict['solution_sha256'] = hashlib.sha256(other).hexdigest(); W(root/PROOF/'verdict.json', verdict)
            seal = J(root/PROOF/'seal.json'); ephemeral = seal['ephemeral_sha256']
            rebind(root, PROOF); seal = J(root/PROOF/'seal.json'); seal['ephemeral_sha256'].update(ephemeral); W(root/PROOF/'seal.json', seal)  # the recorded digest kept
    elif name == 'solution_from_other_site_resealed':
        import hashlib
        with gzip.open(broker.RUNS/ARM/'bracket-l069/solution.ndjson.gz', 'rb') as f: other = f.read()
        with gzip.open(root/PROOF/'solution.ndjson.gz', 'wb') as f: f.write(other)
        verdict = J(root/PROOF/'verdict.json'); verdict['solution_sha256'] = hashlib.sha256(other).hexdigest(); W(root/PROOF/'verdict.json', verdict); rebind(root, PROOF)
    elif name == 'summary_cost_changed':
        summary = J(root/'deterministic.json'); summary['results'][ARM]['bracket-l070']['resources']['wall_seconds'] += 1; W(root/'deterministic.json', summary)
    else: raise AssertionError(name)


def run_audit(root):
    try: result = audit.audit(root)
    except audit.Rejection as rejection: return {'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)[:400]}
    return {'accepted': True, 'case_count': result['case_count']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--only', nargs='*', help='trial: these controls only; the record requires the full population')
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    tools = broker.tools_for(ROOT.parents[1]/'lean-bridge/.lake/packages')  # built once; every audit uses these
    TOOLS.append(tools)
    results = {}
    with patch.object(broker, 'tools_for', lambda packages: tools):
        for name in (*CONTROLS, *ACCEPTED):
            if args.only and name not in args.only and name != 'baseline': continue
            with tempfile.TemporaryDirectory(prefix='r6-014-det-controls-') as temp:
                root = Path(temp)/'runs'; shutil.copytree(broker.RUNS, root)
                if name != 'baseline': mutate(name, root)
                observed = run_audit(root)
                if name in ('baseline', *ACCEPTED): assert observed['accepted'] is True, observed
                else: assert observed['accepted'] is False and observed['rejected_case'] == EXPECTED[name], (name, observed)
                results[name] = observed; print(name, observed.get('rejected_case') or observed, flush=True)
    if args.only: print(json.dumps({'trial': True, 'controls': len(results)})); return
    assert tuple(results) == (*CONTROLS, *ACCEPTED)
    r6.write_json(args.output, {'passed': True, 'controls': len(results), 'results': results, 'baseline_cases': results['baseline']['case_count'], 'preconditions': PRECONDITIONS,
                                'auditor_sha256': r6.sha(Path(__file__).with_name('deterministic_audit.py')), 'program_sha256': r6.sha(Path(__file__)),
                                'scope': 'temporary copies; one relationship per mutation; coherent re-chaining and re-sealing where the relationship is sealed'})
    print(json.dumps({'passed': True, 'controls': len(results)}, indent=1))


if __name__ == '__main__':
    main()

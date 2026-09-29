#!/usr/bin/env python3
"""Controls for the R6-014 cohort v7 auditor, in both modes.

Rehearsal mode: the approved R6-013 control population (`reviews/2026-09-22/cohort_v6_audit_controls.py`, 101 controls at revision 3),
run unchanged against the v7 auditor and the v7 canned runs, which have the same population and order as v6's.

Live mode: one relationship per mutation on a fresh copy of the live-shaped fixture (`fixtures/r6-014-live-shaped`, SYNTHETIC), which first
passes the unmutated live audit; the mutated copy must be rejected at exactly the named case. Records that later records commit to are
re-finalized with the production `finalize(..., live=True)`. Covered: the signed policy (by its recorded bytes) and its checkpoint (altered or missing: the signed state alone); scope (a run outside the signed
schedule); an outcome without a reviewed live audit (fails closed); the commitment, the use receipt and a claimed exact receipt; a local
receiver, a received body, a fixture mount, --unshare-net in the sender or an unshared namespace recorded or a credential inside the tree in a live record; a claimed publication
acceptance; the live ledger; each operator-scan binding (a missing or unbound receipt, a disclosure, a scan before the runs finished, an
uncovered file, a changed commitment domain); and a verifier acceptance on the negative control.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import cohort_episode as driver
import credential
import events
import run as r6

spec = importlib.util.spec_from_file_location('r6_014_cohort_audit', Path(__file__).with_name('cohort_v7_audit.py'))
audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
base_spec = importlib.util.spec_from_file_location('r6_013_controls_for_v7', ROOT/'reviews/2026-09-22/cohort_v6_audit_controls.py')
base = importlib.util.module_from_spec(base_spec); base_spec.loader.exec_module(base)
base.audit = audit  # the approved population, audited by the v7 auditor in rehearsal mode
J, W = base.J, base.W
FIXTURE = ROOT/'fixtures/r6-014-live-shaped'
FIRST, LAST, NEG = 'l069-draw1', 'l204-draw1', 'l170-draw1'
LIVE_EXPECTED = {
    'live_policy_unsigned': f'{FIRST}:versions:policy_lock_contract_campaign_bound',
    'live_checkpoint_altered': f'{FIRST}:versions:policy_lock_contract_campaign_bound',
    'live_checkpoint_missing': 'revision:superseded_v6_bound',
    'live_run_outside_signed_schedule': 'population:within_authorized_schedule',
    'live_unreviewed_outcome_fails_closed': 'population:derived_from_evidence',
    'live_commitment_forged_in_receipt': f'{LAST}:commitment:bound_to_mounted_canary',
    'live_exact_receipt_claimed': f'{LAST}:credential_receipt:recorded',
    'live_local_receiver_recorded': f'{LAST}:transport:local_send_and_remote_receipt',
    'live_received_body_present': f'{LAST}:transport:bodies_are_the_contract_rendering',
    'live_fixture_mount_in_sender': f'{LAST}:command:reconstructed_from_pinned_runtime_and_layout',
    'live_unshare_net_in_sender': f'{LAST}:command:reconstructed_from_pinned_runtime_and_layout',
    'live_unshared_network_recorded': f'{LAST}:command:reconstructed_from_pinned_runtime_and_layout',
    'live_credential_inside_tree': f'{LAST}:command:reconstructed_from_pinned_runtime_and_layout',
    'live_publication_acceptance_claimed': f'{LAST}:terminal:commitments_bound',
    'live_ledger_terminal_row_removed': 'ledger:continuous_single_revision',
    'live_negative_control_accepted': f'{NEG}:witness_rejected:recomputed_invalid_and_stopped',
    'operator_receipt_missing': f'{FIRST}:operator_scan:receipt_bound',
    'operator_receipt_commitment_unbound': f'{FIRST}:operator_scan:receipt_bound',
    'operator_receipt_seal_stale': f'{FIRST}:operator_scan:receipt_bound',
    'operator_report_disclosure': 'operator_scan:report_bound',
    'operator_scan_before_runs_finished': 'operator_scan:report_bound',
    'operator_inventory_uncovered_file': 'operator_scan:report_bound',
    'operator_commitment_domain_changed': 'operator_scan:report_bound',
}


def live_paths(temp):
    f = temp/'fixture'; shutil.copytree(FIXTURE, f)
    audit.configure('live', str((FIXTURE/'runs').relative_to(ROOT)), f/'policies', str((FIXTURE/'ledgers/campaigns').relative_to(ROOT)),
                    f/'operator-disclosure-scan.json', synthetic=True)
    audit.LAYOUT['scan_root'] = f
    return f


def run_live(f):
    try: result = audit.audit(f/'runs', f/'ledgers/campaigns')
    except audit.Rejection as rejection: return {'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}
    return {'accepted': result['accepted'], 'case_count': result['case_count']}


def refinalize_live(run, change):
    rows = events.read(run/'events.ndjson'); rows.pop(); change(run, rows); base.rechain(run, rows)
    for n in ('publication-scan.json', 'publication-final.json', 'seal.json'): (run/n).unlink()
    nonce = J(run/'credential-canary.json')['nonce']
    driver.finalize(run, credential.derive(nonce), nonce, J(run/'credential-summary.json'), True)


def event(rows, name, stage=None):
    matches = [r for r in rows if r['event'] == name and (stage is None or r['stage'] == stage) and r['source'] == 'supervisor']
    assert len(matches) == 1, (name, len(matches)); return matches[0]['payload']


def mutate_live(name, f):
    runs = f/'runs'; report = f/'operator-disclosure-scan.json'
    def report_change(change):
        value = J(report); change(value); report.write_text(json.dumps(value, sort_keys=True, indent=1)+'\n')
    if name == 'live_policy_unsigned':
        shutil.copyfile(f/'policies'/audit.CHECKPOINT, f/'policies'/audit.POLICY)
    elif name == 'live_checkpoint_altered':
        base.change_json(f/'policies', audit.CHECKPOINT, lambda v: v.__setitem__('scope', v['scope']+' altered'))
    elif name == 'live_checkpoint_missing':
        (f/'policies'/audit.CHECKPOINT).unlink()
    elif name == 'live_run_outside_signed_schedule':
        shutil.copytree(runs/FIRST, runs/'l069-draw2'); base.change_json(runs/'l069-draw2', 'search-policy.json', lambda v: v.__setitem__('draw', 2))
    elif name == 'live_unreviewed_outcome_fails_closed':
        refinalize_live(runs/LAST, lambda run, rows: base.change_json(run, 'credential-summary.json', lambda v: v.__setitem__('failure_category', 'credential_format')))
    elif name == 'live_commitment_forged_in_receipt':
        def change(run, rows):
            base.change_json(run, 'credential-receipt.json', lambda v: v.__setitem__('credential_commitment_sha256', '0'*64))
            receipt = event(rows, 'credential_use_checked'); receipt['credential_commitment_sha256'] = '0'*64
        refinalize_live(runs/LAST, change)
    elif name == 'live_exact_receipt_claimed':
        def change(run, rows):
            base.change_json(run, 'credential-receipt.json', lambda v: v.__setitem__('exact_receipt', True))
            event(rows, 'credential_use_checked')['exact_receipt'] = True
        refinalize_live(runs/LAST, change)
    elif name == 'live_local_receiver_recorded':
        refinalize_live(runs/LAST, lambda run, rows: base.change_json(run, 'stages/proposal-1/output/server.json', lambda v: v['requests'].append({'body_sha256': '0'*64})))
    elif name == 'live_received_body_present':
        refinalize_live(runs/LAST, lambda run, rows: shutil.copyfile(run/'stages/proposal-1/output/outbound-body.json', run/'stages/proposal-1/output/received-body.json'))
    elif name in ('live_fixture_mount_in_sender', 'live_unshare_net_in_sender', 'live_unshared_network_recorded', 'live_credential_inside_tree'):
        def alter(v):
            argv = v['argv']
            if name == 'live_fixture_mount_in_sender': argv[argv.index('/ca.pem')+1:argv.index('/ca.pem')+1] = ['--ro-bind', v['run']+'/canned-provider.json', '/fixture.json']
            elif name == 'live_unshare_net_in_sender': argv.insert(argv.index('--unshare-user')+1, '--unshare-net')
            elif name == 'live_unshared_network_recorded': v['network_namespace'] = 'unshared'
            else: argv[argv.index('/credential')-1] = v['run']+'/credential'
        refinalize_live(runs/LAST, lambda run, rows: base.change_json(run, 'stages/proposal-1/command.json', alter))
    elif name == 'live_publication_acceptance_claimed':
        run = runs/LAST; rows = events.read(run/'events.ndjson'); rows[-1]['payload']['publication_accepted'] = True; rows[-1]['payload']['publication_pending'] = False
        base.rechain(run, rows); driver.network.seal(run, False)
    elif name == 'live_ledger_terminal_row_removed':
        campaign = J(runs/FIRST/'search-policy.json')['campaign_id']; book = f/'ledgers/campaigns'/campaign/'live'
        rows = [json.loads(l) for l in (book/'ledger.ndjson').read_bytes().splitlines()]
        base.rewrite_ledger(book, campaign, [r for r in rows if not (r['kind'] in audit.ledger.TERMINAL and r.get('episode_id') == FIRST)])
    elif name == 'live_negative_control_accepted':
        def change(run, rows):
            base.change_json(run, 'certificate-verdict.json', lambda v: v.__setitem__('accepted', True))
            event(rows, 'independent_certificate_verdict')['accepted'] = True
        refinalize_live(runs/NEG, change)
    elif name == 'operator_receipt_missing':
        report_change(lambda v: v['operator_scan'].__setitem__('run_receipts', [r for r in v['operator_scan']['run_receipts'] if r['run']['name'] != FIRST]))
    elif name == 'operator_receipt_commitment_unbound':
        report_change(lambda v: [r.__setitem__('commitment_bound', False) for r in v['operator_scan']['run_receipts'] if r['run']['name'] == FIRST])
    elif name == 'operator_receipt_seal_stale':
        report_change(lambda v: [r.__setitem__('seal_sha256', '0'*64) for r in v['operator_scan']['run_receipts'] if r['run']['name'] == FIRST])
    elif name == 'operator_report_disclosure':
        report_change(lambda v: v['disclosures'].append({'path_sha256': '0'*64}))
    elif name == 'operator_scan_before_runs_finished':
        report_change(lambda v: v['operator_scan'].__setitem__('evaluated_at_unix', 1))
    elif name == 'operator_inventory_uncovered_file':
        report_change(lambda v: v.__setitem__('inventory', [e for e in v['inventory'] if not (e['path'] or '').startswith(f'runs/{FIRST}/evidence.json')]))
    elif name == 'operator_commitment_domain_changed':
        report_change(lambda v: v['operator_scan'].__setitem__('commitment_domain', 'another-domain'))
    else: raise AssertionError(name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--only', nargs='*', help='trial: run only these controls; the record requires the full population')
    parser.add_argument('--live-only', action='store_true', help='trial: skip the rehearsal population')
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    rehearsal, live = {}, {}
    if not args.live_only:
        audit.configure('rehearsal')
        for name in base.CONTROLS:
            if args.only and name not in args.only and name != 'baseline': continue
            with tempfile.TemporaryDirectory(prefix='r6-014-controls-') as temp:
                temp = Path(temp); paths = {k: temp/k for k in ('runs', 'ledgers', 'representability', 'v4', 'v5')}
                shutil.copytree(ROOT/audit.RUNS, paths['runs']); shutil.copytree(ROOT/'ledgers/campaigns', paths['ledgers'])
                shutil.copytree(ROOT/audit.REPRESENTABILITY, paths['representability'])
                shutil.copytree(ROOT/audit.HISTORY_V4['runs'], paths['v4']); shutil.copytree(ROOT/audit.HISTORY_V5['runs'], paths['v5'])
                baseline = base.run_audit(paths); assert baseline['accepted'] is True, baseline
                if name == 'baseline': rehearsal[name] = baseline; print('rehearsal', name, baseline, flush=True); continue
                if name == 'audit_case_removed':
                    original = audit.Audit.require
                    def omit(self, ok, case, detail=''):
                        if case == f'{base.NAT}:proof:shared_checker': return
                        return original(self, ok, case, detail)
                    with base.patch.object(audit.Audit, 'require', omit): observed = base.run_audit(paths)
                else:
                    base.mutate(name, paths); observed = base.run_audit(paths)
                assert observed['accepted'] is False and observed['rejected_case'] == base.EXPECTED[name], (name, observed)
                rehearsal[name] = {'rejected': True, 'rejected_case': observed['rejected_case']}; print('rehearsal', name, observed['rejected_case'], flush=True)
    for name in ('baseline', *LIVE_EXPECTED):
        if args.only and name not in args.only and name != 'baseline': continue
        with tempfile.TemporaryDirectory(prefix='r6-014-live-controls-') as temp:
            f = live_paths(Path(temp)); baseline = run_live(f); assert baseline['accepted'] is True, baseline
            if name == 'baseline': live[name] = baseline; print('live', name, baseline, flush=True); continue
            mutate_live(name, f); observed = run_live(f)
            assert observed['accepted'] is False and observed['rejected_case'] == LIVE_EXPECTED[name], (name, observed)
            live[name] = {'rejected': True, 'rejected_case': observed['rejected_case']}; print('live', name, observed['rejected_case'], flush=True)
    if args.only or args.live_only:
        print(json.dumps({'trial': True, 'rehearsal': len(rehearsal), 'live': len(live)})); return
    assert tuple(rehearsal) == base.CONTROLS and tuple(live) == ('baseline', *LIVE_EXPECTED)
    r6.write_json(args.output, {'passed': True, 'rehearsal_controls': len(rehearsal), 'live_controls': len(live), 'rehearsal': rehearsal, 'live': live,
        'rehearsal_population': 'reviews/2026-09-22/cohort_v6_audit_controls.py (approved at R6-013 revision 3), run against the v7 auditor and runs',
        'rehearsal_baseline_cases': rehearsal['baseline']['case_count'], 'live_baseline_cases': live['baseline']['case_count'],
        'auditor_sha256': r6.sha(Path(__file__).with_name('cohort_v7_audit.py')), 'program_sha256': r6.sha(Path(__file__)),
        'live_fixture_sha256': r6.sha(FIXTURE/'FIXTURE.json'), 'live_model_calls': 0, 'credentials_read': 0,
        'scope': 'temporary copies; one relationship per mutation; exact control populations; the live fixture is synthetic'})
    print(json.dumps({'passed': True, 'rehearsal_controls': len(rehearsal), 'live_controls': len(live)}, indent=1))


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Controls for the R6-014 revision 3 cohort v9 auditor (`cohort_v9_audit.py`), in both modes; the revision 2 controls (retained) carried to
v9 and its fixture (`fixtures/r6-014-v3-live-revisions`), with the revision 2 review's controls: the progress floor missing or behind; the
review's compressed `.bin` reported as raw-only, with the frozen scanner first shown to find its gzip disclosures; a non-run file changed
after the scan; a miscounted gzip total.

The revision 2 description follows.

Controls for the R6-014 revision 2 cohort v8 auditor (`cohort_v8_audit.py`), in both modes; derived from the v7 controls (retained).

Revision 2 (R6-014 review): the live fixture is `fixtures/r6-014-v2-live-revisions` (the production signing layout, a distinct admitted
capture, then an authorization and a pricing revision). Added: the review's per-entry scan probes and further entry relationships
(finding 3); the review's signed-production-policy probe and a guard that no production policy file is read, both of which must be accepted;
the revision history, its captures and the activation receipt (finding 2). Live case names follow the v8 auditor.

The v7 description follows.

Controls for the R6-014 cohort v7 auditor, in both modes.

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
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import cohort_episode as driver
import credential
import events
import run as r6

spec = importlib.util.spec_from_file_location('r6_014_v3_cohort_audit', Path(__file__).with_name('cohort_v9_audit.py'))
audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
base_spec = importlib.util.spec_from_file_location('r6_013_controls_for_v9', ROOT/'reviews/2026-09-22/cohort_v6_audit_controls.py')
base = importlib.util.module_from_spec(base_spec); base_spec.loader.exec_module(base)
base.audit = audit  # the approved population, audited by the v7 auditor in rehearsal mode
J, W = base.J, base.W
FIXTURE = ROOT/'fixtures/r6-014-v3-live-revisions'
OPERATOR_NONCE = 'f'*62+'14'  # the fixture's one synthetic operator credential (live_shape)
FIRST, LAST, NEG = 'l069-draw1', 'l204-draw1', 'l170-draw1'
LIVE_EXPECTED = {
    'live_policy_unsigned': 'revision:history_bound',  # v8: the revision history is read first, from the configured layout
    'live_checkpoint_altered': 'revision:history_bound',
    'live_checkpoint_missing': 'revision:history_bound',
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
    'live_ledger_terminal_row_removed': 'ledger:continuous_across_revisions',
    'live_negative_control_accepted': f'{NEG}:witness_rejected:recomputed_invalid_and_stopped',
    'operator_receipt_missing': f'{FIRST}:operator_scan:receipt_bound',
    'operator_receipt_commitment_unbound': f'{FIRST}:operator_scan:receipt_bound',
    'operator_receipt_seal_stale': f'{FIRST}:operator_scan:receipt_bound',
    'operator_report_disclosure': 'operator_scan:report_bound',
    'operator_scan_before_runs_finished': 'operator_scan:report_bound',
    'operator_inventory_uncovered_file': 'operator_scan:report_bound',
    'operator_commitment_domain_changed': 'operator_scan:report_bound',
    # revision 2: finding 3, each entry relationship
    'operator_entry_scanned_false': 'operator_scan:report_bound',
    'operator_entry_error_present': 'operator_scan:report_bound',
    'operator_entry_finding_present': 'operator_scan:report_bound',
    'operator_entry_duplicated': 'operator_scan:report_bound',
    'operator_entry_gzip_stream_missing': 'operator_scan:report_bound',
    'operator_files_scanned_miscounted': 'operator_scan:report_bound',
    # revision 2: finding 2, the revision history, its captures and the activation receipt
    'revision_retained_missing': 'revision:history_bound',
    'revision_retained_altered': 'revision:history_bound',
    'revision_authority_rolled_back': 'revision:history_bound',
    'revision_outside_plan': 'revision:history_bound',
    'revision_pricing_admission_unbound': 'revision:runtime_pricing_ledger_publication_bound',
    'revision_capture_substituted': 'revision:runtime_pricing_ledger_publication_bound',
    'activation_receipt_missing': 'revision:history_bound',
    'activation_receipt_altered': 'ledger:continuous_across_revisions',
    'ledger_revision_row_removed': 'ledger:continuous_across_revisions',
    'run_retained_policy_swapped': f'{LAST}:versions:policy_lock_contract_campaign_bound',
    # revision 3: the revision 2 review
    'progress_floor_missing': 'revision:history_bound',
    'progress_floor_behind': 'ledger:continuous_across_revisions',
    'compressed_disclosure_bin_reported_raw': 'operator_scan:report_bound',
    'inventory_file_changed_after_scan': 'operator_scan:report_bound',
    'gzip_stream_total_miscounted': 'operator_scan:report_bound',
}
PRECONDITIONS = {}
ACCEPTED_PROBES = ('production_policy_file_signed', 'production_policy_files_unread')  # must be accepted


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
    elif name.startswith('operator_entry_') or name == 'operator_files_scanned_miscounted':
        def entry_change(v):
            inventory = v['inventory']; i = next(i for i, e in enumerate(inventory) if e['path'] == f'runs/{FIRST}/accounting.json')
            if name == 'operator_entry_scanned_false': inventory[i]['scanned'] = False  # the review's probe
            elif name == 'operator_entry_error_present': inventory[i]['error'] = 'synthetic unreadable stream'  # the review's probe
            elif name == 'operator_entry_finding_present': inventory[i]['findings'] = [{'stream': 'raw', 'form': 'token:utf-8', 'offset': 0}]  # the review's probe
            elif name == 'operator_entry_duplicated': inventory.append(dict(inventory[i]))
            elif name == 'operator_entry_gzip_stream_missing':
                j = next(j for j, e in enumerate(inventory) if e['path'].endswith('.gz')); inventory[j]['streams'] = ['raw']
            else: v['files_scanned'] += 1
        report_change(entry_change)
    elif name.startswith('revision_') or name.startswith('activation_receipt_'):
        d = f/'policies'; stem = audit.POLICY.removesuffix('.json')
        paths = {1: d/f'{stem}.r1.json', 2: d/f'{stem}.r2.json', 3: d/audit.POLICY}
        def rewrite(k, change):  # one revision changed; each later revision re-chained to it, as a coherent forger would
            value = J(paths[k]); change(value); W(paths[k], value)
            for later in range(k+1, 4):
                after = J(paths[later]); after['previous_policy_sha256'] = r6.sha(paths[later-1]); W(paths[later], after)
        if name == 'revision_retained_missing': paths[1].unlink()
        elif name == 'revision_retained_altered':
            value = J(paths[2]); value['revision_reason'] += ' (altered)'; W(paths[2], value)
        elif name == 'revision_authority_rolled_back':
            rewrite(2, lambda v: v['authorization'].__setitem__('approved_utc', '2026-09-22T20:00:00Z'))
        elif name == 'revision_outside_plan':
            def beyond(v):
                v['authorization']['schedule']['bracket-l069'] = 9; v['campaign']['schedule']['bracket-l069'] = 9
                slots = sum(v['campaign']['schedule'].values()); v['authorization']['maximum_micro_usd'] = v['limits']['total_micro_usd'] = slots*audit.contract.ATTEMPT_MICRO_USD
                v['live_model_calls_authorized'] = slots
            rewrite(2, beyond)
        elif name == 'revision_pricing_admission_unbound':  # a recorded admission that is not its capture's recomputed review
            rewrite(2, lambda v: v['pricing_admission']['sources']['model'].__setitem__('raw_sha256', '0'*64))
        elif name == 'revision_capture_substituted':  # the revision names another retained capture than the one it was admitted with
            rewrite(2, lambda v: v.__setitem__('pricing_sources', 'sources/pricing-approved-campaign-2'))
        elif name == 'activation_receipt_missing': (d/audit.ACTIVATION).unlink()
        elif name == 'activation_receipt_altered': base.change_json(d, audit.ACTIVATION, lambda v: v.__setitem__('activation_row_hash', '0'*64))
        else: raise AssertionError(name)
    elif name == 'progress_floor_missing': (f/'policies'/audit.FLOOR).unlink()
    elif name == 'progress_floor_behind':  # the floor one row back, as a restored older floor would be
        campaign = J(runs/FIRST/'search-policy.json')['campaign_id']; rows = [json.loads(l) for l in (f/'ledgers/campaigns'/campaign/'live/ledger.ndjson').read_bytes().splitlines()]
        base.change_json(f/'policies', audit.FLOOR, lambda v: v.update(rows=len(rows)-1, last_hash=rows[-2]['row_hash']))
    elif name == 'compressed_disclosure_bin_reported_raw':  # the review's probe: gzip bytes under a non-.gz name
        import gzip, publication
        token = credential.derive(OPERATOR_NONCE); extra = f/'compressed-disclosure.bin'; extra.write_bytes(gzip.compress(credential.header(token).encode()))
        entry = publication.scan_file(extra, publication.patterns(token), f)
        assert 'gzip' in entry['streams'] and any(x['stream'] == 'gzip' for x in entry['findings']) and not any(x['stream'] == 'raw' for x in entry['findings'])
        PRECONDITIONS[name] = {'scanner_streams': entry['streams'], 'gzip_findings': sum(x['stream'] == 'gzip' for x in entry['findings']),
                               'raw_findings': sum(x['stream'] == 'raw' for x in entry['findings'])}
        entry.update(streams=['raw'], findings=[], root_index=0)
        report_change(lambda v: (v['inventory'].append(entry), v.__setitem__('files_scanned', v['files_scanned']+1)))
    elif name == 'inventory_file_changed_after_scan':
        p = f/'captures/signing/model.html'; p.write_bytes(p.read_bytes()+b'\n')
    elif name == 'gzip_stream_total_miscounted': report_change(lambda v: v.__setitem__('gzip_streams_scanned', v['gzip_streams_scanned']+1))
    elif name == 'ledger_revision_row_removed':
        campaign = J(runs/FIRST/'search-policy.json')['campaign_id']; book = f/'ledgers/campaigns'/campaign/'live'
        rows = [json.loads(l) for l in (book/'ledger.ndjson').read_bytes().splitlines()]
        last = max(i for i, r in enumerate(rows) if r['kind'] == 'authorization_revision')
        base.rewrite_ledger(book, campaign, rows[:last]+rows[last+1:])
    elif name == 'run_retained_policy_swapped':  # the last run was reserved under revision 3; its retained policy claims revision 1
        stem = audit.POLICY.removesuffix('.json')
        shutil.copyfile(f/'policies'/f'{stem}.r1.json', runs/LAST/'provenance/cohort-harness/policies'/audit.POLICY)
    else: raise AssertionError(name)


def probe(name, f):
    """The acceptance probes: the audit reads the configured layout only, whatever the production policy directory holds."""
    import builtins, pathlib
    production = {ROOT/'policies'/n for n in (audit.POLICY, audit.CHECKPOINT, audit.ACTIVATION)} | set((ROOT/'policies').glob(audit.POLICY.removesuffix('.json')+'.r*.json'))
    if name == 'production_policy_file_signed':  # the review's probe: the production policy read as the signed one
        original = audit.load
        def signed(path):
            return original(f/'policies'/audit.POLICY) if Path(path) == ROOT/'policies'/audit.POLICY else original(path)
        with patch.object(audit, 'load', signed): return run_live(f)
    guarded = lambda path: Path(path).resolve() in {p.resolve() for p in production}
    read_bytes, read_text, opened = pathlib.Path.read_bytes, pathlib.Path.read_text, builtins.open
    def rb(self, *a, **k):
        if guarded(self): raise PermissionError('production policy file read: '+str(self))
        return read_bytes(self, *a, **k)
    def rt(self, *a, **k):
        if guarded(self): raise PermissionError('production policy file read: '+str(self))
        return read_text(self, *a, **k)
    def op(file, *a, **k):
        if isinstance(file, (str, Path)) and guarded(file): raise PermissionError('production policy file read: '+str(file))
        return opened(file, *a, **k)
    with patch.object(pathlib.Path, 'read_bytes', rb), patch.object(pathlib.Path, 'read_text', rt), patch.object(builtins, 'open', op): return run_live(f)


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
    for name in ACCEPTED_PROBES:
        if args.only and name not in args.only: continue
        with tempfile.TemporaryDirectory(prefix='r6-014-live-probes-') as temp:
            f = live_paths(Path(temp)); observed = probe(name, f)
            assert observed['accepted'] is True, (name, observed)
            live[name] = observed; print('live', name, observed, flush=True)
    if args.only or args.live_only:
        print(json.dumps({'trial': True, 'rehearsal': len(rehearsal), 'live': len(live)})); return
    assert tuple(rehearsal) == base.CONTROLS and tuple(live) == ('baseline', *LIVE_EXPECTED, *ACCEPTED_PROBES)
    r6.write_json(args.output, {'passed': True, 'rehearsal_controls': len(rehearsal), 'live_controls': len(live), 'rehearsal': rehearsal, 'live': live,
        'rehearsal_population': 'reviews/2026-09-22/cohort_v6_audit_controls.py (approved at R6-013 revision 3), run against the v8 auditor and runs',
        'accepted_probes': list(ACCEPTED_PROBES), 'preconditions': PRECONDITIONS,
        'rehearsal_baseline_cases': rehearsal['baseline']['case_count'], 'live_baseline_cases': live['baseline']['case_count'],
        'auditor_sha256': r6.sha(Path(__file__).with_name('cohort_v9_audit.py')), 'program_sha256': r6.sha(Path(__file__)),
        'live_fixture_sha256': r6.sha(FIXTURE/'FIXTURE.json'), 'live_model_calls': 0, 'credentials_read': 0,
        'scope': 'temporary copies; one relationship per mutation; exact control populations; the live fixture is synthetic'})
    print(json.dumps({'passed': True, 'rehearsal_controls': len(rehearsal), 'live_controls': len(live)}, indent=1))


if __name__ == '__main__':
    main()

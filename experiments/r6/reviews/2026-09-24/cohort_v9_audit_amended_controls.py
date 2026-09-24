#!/usr/bin/env python3
"""Controls for R6-014 amendment 1 (`cohort_v9_audit_amended.py`). SYNTHETIC evidence only; the collected block 1 is not read.

1. The frozen live control population (`reviews/2026-09-23/cohort_v9_audit_controls.py`: 51 live records) runs unchanged against the
   amended auditor on the isolated fixture, each with the same outcome.
2. The isolated fixture keeps its accepted case population: the amended auditor evaluates exactly the cases, all true, of the frozen record
   `R6-014-V4-LIVE-FIXTURE-AUDIT.json`.

3. The production directory layout, exercised with the synthetic fixture: a shared policy directory holding every unrelated file of the
   production `policies/` (never the production campaign's own files) beside the fixture campaign's files. It must be accepted, and so must
   an unrelated look-alike name. It must be rejected for a missing required file, an unexpected campaign revision, an unexpected
   campaign-specific file (for the policy's prefix and, separately, the source lock's), and altered bindings (a retained revision, the
   activation receipt).

Not re-executed: the rehearsal-mode audit and its 101 controls. They presuppose the pre-signing production tree (a disabled policy, a
rehearsal-only ledger directory, a single-revision rehearsal ledger), which signing changed by design; the amended predicate is reached only
in live mode (`revision_history` returns before it otherwise), so the rehearsal path is byte-identical to the frozen auditor's.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent; R6 = HERE.parents[1]
sys.path.insert(0, str(R6))
import run as r6

spec = importlib.util.spec_from_file_location('r6_014_amended_audit', HERE/'cohort_v9_audit_amended.py'); amended = importlib.util.module_from_spec(spec); spec.loader.exec_module(amended)
spec = importlib.util.spec_from_file_location('r6_014_v9_controls', R6/'reviews/2026-09-23/cohort_v9_audit_controls.py'); frozen = importlib.util.module_from_spec(spec); spec.loader.exec_module(frozen)
frozen.audit = amended; frozen.base.audit = amended  # the frozen control populations, evaluated by the amended auditor
FROZEN_RECORDS = {'live': R6/'reviews/2026-09-23/R6-014-V4-LIVE-FIXTURE-AUDIT.json'}
FROZEN_CONTROLS = R6/'reviews/2026-09-23/R6-014-V4-AUDIT-CONTROLS.json'
STEM, LOCK_STEM = amended.POLICY.removesuffix('.json'), amended.LOCK.removesuffix('.sha256.json')
SHARED = {  # name: expected rejected case, or None where the layout must be accepted
    'shared_directory_accepted': None,
    'shared_unrelated_lookalike_accepted': None,
    'shared_floor_missing': 'revision:history_bound',
    'shared_checkpoint_missing': 'revision:history_bound',
    'shared_unexpected_campaign_revision': 'revision:history_bound',
    'shared_unexpected_policy_prefixed_file': 'revision:history_bound',
    'shared_unexpected_lock_prefixed_file': 'revision:history_bound',
    'shared_retained_revision_altered': 'revision:history_bound',
    'shared_activation_receipt_altered': 'ledger:continuous_across_revisions',
}


def owned(name): return name in (amended.POLICY, amended.LOCK) or name.startswith(STEM+'.') or name.startswith(LOCK_STEM+'.')


def shared_directory(f, temp):
    """The production neighbours (every unrelated production policy file), then the synthetic campaign's own files."""
    d = temp/'shared-policies'; d.mkdir()
    for p in (R6/'policies').iterdir():
        if p.is_file() and not owned(p.name): shutil.copyfile(p, d/p.name)
    campaign = sorted(p.name for p in (f/'policies').iterdir())
    assert all(owned(n) for n in campaign)
    for n in campaign: shutil.copyfile(f/'policies'/n, d/n)
    return d, len(list(d.iterdir()))-len(campaign)


def mutate_shared(name, d):
    J = frozen.J; W = frozen.W
    if name == 'shared_unrelated_lookalike_accepted': shutil.copyfile(d/amended.POLICY, d/(STEM+'0.json'))  # `<stem>0.json` is not this campaign's
    elif name == 'shared_floor_missing': (d/amended.FLOOR).unlink()
    elif name == 'shared_checkpoint_missing': (d/amended.CHECKPOINT).unlink()
    elif name == 'shared_unexpected_campaign_revision': shutil.copyfile(d/f'{STEM}.r1.json', d/f'{STEM}.r7.json')
    elif name == 'shared_unexpected_policy_prefixed_file': shutil.copyfile(d/amended.POLICY, d/(amended.POLICY+'.bak'))
    elif name == 'shared_unexpected_lock_prefixed_file': shutil.copyfile(d/amended.LOCK, d/(LOCK_STEM+'.sha256.json.orig'))
    elif name == 'shared_retained_revision_altered':
        value = J(d/f'{STEM}.r2.json'); value['revision_reason'] += ' (altered)'; W(d/f'{STEM}.r2.json', value)
    elif name == 'shared_activation_receipt_altered':
        value = J(d/amended.ACTIVATION); value['activation_row_hash'] = '0'*64; W(d/amended.ACTIVATION, value)


def cases_of(record): return json.loads(record.read_bytes())['cases']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--only', nargs='*', help='trial: these controls only')
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    out = {'baselines': {}, 'shared': {}, 'live': {}}
    # 2. the isolated fixture, case by case against the frozen record
    with tempfile.TemporaryDirectory(prefix='r6-014-amended-') as temp:
        f = frozen.live_paths(Path(temp)); live = amended.audit(f/'runs', f/'ledgers/campaigns')
        assert live['cases'] == cases_of(FROZEN_RECORDS['live']) and live['accepted'], 'isolated fixture case population changed'
        out['baselines']['isolated_fixture'] = {'case_count': live['case_count'], 'identical_to': str(FROZEN_RECORDS['live'].relative_to(R6))}
    print('baselines', out['baselines'], flush=True)
    # 3. the production directory layout, synthetic evidence
    for name, expected in SHARED.items():
        if args.only and name not in args.only: continue
        with tempfile.TemporaryDirectory(prefix='r6-014-amended-shared-') as temp:
            temp = Path(temp); f = frozen.live_paths(temp); d, neighbours = shared_directory(f, temp)
            amended.LAYOUT['policies'] = d; mutate_shared(name, d); observed = frozen.run_live(f)
            if expected is None: assert observed['accepted'] is True, (name, observed)
            else: assert observed['accepted'] is False and observed['rejected_case'] == expected, (name, observed)
            out['shared'][name] = {**observed, 'unrelated_neighbours': neighbours}; print('shared', name, observed.get('rejected_case') or observed, flush=True)
    # 1. the frozen populations, unchanged outcomes
    if not args.only:
        recorded = json.loads(FROZEN_CONTROLS.read_bytes())
        for name in ('baseline', *frozen.LIVE_EXPECTED):
            with tempfile.TemporaryDirectory(prefix='r6-014-amended-live-') as temp:
                f = frozen.live_paths(Path(temp)); baseline = frozen.run_live(f); assert baseline['accepted'], baseline
                if name == 'baseline': out['live'][name] = baseline; continue
                frozen.mutate_live(name, f)
                if name in frozen.ESCAPES: observed, reads = frozen.reads_of_sentinel(lambda: frozen.run_live(f)); assert reads == [], (name, reads)
                else: observed = frozen.run_live(f)
                assert observed['accepted'] is False and observed['rejected_case'] == recorded['live'][name]['rejected_case'], (name, observed)
                out['live'][name] = {'rejected': True, 'rejected_case': observed['rejected_case']}; print('live', name, observed['rejected_case'], flush=True)
        for name in frozen.ACCEPTED_PROBES:
            with tempfile.TemporaryDirectory(prefix='r6-014-amended-probes-') as temp:
                f = frozen.live_paths(Path(temp)); observed = frozen.probe(name, f); assert observed['accepted'] is True, (name, observed); out['live'][name] = observed
        assert set(out['live']) == set(recorded['live']), 'population differs from the frozen record'
    if args.only: print(json.dumps({'trial': True, 'shared': len(out['shared'])})); return
    r6.write_json(args.output, {'passed': True, **out, 'shared_controls': len(out['shared']), 'live_controls': len(out['live']),
                                'not_reexecuted': 'the rehearsal-mode audit and its 101 controls: they presuppose the pre-signing tree; the amended predicate is live-only',
                                'amended_auditor_sha256': r6.sha(HERE/'cohort_v9_audit_amended.py'), 'frozen_auditor_sha256': r6.sha(R6/'reviews/2026-09-23/cohort_v9_audit.py'),
                                'program_sha256': r6.sha(Path(__file__)), 'collected_block_read': False,
                                'scope': 'synthetic evidence only; the collected block 1 is not read by these controls'})
    print(json.dumps({'passed': True, 'shared': len(out['shared']), 'live': len(out['live'])}, indent=1))


if __name__ == '__main__':
    main()

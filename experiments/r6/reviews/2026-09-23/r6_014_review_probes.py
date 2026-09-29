#!/usr/bin/env python3
"""Independent R6-014 review probes. Isolated synthetic authority only; no credential/network use."""
import argparse, contextlib, copy, importlib.util, io, json, shutil, sys, tempfile
from pathlib import Path
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT)); sys.dont_write_bytecode = True
import cohort_contract as contract
import test_cohort as tc
import test_analysis_r6 as ta
import analysis_r6 as analysis
import test_site_broker as tb
import site_broker as broker
import run as r6

def quick():
    results = {}
    capture = ROOT/'sources/pricing-approved-campaign-3'
    now = max(v['finished_unix'] for v in tc.v2.source_evidence(capture).values()) + 3600
    schedule = {s: 1 for s in contract.POSABLE}
    with tempfile.TemporaryDirectory(prefix='r6-014-review-sign-') as tmp:
        p = Path(tmp)
        with patch.object(contract, 'CONFIG', p/'policy.json'), patch.object(contract, 'LOCK', p/'lock.json'), patch.object(contract, 'CHECKPOINT', p/'checkpoint.json'), patch.object(contract, 'LEDGERS', p/'ledgers'):
            contract.freeze(capture)
            args = ('review-synthetic', '2026-09-22T21:00:00Z', schedule, capture, 'isolated review; no transmission')
            contract.sign(*args, now=now)
            c = contract.config(); book = contract.campaign_ledger(True, c)
            permit = tc.reserve(book,c,tc.D1,1); tc.with_grant(book,permit)
            book.reconcile(permit, tc.TERMINATED, tc.SENT, {})
            _, before = book.snapshot()
            try: tc.reserve(book,c,tc.D1,1); raise AssertionError('consumed baseline slot accepted')
            except tc.ledger.Failure as e: assert e.code == 'cohort_slot_consumed'
            book.directory.rename(p/'retained-established-live-ledger')
            contract.sign(*args, now=now)
            _, after = book.snapshot()
            again = tc.reserve(book, c, tc.D1, 1)
            results['missing_established_live_ledger'] = {'baseline_consumed_slot_refused': True, 'consumed_before': before['transmissions_consumed'], 'consumed_after_resigning': after['transmissions_consumed'], 'same_slot_reserved_again': again['task_id'] == tc.D1 and again['draw'] == 1}
    slots = {f'{s}/1': ta.realistic(s) for s in ta.POPS['posed']}
    for v in slots.values(): v['usage'] = dict.fromkeys(('input_tokens','output_tokens','cached_tokens'))
    results['all_usage_unreported'] = ta.run(slots)['costs']
    x = ta.realistic('bracket-l069'); x['usage'] = {'input_tokens':1,'cached_tokens':1,'output_tokens':0}
    results['fractional_micro_cost'] = ta.run({'bracket-l069/1':x})['costs']
    slots = {f'{s}/1':ta.realistic(s) for s in ta.POPS['posed']}
    neg = slots['bracket-l170/1']; neg['reconstruction']['consumed'] = True
    r = ta.run(slots)
    results['negative_verifier_false_consumer_true'] = {k:r[k] for k in ('negative_control','integrity_stop','continue_permitted')}
    results['negative_verifier_false_consumer_true']['reported_consumed'] = r['per_slot']['bracket-l170/1']['consumed']
    results['rejected_proposal_counted_as_witness'] = r['arms']['learned']['by_site']['bracket-l170']['distinct_witnesses']
    cl = copy.deepcopy(ta.CLASSIFICATION); cl['classes']['posable_certificate'].remove('bracket-l096')
    slots.pop('bracket-l096/1'); neg['reconstruction']['consumed'] = None
    data = ta.collection(slots,{s:1 for s in ta.POPS['posed'] if s!='bracket-l096'})
    data['campaign']['planned_schedule'].pop('bracket-l096')
    results['classification_drops_feasible_site'] = analysis.analyse(data,ta.DETERMINISTIC,cl,ta.RATES)['denominators']
    with tempfile.TemporaryDirectory(prefix='r6-014-review-det-') as tmp:
        p = Path(tmp); original = r6.read_json(broker.RUNS/'deterministic.json')
        with contextlib.redirect_stdout(io.StringIO()): tb.controls(p/'baseline.json')
        original['sites'] = []; r6.write_json(p/'deterministic.json',original)
        with patch.object(broker,'RUNS',p), contextlib.redirect_stdout(io.StringIO()): tb.controls(p/'empty.json')
        results['empty_deterministic_run_population'] = {'baseline':r6.read_json(p/'baseline.json'), 'mutated':r6.read_json(p/'empty.json')}
    return results

def deterministic():
    import events
    import site_network
    result = {}
    with tempfile.TemporaryDirectory(prefix='r6-014-review-det-proof-') as tmp:
        p = Path(tmp); copied = p/'runs'; shutil.copytree(broker.RUNS,copied)
        run = copied/broker.ARM/'bracket-l070'
        verdict = r6.read_json(run/'verdict.json')
        old = verdict['final_validation']['local']['targets'][0]['type_sha256']
        verdict['final_validation']['local']['targets'][0]['type_sha256'] = '0'*64
        r6.write_json(run/'verdict.json', verdict)
        outcome = r6.read_json(run/'outcome.json'); outcome['verdict_sha256'] = r6.sha(run/'verdict.json'); r6.write_json(run/'outcome.json',outcome)
        summary = r6.read_json(copied/'deterministic.json'); summary['results'][broker.ARM]['bracket-l070'] = outcome; r6.write_json(copied/'deterministic.json',summary)
        rows = events.read(run/'events.ndjson'); rows[-1]['payload']['outcome_sha256'] = r6.sha(run/'outcome.json')
        previous = events.ZERO
        for row in rows:
            row.pop('event_hash'); row['previous_hash']=previous; row['event_hash']=events.digest(row); previous=row['event_hash']
        (run/'events.ndjson').write_bytes(b''.join(events.canonical(row)+b'\n' for row in rows))
        site_network.seal(run,True)
        with patch.object(broker,'RUNS',copied), contextlib.redirect_stdout(io.StringIO()): tb.controls(p/'controls.json')
        result = {'changed_type_from':old,'changed_type_to':'0'*64,'outcome_summary_terminal_seal_rebound':True,'controls':r6.read_json(p/'controls.json')}
    return result

def live():
    spec = importlib.util.spec_from_file_location('review_live_controls',Path(__file__).with_name('cohort_v7_audit_controls.py'))
    m = importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    results = {}
    with tempfile.TemporaryDirectory(prefix='r6-014-review-live-') as tmp:
        f = m.live_paths(Path(tmp)); a = m.audit
        results['baseline'] = m.run_live(f); assert results['baseline']['accepted']
        original_load = a.load
        def signed_production_read(path):
            path = Path(path)
            if path == a.ROOT/'policies'/a.POLICY: return original_load(f/'policies'/a.POLICY)
            return original_load(path)
        with patch.object(a,'load',signed_production_read): results['production_policy_is_signed'] = m.run_live(f)
        report_path = f/'operator-disclosure-scan.json'; report = m.J(report_path)
        entry_index = next(i for i,e in enumerate(report['inventory']) if e.get('path') and e['path'].startswith('runs/'))
        results['operator_entry_schema'] = copy.deepcopy(report['inventory'][entry_index])
        for name, change in [('scanned_false', {'scanned':False}), ('error_non_null',{'error':'synthetic unreadable stream'}),
                             ('finding_present',{'findings':[{'stream':'raw','form':'token:utf-8','offset':0}]})]:
            mutated = copy.deepcopy(report); mutated['inventory'][entry_index].update(change); m.W(report_path,mutated)
            results['operator_entry_'+name] = m.run_live(f)
        m.W(report_path,report)
    # Real signing function, a distinct admissible copy of the existing capture; no new external price claim.
    capture = ROOT/'sources/pricing-approved-campaign-3'
    now = max(v['finished_unix'] for v in tc.v2.source_evidence(capture).values())+3600
    with tempfile.TemporaryDirectory(prefix='r6-014-review-capture-',dir=ROOT/'.cache') as capdir, tempfile.TemporaryDirectory(prefix='r6-014-review-authority-') as tmp:
        copied = Path(capdir)/'capture'; shutil.copytree(capture,copied); p=Path(tmp)
        with patch.object(contract,'CONFIG',p/a.POLICY), patch.object(contract,'LOCK',p/contract.LOCK.name), patch.object(contract,'CHECKPOINT',p/a.CHECKPOINT), patch.object(contract,'LEDGERS',p/'ledgers'):
            contract.freeze(capture)
            contract.sign('review-synthetic','2026-09-22T21:00:00Z',{s:1 for s in contract.POSABLE},copied,'isolated capture-binding review',now=now)
            with patch.dict(a.LAYOUT,{'policies':p}):
                results['distinct_admissible_capture'] = {'production_sign_succeeded':True, 'signed_state_ok':a.signed_state_ok(contract.config()), 'same_source_bytes':True}
    return results

if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('mode',choices=['quick','live','deterministic']); parser.add_argument('--output',type=Path,required=True); args=parser.parse_args()
    assert not args.output.exists()
    result = globals()[args.mode]()
    args.output.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps({'mode':args.mode,'output':str(args.output)}))

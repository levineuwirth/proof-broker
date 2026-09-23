#!/usr/bin/env python3
"""Independent v2 review. Temporary synthetic authority and coherently resealed copies only."""
import argparse, copy, importlib.util, json, shutil, sys, tempfile
from pathlib import Path
from unittest.mock import patch
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
import cohort_contract as contract
import test_cohort as tc
import run as r6
import events

def load_module(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def authority():
    capture=ROOT/'sources/pricing-approved-campaign-3';now=max(v['finished_unix'] for v in tc.v2.source_evidence(capture).values())+3600
    with tempfile.TemporaryDirectory(prefix='r6-014-v2-authority-') as tmp:
        p=Path(tmp)
        with patch.object(contract,'CONFIG',p/'policy.json'),patch.object(contract,'LOCK',p/'lock.json'),patch.object(contract,'CHECKPOINT',p/'checkpoint.json'),patch.object(contract,'LEDGERS',p/'ledgers'):
            contract.freeze(capture)
            args=('review-synthetic','2026-09-22T21:00:00Z',{s:1 for s in contract.POSABLE},capture,'isolated rollback review, no transmission')
            contract.sign(*args,now=now);c=contract.config();book=contract.campaign_ledger(True,c)
            receipt=book.receipt.read_bytes();shutil.copytree(book.directory,p/'activation-only-snapshot')
            permit=tc.reserve(book,c,tc.D1,1);tc.with_grant(book,permit);book.reconcile(permit,tc.TERMINATED,tc.SENT,{})
            try:tc.reserve(book,c,tc.D1,1);raise AssertionError('spent baseline accepted')
            except tc.ledger.Failure as error:assert error.code=='cohort_slot_consumed'
            book.directory.rename(p/'spent-preserved')
            try:contract.sign(*args,now=now);raise AssertionError('lost authority accepted')
            except tc.ledger.Failure as error:assert error.code=='cohort_activation_authority_lost'
            shutil.copytree(p/'activation-only-snapshot',book.directory)
            assert book.receipt.read_bytes()==receipt
            _,s=contract.live_permitted(c);again=tc.reserve(book,c,tc.D1,1)
            return {'spent_slot_baseline_refused':True,'lost_directory_resign_refused':True,'activation_receipt_unchanged':True,'live_permitted_after_snapshot_rollback':True,
                    'consumed_after_rollback':s['transmissions_consumed'],'same_slot_reserved_again':again['task_id']==tc.D1 and again['draw']==1}

def deterministic(extra=False):
    m=load_module('v2_deterministic_controls','deterministic_audit_controls.py');a=m.audit
    tools=a.broker.tools_for(ROOT.parents[1]/'lean-bridge/.lake/packages');result={}
    def observe(root):
        try:return a.audit(root)
        except a.Rejection as e:return {'accepted':False,'rejected_case':e.case,'detail':str(e)}
    with tempfile.TemporaryDirectory(prefix='r6-014-v2-det-') as tmp:
        p=Path(tmp);original=a.broker.RUNS
        root=p/'baseline';shutil.copytree(original,root);result['baseline']=observe(root);assert result['baseline']['accepted']
        for label in (('proof_search_workload_live','proof_solution_other_site') if extra else ('refused_bad_certificate','refused_wrong_closer','proof_verification_receipt_wrong','proof_search_exit_nonzero','proof_solution_changed_coherently')):
            root=p/label;shutil.copytree(original,root)
            name=m.REFUSED if label.startswith('refused_') else m.PROOF;run=root/name
            if label=='refused_bad_certificate':
                def change(rows):
                    count=0
                    for row in rows:
                        d=row['payload'].get('data',{});cert=d.get('certificate')
                        if cert and cert.get('tier')==1 and cert.get('format')=='farkas':
                            cert['payload']['witness_data']['coefficients']=[{'hypothesis':'neg_goal','coefficient':'0'}];count+=1
                    assert count>=3
                m.rebind(root,name,change)
                rows=events.read(run/'events.ndjson');data={r['event']:r['payload']['data'] for r in rows if r['source']=='child_report'}
                packet={'certificate':data['dispatch_received']['certificate'],'input_ir':data['dispatch_started']['ir'],'final_ir':data['dispatch_received']['final_ir'],'trace':data['dispatch_received']['trace']}
                evidence=p/'invalid-evidence.json';m.W(evidence,packet);result['refused_bad_certificate_independent_check']=a.verifier_verdict(tools,evidence)
                assert result['refused_bad_certificate_independent_check']['accepted'] is False
            elif label=='refused_wrong_closer':
                def change(rows):m.child(rows,'closer_selected')['payload']['data']['closer']='term_mode_int'
                out=m.J(run/'outcome.json');out['closer']='term_mode_int';m.W(run/'outcome.json',out);m.rebind(root,name,change)
            elif label=='proof_verification_receipt_wrong':
                def change(rows):m.child(rows,'certificate_verification_finished')['payload']['data']['certificate']['payload']['witness_data']['coefficients']=[{'hypothesis':'neg_goal','coefficient':'0'}]
                m.rebind(root,name,change)
            elif label in ('proof_search_exit_nonzero','proof_search_workload_live'):
                proc=m.J(run/'stages/search/search.process.json');proc['exit_code' if label=='proof_search_exit_nonzero' else 'workload_empty_after_cleanup']=7 if label=='proof_search_exit_nonzero' else False;m.W(run/'stages/search/search.process.json',proc)
                m.rebind(root,name,lambda rows:m.receipt(rows,'search','stage_finished').__setitem__('payload',proc))
            else:
                import gzip,hashlib
                with gzip.open(run/'solution.ndjson.gz','rb') as f: solution=f.read()
                if label=='proof_solution_other_site':
                    with gzip.open(original/m.ARM/'bracket-l069/solution.ndjson.gz','rb') as f: other=f.read()
                    assert other!=solution;solution=other
                else:solution+=b'\n'
                with gzip.open(run/'solution.ndjson.gz','wb') as f:f.write(solution)
                verdict=m.J(run/'verdict.json');verdict['solution_sha256']=hashlib.sha256(solution).hexdigest();m.W(run/'verdict.json',verdict);m.rebind(root,name)
            result[label]=observe(root)
    return result

def deterministic_extra(): return deterministic(extra=True)

def live():
    import gzip
    import publication,credential
    m=load_module('v2_live_controls','cohort_v8_audit_controls.py');result={}
    with tempfile.TemporaryDirectory(prefix='r6-014-v2-live-review-') as tmp:
        f=m.live_paths(Path(tmp));result['baseline']=m.run_live(f);assert result['baseline']['accepted']
        p=f/'operator-disclosure-scan.json';original=m.J(p)
        for name in ('operator_entry_scanned_false','operator_entry_error_present','operator_entry_finding_present'):
            m.W(p,original);m.mutate_live(name,f);result[name]=m.run_live(f);assert not result[name]['accepted']
        m.W(p,original)
        token=credential.derive('f'*62+'14');extra=f/'compressed-disclosure.bin';extra.write_bytes(gzip.compress(credential.header(token).encode()))
        entry=publication.scan_file(extra,publication.patterns(token),f)
        assert 'gzip' in entry['streams'] and entry['findings']
        result['gzip_magic_precondition']={'suffix':extra.suffix,'streams':entry['streams'],'finding_count':len(entry['findings']), 'raw_has_findings':any(x['stream']=='raw' for x in entry['findings'])}
        entry.update(streams=['raw'],findings=[],root_index=0)
        report=copy.deepcopy(original);report['inventory'].append(entry);report['files_scanned']+=1;m.W(p,report)
        result['gzip_without_gz_suffix']=m.run_live(f)
    return result

def analysis():
    import test_analysis_r6 as t, analysis_r6 as a
    slots={f'{s}/1':t.realistic(s) for s in t.POPS['posed']};data=t.collection(slots)
    baseline=a.analyse(data,t.DETERMINISTIC,t.CLASSIFICATION,t.RATES)
    changed=copy.deepcopy(t.CLASSIFICATION);row=next(r for r in changed['results'] if r['site_id']=='bracket-l069');old=row['family'];row['family']='Review.synthetic_family'
    got=a.analyse(data,t.DETERMINISTIC,changed,t.RATES)
    return {'baseline_denominators':baseline['denominators'],'mutated_denominators':got['denominators'],'family_change':{'site':'bracket-l069','from':old,'to':row['family']},
            'baseline_families':list(baseline['families']), 'mutated_families':list(got['families']),
            'baseline_excluding_lift_cell_slots':baseline['sensitivities']['excluding_lift_cell']['slots'],'mutated_excluding_lift_cell_slots':got['sensitivities']['excluding_lift_cell']['slots'],
            'continue_permitted':got['continue_permitted']}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('mode',choices=['authority','deterministic','deterministic_extra','live','analysis']);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();assert not args.output.exists()
    result=globals()[args.mode]();args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'mode':args.mode,'output':str(args.output)}))

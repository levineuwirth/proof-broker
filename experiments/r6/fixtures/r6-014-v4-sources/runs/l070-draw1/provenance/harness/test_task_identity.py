"""Resealed mutations of task and recovery identity on disposable artifacts."""
import copy
import shutil

import events
import run as r6


def rehash(rows):
    previous=events.ZERO
    for i,row in enumerate(rows):
        row.pop('event_hash',None)
        row['sequence']=i
        row['previous_hash']=previous
        previous=events.digest(row)
        row['event_hash']=previous
    return b''.join(events.canonical(row)+b'\n' for row in rows)


def wrong_branch(saved,out):
    seal=r6.read_json(saved/'seal.json')
    for item in seal['retained_sha256']:
        target=out/item
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(saved/item,target)
    rows=events.read(out/'events.ndjson')
    selected=[r for r in rows if r['source']=='child_report' and r['event'] in {'recovery_started','recovery_finished'}]
    success=selected[-1]
    route='exact_support_bounded' if success['payload']['data']['route']=='bounded_enumeration' else 'bounded_enumeration'
    replacement=[]
    for branch in (['bounded_enumeration','exact_support_bounded'] if route=='exact_support_bounded' else ['bounded_enumeration']):
        start=copy.deepcopy(selected[0])
        start['payload']['data']={'route':branch}
        finish=copy.deepcopy(success)
        finish['receipt_monotonic_ns']=start['receipt_monotonic_ns']
        finish['payload']['data']={'route':branch,'ok':branch==route}
        finish['payload']['data'].update({'witness':success['payload']['data']['witness']} if branch==route else {'reason':'injected'})
        replacement.extend([start,finish])
    at=rows.index(selected[0])
    rows=rows[:at]+replacement+rows[at+len(selected):]
    verdict=r6.read_json(out/'verdict.json')
    verdict['recovery_route']=route
    r6.write_json(out/'verdict.json',verdict)
    rows[-1]['payload']['verdict_sha256']=r6.sha(out/'verdict.json')
    (out/'events.ndjson').write_bytes(rehash(rows))
    seal['event_count']=len(rows)
    seal['last_event_hash']=rows[-1]['event_hash']
    seal['retained_sha256']={n:r6.sha(out/n) for n in seal['retained_sha256']}
    r6.write_json(out/'seal.json',seal)

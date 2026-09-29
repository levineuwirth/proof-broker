"""Price admission precedes every append to the durable reservation ledger."""
import fcntl
import os
from pathlib import Path
import time

import priced_contract as contract
import priced_payload as wire
import pricing_gate as gate


def reserve(path,episode_id,arguments,request,sources):
    c=contract.config()
    gate.require(isinstance(episode_id,str) and bool(episode_id),'missing_episode_identity')
    # This is executed in the production reservation path, not an optional check.
    admitted=gate.admission(c,sources,arguments,request,time.time())
    path=Path(path)
    with path.open('a+b') as f:
        fcntl.flock(f,fcntl.LOCK_EX)
        f.seek(0); raw=f.read()
        rows=[]
        if raw:
            gate.require(raw.endswith(b'\n'),'truncated_reservation_ledger')
            rows=[gate.strict(line) for line in raw.splitlines()]
        for index,row in enumerate(rows):
            gate.require(row['sequence']==index and row['policy_sha256']==admitted['policy_sha256'],'ledger_identity')
            previous='0'*64 if index==0 else gate.sha(gate.canonical(rows[index-1]))
            gate.require(row['previous_hash']==previous,'ledger_chain')
            gate.require(type(row['reservation']['reserved_micro_usd']) is int
                and row['reservation']['reserved_micro_usd']==admitted['reserved_micro_usd'],'ledger_price')
            gate.require(row['pricing_admission']['reserved_micro_usd']==admitted['reserved_micro_usd']
                and row['pricing_admission']['policy_sha256']==admitted['policy_sha256'],'ledger_admission_binding')
        attempts=sum(row['episode_id']==episode_id for row in rows)
        spent=sum(row['reservation']['reserved_micro_usd'] for row in rows)
        reservation=wire.reservation(arguments,spent,attempts)
        gate.require(len(rows)<c['limits']['campaign_attempts'],'campaign_request_budget')
        row={'sequence':len(rows),'previous_hash':gate.sha(gate.canonical(rows[-1])) if rows else '0'*64,
             'episode_id':episode_id,'policy_sha256':admitted['policy_sha256'],
             'request_sha256':gate.sha(request),'arguments_sha256':gate.sha(gate.canonical(arguments)),
             'reservation':reservation,'pricing_admission':admitted}
        f.seek(0,2); f.write(gate.canonical(row)+b'\n'); f.flush(); os.fsync(f.fileno())
    return row

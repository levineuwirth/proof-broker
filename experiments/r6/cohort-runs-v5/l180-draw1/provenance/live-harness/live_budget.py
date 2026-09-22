"""Durable reservations; unknown/failed responses never refund a reservation."""
import fcntl
import json
import os
from pathlib import Path

import events
import live_contract as contract
import live_payload as wire
import run as r6


def reserve(path, episode_id, arguments, request_sha256):
    c=contract.config()
    if not isinstance(episode_id,str) or not episode_id: raise ValueError('Missing episode identity')
    path=Path(path)
    with path.open('a+b') as f:
        fcntl.flock(f,fcntl.LOCK_EX)
        f.seek(0); raw=f.read()
        rows=[]
        if raw:
            if not raw.endswith(b'\n'): raise ValueError('Truncated reservation ledger')
            rows=[json.loads(line) for line in raw.splitlines()]
        for index,row in enumerate(rows):
            if row['sequence']!=index or row['policy_sha256']!=r6.sha(contract.CONFIG):
                raise ValueError('Reservation ledger identity differs')
            prior='0'*64 if index==0 else events.digest(rows[index-1])
            if row['previous_hash']!=prior: raise ValueError('Reservation ledger chain differs')
            rate=c['pricing']['reservation_micro_usd_per_token']; limits=c['limits']
            expected=limits['input_tokens_reserved']*rate['input']+limits['output_tokens']*rate['output']
            if type(row['reservation']['reserved_micro_usd']) is not int or row['reservation']['reserved_micro_usd']!=expected:
                raise ValueError('Reservation amount differs from the frozen policy')
        attempts=sum(row['episode_id']==episode_id for row in rows)
        spent=sum(row['reservation']['reserved_micro_usd'] for row in rows)
        receipt=wire.reservation(arguments,spent,attempts)
        if len(rows)>=c['limits']['campaign_attempts']:
            raise wire.Failure('campaign_request_budget','admission','Campaign request budget exhausted')
        row={'sequence':len(rows),'previous_hash':events.digest(rows[-1]) if rows else '0'*64,
            'policy_sha256':r6.sha(contract.CONFIG),'episode_id':episode_id,
            'request_sha256':request_sha256,'arguments_sha256':events.digest(arguments),'reservation':receipt}
        f.seek(0,2); f.write(events.canonical(row)+b'\n'); f.flush(); os.fsync(f.fileno())
        return row

#!/usr/bin/env python3
"""R6-014 amendment 2: SYNTHETIC source episodes for the amendment's live-shaped fixture, including a pre-send release and its retry,
before any auditor reads the collected release.

Canned rehearsal episodes of the unmodified cohort driver (`cohort_episode.execute`, mode `rehearsal`) on an **isolated** copy of the frozen
disabled v9 policy (its checkpoint bytes) with its own rehearsal ledger under `fixtures/r6-014-v4-sources/`; the production policy, lock
and campaign ledgers are never touched. All sources share one admitted capture, so the fixture needs no pricing reversal: the eleven posed
sites at draw 1 (the v9 rehearsal order), then one slot (l096, draw 2) twice:

1. `l096-draw2` — the loopback TLS fixture is materialized with its reviewed `untrusted_ca` case (R6-005), so the sender's own TLS
   handshake fails before any header byte: a genuine connection-phase failure of the unmodified sender, which the ledger reconciles as a
   pre-send release (established termination, zero sends). This is the one intervention, and the episode records it (`tls-fixture/
   provenance.json`: the trust root is the other CA).

2. `l096-draw2-attempt2` — the same slot retried with the `valid` fixture: an ordinary canned episode.

The isolated disabled policy (the checkpoint's bytes, pricing capture 3) is first moved onto the admitted capture 6 by the production pricing
revision (`cohort_contract.revise`), in the isolated copy only; without it the pricing gate refuses both episodes before reservation.

No provider is contacted; the credential is the driver's synthetic canary. The live-shaped fixture generator (`live_shape_v10.py`) then
rebinds both to its live test campaign by the production functions, as it does every other source run.
"""
import argparse
import contextlib
import json
from pathlib import Path
import shutil
import sys
from unittest.mock import patch

R6 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(R6))
import cohort_contract as contract
import cohort_episode as driver
import live_tls_fixture
import run as r6
import site_task

OUT = R6/'fixtures/r6-014-v4-sources'
DRAW1 = ('l069', 'l070', 'l071', 'l078', 'l096', 'l166', 'l170', 'l175', 'l178', 'l204', 'l099')
SLOT = ('bracket-l096', 2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    if OUT.exists(): raise SystemExit('exists: '+str(OUT))
    (OUT/'policies').mkdir(parents=True); (OUT/'runs').mkdir()
    disabled = R6/'policies/farkas-cohort-v9.checkpoint.json'  # the frozen disabled v9 policy, byte for byte
    shutil.copyfile(disabled, OUT/'policies'/contract.CONFIG.name)
    results = {}
    with patch.object(contract, 'CONFIG', OUT/'policies'/contract.CONFIG.name), patch.object(contract, 'CHECKPOINT', OUT/'policies/unused.checkpoint.json'), \
         patch.object(contract, 'LEDGERS', OUT/'ledgers/campaigns'):
        c = contract.config(); assert c['live_enabled'] is False
        contract.campaign_ledger(False, c).activate(c, False)
        # the disabled policy names capture 3, long expired: moved onto the current admitted capture by the production pricing revision
        contract.revise(R6/'sources/pricing-approved-campaign-6', 'isolated synthetic sources: pricing refresh to the admitted capture 6')
        c = contract.config(); assert c['live_enabled'] is False and c['revision'] == 2
        packages = R6.parents[1]/'lean-bridge/.lake/packages'; task = site_task.get(SLOT[0])
        for site in DRAW1:
            run = OUT/'runs'/f'{site}-draw1'; run.mkdir(); results[run.name] = driver.execute(run, site_task.get('bracket-'+site), 1, 'rehearsal', packages, None)
        original = live_tls_fixture.materialize
        def untrusted(run, case): return original(run, 'untrusted_ca')
        with patch.object(driver.live_tls_fixture, 'materialize', untrusted):
            run = OUT/'runs/l096-draw2'; run.mkdir(); results['l096-draw2'] = driver.execute(run, task, SLOT[1], 'rehearsal', packages, None)
        run = OUT/'runs/l096-draw2-attempt2'; run.mkdir(); results['l096-draw2-attempt2'] = driver.execute(run, task, SLOT[1], 'rehearsal', packages, None)
        _, s = contract.campaign_ledger(False, c).snapshot()
    summary = {name: {k: r6.read_json(OUT/'runs'/name/'credential-summary.json').get(k) for k in ('failure_category', 'proof_accepted', 'reservation_state')}
               for name in results}
    r6.write_json(OUT/'SOURCES.json', {'schema_version': 'r6-014-release-sources-1', 'synthetic': True, 'slot': {'task_id': SLOT[0], 'draw': SLOT[1]},
        'runs': summary, 'ledger': {'slot': s['slots'].get(f'{SLOT[0]}/{SLOT[1]}'), 'rows': s['rows']}, 'disabled_policy_sha256': r6.sha(disabled),
        'intervention': 'attempt 1 only: live_tls_fixture.materialize(run, "untrusted_ca") in place of "valid"', 'program_sha256': r6.sha(Path(__file__)),
        'scope': 'canned rehearsal episodes on an isolated copy of the disabled v9 policy and its own ledger; no provider; synthetic canary'})
    print(json.dumps({'runs': summary, 'slot': s['slots'].get(f'{SLOT[0]}/{SLOT[1]}')}, indent=1))


if __name__ == '__main__':
    main()

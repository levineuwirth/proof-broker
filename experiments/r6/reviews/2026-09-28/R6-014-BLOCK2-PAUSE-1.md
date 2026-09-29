# R6-014 block 2, pause 1: a pre-send connection failure at l204 draw 6

This was recorded on 2026-09-29 (UTC). The collection as paused is committed as `ae1c8bbf`, with the runner log in
[R6-014-BLOCK2-RUN-2.log](R6-014-BLOCK2-RUN-2.log).

## What happened

The relaunched block 2 runner (revision 5) began at 2026-09-28T23:00:49Z.
- **Before the pause:** it collected **53 slots**, each gated `continue`: 29 proofs, 19 closer refusals and 5 rejected l170 witnesses.
- **The pause:** at the 54th slot, `l204-draw6` (episode 23:34:06–23:34:30Z), the sender made **one connection attempt that failed**
  (`transport_connection_failure`, phase `https_transport`, after 15.7 s).
- **What the failure left:**
  - zero header or body sends started, no grant committed, and no HTTP status;
  - termination established;
  - the ledger reconciled the reservation as a **release** (`pre_send_failure_with_established_termination`).
- **The gate:** it paused, as the reviewed rule requires ("a release or unknown send … pauses"). The command chain therefore skipped the
  operator scan.

**Ledger after the pause:**
- 64 transmissions consumed (11 + 53), and 6,553,600 µUSD committed;
- nothing open;
- slot `bracket-l204/6` **not consumed**, with `released: 1`;
- the frozen pre-send limit is 3 attempts, so two remain.

**No request reached the provider for this slot.**

**Likely cause: a brief network interruption on the host.** The system journal shows Tailscale's connectivity probe dropping (`udp=false`)
at 23:34:03Z and recovering at 23:34:29Z. That brackets the connection attempt. This is circumstantial, and nothing in the harness
indicates a fault.

## Why collection cannot simply resume

- **The runner** has no reviewed rule for retrying a released slot, and no override.
- **The frozen live auditor** (amendment 1, `live-evaluation-v2`) cannot accept a collection containing this event:
  - live mode fails closed on a pre-send release, which is not among its reviewed live kinds;
  - a retry would put two runs on one slot, which its population check refuses;
  - moving the release run aside would leave its ledger reservation and release rows without a matching run.
- **The frozen analysis** already defines pre-send releases (disposition `pre_send_released`, with attempt counts, and `exhausted` at the
  limit). It needs no change.

## Decision

The operator chose "Amendment 2, then resume". To be prepared for review:
- **(a)** a live-mode auditor amendment for pre-send releases and retried slots, reusing the reviewed rehearsal-mode release relationships
  and the ledger's own retry rule, with synthetic evidence first;
- **(b)** runner revision 6, allowing a released slot, with termination established and zero sends, to be retried as a new attempt
  directory within the frozen pre-send limit, with everything else unchanged.

After review:
1. re-lock the evaluation as `live-evaluation-v3`;
2. refresh pricing by the established pricing revision, since capture 6 is admissible only until 2026-09-29T20:13:37Z;
3. resume the remaining 24 slots: the retry of l204 draw 6, then 23 not yet attempted.

The collected runs, the ledger and the release run stay exactly as they are.

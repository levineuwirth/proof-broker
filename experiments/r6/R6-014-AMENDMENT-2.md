# R6-014 amendment 2 — live pre-send releases and retried slots

Status: prepared for review, 2026-09-29. This is a **post-collection amendment**. It is not an unchanged preregistered evaluation. Its
decision is recorded in [R6-014-BLOCK2-PAUSE-1.md](reviews/2026-09-28/R6-014-BLOCK2-PAUSE-1.md) ("Amendment 2, then resume").

Nothing has been authorized, reserved or sent since the pause. Analysis stays deferred until an accepted audit. The collected runs, the
ledger and the release run stay exactly as they are.

## When and why

| time (UTC) | commit | event |
|---|---|---|
| 2026-09-28 23:00:49 | `994bf8bc` | block 2 runner (revision 5) relaunched under `live-evaluation-v2` |
| 23:34:06–23:34:30 | `ae1c8bbf` | l204 draw 6: one connection attempt fails (`transport_connection_failure`, 15.7 s); zero sends; the ledger releases the slot; the gate pauses after 53 collected slots |
| 2026-09-29 08:43 | `c8aa54b6` | pause record; the operator chooses "Amendment 2, then resume" |

Three frozen pieces met an event none of them had reviewed for live mode:
- **the runner** pauses on any release and has no retry;
- **the live auditor** (amendment 1) fails closed on a live release and refuses two runs for one slot;
- **the ledger** already has the rule: a release with established termination and zero sends leaves the slot unconsumed, retriable up to
  `maximum_presend_attempts` (3).

The frozen analysis already defines `pre_send_released`, `presend_attempts` and `exhausted`, and needs no change.

Both changes were designed from the driver's, sender's and ledger's code and exercised on synthetic evidence. **The collected release has
not been read by the auditor, the runner's new path or any control.**

Retained byte-for-byte: `live-evaluation-v1` and `-v2` and v2's erratum; the amendment 1 auditor and its controls; the collection
(`cohort-live-v9/`: 65 runs, the 64 consumed slots and the release), the live ledger, floor and slots; the runner log; the interrupted attempt of incident 1.

## (a) The auditor: [`cohort_v9_audit_amended_2.py`](reviews/2026-09-28/cohort_v9_audit_amended_2.py)

Amendment 1's auditor with these changes, each stated in its docstring (80 diff lines, docstring included):
- **A live kind `release`.** A run is a release when its ledger reconciliation is one; this is read before the transport outcome, which
  a release shares with a provider error.
- **`live_release`**, the live counterpart of the rehearsal-only release check:
  - the sender's failure is one of the four connection-phase categories `cohort_https.handoff` raises before the grant (TLS
    verification, TLS protocol, timeout, connection failure), agreed by the summary, the validation and the HTTPS record;
  - one connection attempt, no verified TLS, no grant, zero header and body sends, no status, no response;
  - the handled exception: exit 0 and an empty stderr; the pricing check admitted.
- **Retried slots.** A slot may hold `<site>-draw<d>`, then `-attempt2`, `-attempt3`, contiguously:
  - every attempt but the last is a release;
  - at most the reserving revision's `maximum_presend_attempts`;
  - on the ledger, the attempts are reserved in attempt order, and the slot's `released` count equals its release runs.

Every other predicate is amendment 1's: the ledger binding (which already binds each reconciliation's evidence digests), the grant, the
receipts, the chain, the publication and the scan. A partial or unknown send still fails closed. The rehearsal path is unchanged.

## (b) The runner: [`run_block2.py`](reviews/2026-09-24/run_block2.py), revision 6

A release the gate verifies is decided **`retry`**. Verification means:
- the auditor's release predicates;
- the ledger's release (`pre_send_failure_with_established_termination`), the slot's k-th release on the ledger, nothing open;
- nothing past the send: no certificate, consumer, kernel, proof record or response;
- the frozen live release chain.

The runner then waits `RETRY_DELAY_SECONDS` (60 s, to ride out a brief interruption) and reserves the slot again as `-attempt<k+1>`. At the
limit the slot is exhausted and collection pauses. A sent slot must show its prior releases as its `released` count. On restart, every
existing attempt is gated in order before anything launches. Everything else is revision 5's, including the frozen sequences, which
still come from the v2-locked auditor.

## Synthetic evidence first

- **Sources** ([`release_sources.py`](reviews/2026-09-28/release_sources.py), `30bb80c0`). Canned rehearsal episodes of the unmodified
  driver on an isolated copy of the disabled v9 policy, all on the admitted capture 6: the eleven draw-1 sites, then l096 draw 2 with the
  loopback TLS fixture materialized as its reviewed `untrusted_ca` case. The sender's own handshake fails before any header byte, a
  genuine `tls_certificate_verification` release. Then `l096-draw2-attempt2` is an ordinary proof. The isolated ledger ends with the slot
  consumed, `released: 1`, two reservations.
- **Fixture** (`fixtures/r6-014-v4-live-release`, [`live_shape_v10.py`](reviews/2026-09-28/live_shape_v10.py)). All 13 are rebound by the
  production functions under the production signing layout and three revisions; the release and its retry are reserved under revision 2.
  The operator scan binds all 13.

## Controls

**Auditor** ([R6-014-AMENDMENT-2-AUDIT-CONTROLS.json](reviews/2026-09-28/R6-014-AMENDMENT-2-AUDIT-CONTROLS.json),
[controls](reviews/2026-09-28/cohort_v9_audit_amended_2_controls.py)). The collected block 2 is not read.

- **Precondition:** amendment 1 rejects the release fixture.
- **Accepted:** amendment 2 accepts it with **639 cases**, and accepts a fixture regenerated from unmodified sources identically.
- **Transport mutations.** Each is applied to the release's source, and the whole fixture is regenerated by the unchanged generator, so
  the production ledger reconciles the altered records itself and every run, row, seal and scan is re-bound.

  | mutation | ledger reconciles | amendment 2 rejects at |
  |---|---|---|
  | a header send | `unknown`: slot consumed, retry refused (`cohort_slot_consumed`) | `l096-draw2:ledger:permit_and_reconciliation_bound` |
  | a committed grant | `send_grant`: slot consumed, retry refused | `l096-draw2:grant:consistent_with_outcome` |
  | a category outside the connection phase | release | `l096-draw2:failure:classified_and_finalized` |
  | verified TLS | release | `l096-draw2:failure:classified_and_finalized` |
  | a non-zero exit | release | `l096-draw2:receipts:stage_returned_within_frozen_limits` (the shared stage receipt, first) |

  Where the ledger refuses the retry, that fixture cannot exist. It is regenerated without the retry so that the auditor still meets
  the altered run.
- **On the fixture itself:**
  - the release's HTTPS record altered after reconciliation, with the ledger untouched, is rejected at `ledger:permit_and_reconciliation_bound`;
  - a retry renamed out of sequence, a second sent attempt, and a retry without its first attempt are each rejected at
    `population:within_authorized_schedule`;
  - the retry renamed as the first attempt, leaving the ledger's release without its run, is rejected at
    `l096-draw2:ledger:permit_and_reconciliation_bound`.
- **The limit:** `slot_attempts_ok` probed directly. Three attempts pass; a fourth fails; a sent attempt before the last fails.
- **Amendment 1's populations, unchanged:**
  - the isolated fixture's 550 cases, identical to the frozen record;
  - the nine shared-directory controls;
  - all 51 frozen live records, with zero sentinel reads for the escapes.

**Not re-executed:** the rehearsal-mode audit and its 101 controls, as for amendment 1. The amended paths are live-only.

**Fixture records:** [audit](reviews/2026-09-28/R6-014-AMENDMENT-2-RELEASE-FIXTURE-AUDIT.json) (accepted, 639 cases), and the frozen
[analysis](reviews/2026-09-28/R6-014-AMENDMENT-2-RELEASE-FIXTURE-ANALYSIS.json). The analysis reads l096 draw 2 as one slot,
`sent_with_response`, with `presend_attempts: 1`; no pause, no integrity stop.

**Runner** ([R6-014-BLOCK2-RUNNER-V6-CONTROLS.json](reviews/2026-09-24/R6-014-BLOCK2-RUNNER-V6-CONTROLS.json)). 61 cases, each fresh
and on restart: 122 records, all as expected.

Revision 5's 50 cases all keep their decisions. One pauses for different reasons: `sealed_release_pauses`, a proof run whose ledger
reconciliation is forged as a release. It now takes the release path and pauses on four reasons; it is never retried.

Eleven cases are new, on the fixture's release and retry:
- continues or retries:
  - the release is retried;
  - release then sent retry continues;
- pauses:
  - the third release, as exhausted;
  - a header send, a grant, a category outside the connection phase, verified TLS or a non-zero exit;
  - records past the send;
  - a ledger release count that disagrees;
  - a sent retry whose slot's `released` count disagrees.

## After review

1. Freeze **`live-evaluation-v3`** over:
   - the amendment 2 auditor and its controls;
   - the fixture and its generators;
   - the frozen analysis;
   - as records: v2, this record, its review, and runner revision 6 and its controls.
2. `verify` it.
3. Capture 6 is admissible until **2026-09-29T20:13:37Z**. If it has lapsed, refresh pricing by the established revision, a new capture
   and `revise` under the same authority. The operator runs the capture.
4. The operator relaunches the runner in a new log. It re-gates the 54 existing runs, retries l204 draw 6, then collects the 23 remaining
   slots. If the collected release does not gate as a retry, the runner pauses with nothing sent, and that is reviewed separately.
5. The operator scan binds every run, including attempt directories. Then the amendment 2 audit runs; the frozen analysis runs only on
   acceptance. Any further production-only mismatch is retained and reviewed separately.

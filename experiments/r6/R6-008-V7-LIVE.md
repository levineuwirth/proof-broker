# R6-008 revision 7 — the first signed live transmission

Status: complete, 2026-09-14. **One transmission under the signed policy
`7e16462d…` (approved by Levi Neuwirth, 2026-09-14T09:58:00Z), reconciled as
`send_grant`, sealed, and accepted once the operator scan was bound to its
credential commitment and seal.** The model returned the deterministic
witness `2·hZ + neg_goal`; the proof export is byte-identical to the golden
deterministic broker episodes. Priced ceiling 16,638 µUSD ($0.0166); not a
bill. The live audit passes 32 named cases with the operator scan bound and
its 9 controls reject at the named case. The authorization is spent: the live
ledger holds `activation(live), reservation, send_grant`, one transmission
consumed, nothing open.

## Signing

`campaign_contract.py sign` retained the disabled revision-7 bytes as
[responses-campaign-v7.checkpoint.json](policies/responses-campaign-v7.checkpoint.json)
(`1d2696c6…`), wrote the signed policy under the unchanged lock `50e42fbc…`
with `signed_from_checkpoint_sha256` naming those bytes, and activated
`ledgers/live/7e16462d….ndjson` with purpose `live` and the authorization
record verbatim. The audit binds all three, and refuses a checkpoint copy that
differs from the signed policy minus its signature fields.

## The transmission

| | |
| --- | --- |
| Ledger | attempt identity recorded, reservation `a324477c…`, slot created beside the ledger; grant committed in that slot with O_EXCL, durable 440,127 ns before the first header byte; reconciled `send_grant / returned`, termination established, evidence complete |
| Transport | TLSv1.3 `TLS_AES_256_GCM_SHA384`, chain verified against `api.openai.com` (peer `fabf4da3…`, the same certificate the pilot saw), shared network namespace with the resolver and the pinned public bundle; HTTP 200, no retries, no redirects; the captured outbound bytes equal the admitted serialized body; remote receipt recorded as unobservable |
| Provider | `gpt-5.4-2026-03-05`, `status: completed`, `service_tier: default`, `resp_0b61b5e1…`; usage 1,525 in / 855 out (771 reasoning) / 2,380 total, no cache hits — provider claims, not attestation |
| Credential | `credential_use_accepted` on the 2xx status; `exact_receipt: null` — use, not receipt. Commitment `61072a91…` over `domain:nonce:header` recorded at the handoff; the header appears in no record |
| Certificate | `verified_farkas`; recomputed: `Zmax` cancels, constant 18,446,744,069,397,676,034 > 0 |
| Proof | shared checker with task, context and challenge identity; kernel replays 3,702 / 3,721, empty axiom deltas; export `f4c179f3…` |
| Attribution | `live_model_response` on every receipt, route `responses_campaign_v7`, consumer route recorded beside it |
| Seal | 52-event chain, 275 retained files; terminal `episode_finished` with `accepted: false, publication_pending: true` |

## The operator scan, run by the author

49,391 files and 379 gzip streams under `experiments/r6`; zero disclosures,
nothing unreadable, irregular or incomplete. For `live-1`: covered by the
scan, sealed and intact, commitment record sealed, commitment bound — all
four true, `read_failures: 0`. The full report (19,545,851 bytes,
`4884bcb2…`) is retained locally; the committed
[summary](reviews/2026-09-14/R6-008-V7-LIVE1-OPERATOR-SCAN.summary.json)
binds it by digest, and the live audit binds the receipt's commitment, nonce,
seal digest and record digest to the run.

## The result, read carefully

Two live samples now exist for D1: the pilot's `hwidth + 32769·neg_goal` and
this run's `2·hZ + neg_goal`, the deterministic first hit exactly. They share
the instruction bytes, the arithmetic rows and the generation options, but
not the full request: `schema_version` and the model-visible `policy_sha256`
differ, so the user message and its echoed digest differ. They are two
distinct valid outputs under one mathematical task and instruction template;
they do not isolate sampling randomness from that metadata change. The
design consequence stands — repetition (k) is a variable — and R6-009 makes
the model input byte-identical across revisions so that future repeats do
isolate it. Both samples verified; nothing here is a rate, a reliability
claim or a comparison.

## Audit

[`campaign_audit.py --live-run`](reviews/2026-09-13/campaign_audit.py), 32
named cases ([record](reviews/2026-09-14/R6-008-V7-LIVE1-AUDIT.json)): the
rehearsal relationships, with the live ones in their place — signed policy
and checkpoint bound; activation serving the authorization; shared-network
mounts with the resolver, the public bundle and the operator's file outside
the run; credential use recorded as use; publication pending until the
operator receipt is bound; one transmission under the signed authorization.
[Controls](reviews/2026-09-14/campaign_live_audit_controls.py): 9 mutations
(three on the operator receipt, a forged terminal acceptance, retrofitted
attribution, a removed ledger row, a checkpoint mismatch, altered outbound
bytes, a summary naming C8) rejected at the named case
([record](reviews/2026-09-14/R6-008-V7-LIVE1-AUDIT-CONTROLS.json)).

## Reproduce

```bash
cd experiments/r6
python3 reviews/2026-09-13/campaign_audit.py --live-run campaign-runs-v7/live-1 \
  --operator-scan-summary reviews/2026-09-14/R6-008-V7-LIVE1-OPERATOR-SCAN.summary.json --output <new path>
python3 reviews/2026-09-14/campaign_live_audit_controls.py --output <new path>
```

The transmission itself does not reproduce: the authorization is spent, and
the ledger refuses a second reservation with `campaign_transmissions_exhausted`.

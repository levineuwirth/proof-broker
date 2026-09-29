# R6-005 review acceptance and closeout

Accepted on 2026-09-09 at the **local canned HTTPS/client handoff scope**.
The [reviewed report](../../R6-005.md), frozen policy, sources, suites and
episodes remain byte-identical. This dated addendum closes their review;
the report's earlier “ready for review” status is preserved as history.
No live policy or spending authorization is established by this closeout.

The [fresh public recount](R6-005-CLOSEOUT-PUBLIC-GATE.json) accepts the same
**96 checks: 25 focused / 26 native / 30 artifact audits / 15 outer gates**.
The [closeout preflight](R6-005-CLOSEOUT-PREFLIGHT.json) independently recomputes
**518 event hashes and 3,960 sealed entries**. The original 12,242-file
preservation inventory and the additional 13,406-file pre-closeout inventory
overlap: their union is **16,277 distinct prior files, all unchanged**.
This includes reviewed uncommitted work, not just committed blobs.
The [closeout checks](R6-005-CLOSEOUT-CHECKS.json) bind those inventories,
source captures, controls and replay observations to their actual bytes.
No native episode, TLS fixture, compilation or Lean replay was rerun.

## Pricing now has a retained source

Both cited official OpenAI pages were fetched over HTTPS and retained in full:

| Source | Retained entity | Receipt and reproducible extract |
| --- | --- | --- |
| [GPT-5.6 Sol](https://developers.openai.com/api/docs/models/gpt-5.6-sol) | [418,566 bytes](R6-005-SOURCES/gpt-5.6-sol.html) | [receipt](R6-005-SOURCES/gpt-5.6-sol.receipt.json), [extract](R6-005-SOURCES/gpt-5.6-sol.extract.json) |
| [GPT-5.4](https://developers.openai.com/api/docs/models/gpt-5.4) | [419,092 bytes](R6-005-SOURCES/gpt-5.4.html) | [receipt](R6-005-SOURCES/gpt-5.4.receipt.json), [extract](R6-005-SOURCES/gpt-5.4.extract.json) |

Receipts bind the raw entity, extracted pricing and snapshot sections, extractor
source, requested/effective URL, successful retrieval and local observation
times. These captures **postdate the canned checkpoint**; they corroborate its
rates, rather than retroactively becoming its original pricing source. Fetch
metadata is a local observation, not signed provider pricing. The Sol receipt
also retains the harmless curl warning for an unsupported version-format
variable; client version was obtained separately, and all received bytes and
lengths verify.

The [offline checker](pricing_sources.py) re-extracts the page before comparing
its rates with the frozen policy. Sol's input/cache-read/cache-write/output
rates reproduce the **163,840 micro-USD** reservation. GPT-5.4's inspected page
does not establish a cache-write rate: its extract records **null**, and does
not inherit Sol's multiplier. A replacement model needs its own complete rate
basis before its reservation can be frozen.

There are [12 separately gated source controls](R6-005-CLOSEOUT-SOURCE-CONTROLS.json),
not additions to the frozen 96 checks. They include a forged extract with
recomputed hashes, changed output/cache-write rates, a changed pricing condition,
a changed dated ID, missing source/section, and a raw-byte change outside the
extracted sections. Each corruption first verifies the unmutated copy.

The comparison reports raw, extracted-text, numeric-rate and listed-ID changes
separately. **Matching numeric rates cannot approve changed pricing conditions.**
Similarly, unchanged extracted sections do not establish that every other page
change is harmless. The current checker implements an offline comparison;
the next live entrypoint still needs an admission gate bound to the reviewed
source digest and applicable conditions.

```bash
python3 -B experiments/r6/reviews/2026-09-09/pricing_sources.py audit \
  --bundle experiments/r6/reviews/2026-09-09/R6-005-SOURCES \
  --policy experiments/r6/policies/responses-https-v1.json

# After retaining a fresh capture bundle in the same receipt format:
python3 -B experiments/r6/reviews/2026-09-09/pricing_sources.py compare \
  --old experiments/r6/reviews/2026-09-09/R6-005-SOURCES \
  --new /path/to/fresh-capture --model gpt-5.6-sol
```

## Model identity is a cohort decision

**Recommendation, pending author selection:** use the documented dated
`gpt-5.4-2026-03-05` for the initial measurement cohort. If Sol is also useful,
give its undated ID a separate exploratory policy and time-bounded cohort;
do not pool those calls as observations of one established immutable revision.
This is a methodological preference, not a claim that GPT-5.4 performs better.
The frozen canned configuration continues to name `gpt-5.6-sol`.

The official pages establish a dated GPT-5.4 option and no separate dated Sol
snapshot in the inspected listing. That absence does not prove a particular
update schedule. A dated ID improves provider-version attribution; it is still
not a content hash of model weights, a guarantee of future availability or
deterministic output, or independent evidence of the computation performed.
Record requested and returned IDs, timestamps, response/request identifiers and
sampling settings even with a dated selection. Those limitations remain relevant
to VerInf rather than being solved by the model name.

## Replay-field compatibility

R6-004 D1 records `proof_replayed: true`. The two successful R6-005 verdicts omit
that field. Their raw value is **missing**, not false; no field was inserted into
sealed artifacts. The closeout records raw field presence separately from
`recorded_proof_replay_confirmed_by_artifact_audit`, derived from the freshly
passing shared proof audit and its retained local/containing validation reports
and receipts. This is an interpretation of existing evidence, not a new replay.

Both **uncompressed proof exports** were compared byte for byte with R6-003:
D1 is 10,778,141 bytes and C8 is 4,032,429 bytes, with the same recorded SHA-256
digests. `derivation_replayed` remains false: kernel replay of a reconstructed
proof is distinct from replaying the solver's derivation. C8's containing target
remains a statement-identical wrapper, while D1 tests the larger real context.

## Before the two-control live pilot

1. Select the model/cohort deliberately and version the new policy. Freeze the
   requested and allowed response IDs and the precise revision claim. D1/C8
   remain interface controls; two calls are not a capability estimate.
2. Capture the selected model's applicable pricing at policy freeze and refresh
   it in each campaign preflight. Retain both raw and extracted digests and the
   comparison result. Resolve changed or unestablished conditions before making
   reservations. Sol's published promotional horizon reaches into November;
   September's rates must not silently become the confirmatory campaign's rates.
3. Bind the reviewed price basis to the actual reservation, token limits and
   shared campaign ledger before transport. The local cap remains conditional,
   rather than a provider billing guarantee. Confirm the spending ceiling before
   enabling an externally billed entrypoint.
4. Version live proposer attribution, public-root TLS/credential provisioning
   and network admission. Restore an explicitly audited `proof_replayed` field
   in the new verdict schema and preserve missing/false/unobserved distinctions
   in cross-checkpoint readers. Exercise those changed boundaries with canned
   controls before using a real key. Any change to a policy's `FILES` lock
   requires a new version and a fresh native run under that version.

Original-tree recount coverage remains distinct from retained-only audits with
unavailable build products. This closeout fetched public documentation only;
actual live-model calls and cost remain zero. Nothing was committed or pushed.

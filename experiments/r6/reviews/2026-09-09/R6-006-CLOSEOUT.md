# R6-006 review acceptance and closeout

**R6-006 v2 was approved without findings on September 10, 2026**, at the local
canned HTTPS pricing-admission scope. The author reported independent artifact
recomputation and re-fetching both cited sources. That review closes the two
unbound pricing conditions found in v1.

This dated addendum records acceptance. The [v1 report](../../R6-006.md),
[v2 report](../../R6-006-V2.md), policies, source locks, captures, suites and
episodes retain their reviewed bytes, including their earlier status wording.
The historical requirements file is likewise preserved. No live policy or
spending authorization is established here.

## Accepted evidence

The [fresh public recount](R6-006-CLOSEOUT-PUBLIC-GATE.json) accepts the same
**120 checks: 46 focused / 20 native / 39 audits / 15 outer controls**. The
[closeout preflight](R6-006-CLOSEOUT-PREFLIGHT.json) independently recomputes
**431 event hashes and 3,951 sealed entries** across the twenty episodes.

The [closeout comparisons](R6-006-CLOSEOUT-CHECKS.json) verify all 19,536 prior
file digests and the approved v2 retention-input population of 4,022 paths:
**23,558 distinct paths compared against their previous anchors**. V1's
16,292-file inventory is contained byte-for-byte in the 19,536-file inventory.
The earlier v2 preflight was excluded from its own inventory; its file digest
is bound separately at closeout rather than added to that comparison count.

All thirteen pricing negatives made zero connections: twelve actor rejections
and one host rejection with no proposal stage. D1/C8 retain their byte-identical
R6-003 proof exports and empty axiom deltas. C8's containing proof remains a
statement-identical binding wrapper; D1 tests embedding in the larger real
declaration. Original-tree recount coverage remains distinct from retained-only
audits with unavailable build products.

No native episode, Lean replay, outer mutation suite, source retrieval or
provider call was rerun during this closeout. Existing controls were validated
through the public recount; this is an artifact audit, not new execution
attestation. The publication scan covers the new closeout artifacts too and
retains the expected two overlapping synthetic disclosures in the deliberately
reflected response, with zero unexpected disclosures.

## Decisions to carry forward

1. **Recompute at each boundary.** The actor must derive applicability from its
   own retained inputs even after host approval. Preserve the separate host and
   actor verdicts and the detailed failure codes alongside the coarse category.
   A failed earlier stage leaves later predicates unobserved.
2. **State conservative restrictions precisely.** The strict project bound
   `<272000` remains distinct from the documented `>272000` surcharge trigger.
   The exact standard-endpoint allowlist excludes unapproved configurations;
   it is not a regional-endpoint classifier. Preserve the one-stateless-request
   assumption because the documented long-context condition covers a session.
3. **Version changes to frozen execution.** New policy/source-lock versions
   and fresh native evidence are required when locked implementation changes.
   Keep review records additive and use non-locked review helpers for additional
   artifact comparisons.

## Remaining live-pilot decisions

Model/cohort selection and spending approval remain explicitly pending. The
dated GPT-5.4 identity and $0.102400 conditional reservation belong to the
approved canned configuration; approval of these controls does not select or
authorize a billed model.

Before a live pilot, freeze the chosen identity and requested/allowed response
IDs, refresh and admit its applicable price basis, and approve the campaign
budget. Version the transition to real credential provisioning, public-root
TLS and permitted network egress, including live proposer attribution. Exercise
those changed boundaries with canned controls first and use one shared campaign
ledger. Any first D1/C8 calls remain interface controls, not a capability cohort.

```bash
python3 -B experiments/r6/reviews/2026-09-09/pricing_gates_v2.py \
  --run-dir experiments/r6/pricing-v2-runs/checkpoint-v2 \
  --gate-file experiments/r6/reviews/2026-09-09/R6-006-V2-GATES.json \
  --output /tmp/r6-006-closeout-recount.json
```

The [comparison program](pricing_closeout_checks.py) can be rerun on this
closeout checkout with `--output /tmp/r6-006-closeout-comparisons.json`. Its
historical input population is fixed; later research additions are not silently
excluded. Nothing was committed or pushed. Live model calls and cost remain zero.

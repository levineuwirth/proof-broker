# R6-009 proposal — repeated certificate search on a frozen cohort

Status: research-design proposal, 2026-09-14, against `4b8a7d9`. This is not
a frozen experiment, an authorization, or an implemented cohort runner.
R6-008's signed authorization remains spent. No existing source, policy,
ledger, episode or closeout is changed by this proposal.

The first cohort should ask: **on a prospectively enumerated downstream
workload, how often does one learned proposal yield an admissible reconstructed
proof, what does repetition buy, and where does deterministic recovery already
provide that proof?** Witness diversity is a separate descriptive question.
This makes a negative marginal-value result meaningful rather than turning a
different certificate into an improvement claim.

| Decision | Recommendation |
| --- | --- |
| Replication | Eight preassigned learned draws per primary obligation; complete all eight even after success |
| Search policies | Deterministic Proof Broker and independent learned proposal on every primary obligation |
| Operational comparator | The frozen deterministic policy's first admissible result, with its actual cost and failure boundary |
| Witness comparator | Primitive coefficient vectors and supports; a separately bounded deterministic diagnostic, never an unspecified full witness set |
| Context | Existing arithmetic IR and instruction semantics; byte-identical complete model input across a task's repeated draws |
| Scope | September exploratory census; no new repository-general capability or high-reliability claim |

## What the two D1 observations establish

The [pilot](R6-007.md) and [v7 live closeout](R6-008-V7-LIVE.md) retain two
different valid witnesses. Both the system instruction bytes (`30fcc51b…`)
and the arithmetic problem and task-binding objects are identical. The
model ID and all supplied generation options also match. The full requests
are not identical: `schema_version` changes from `r6-farkas-request-7` to
`r6-farkas-request-8`, and `policy_sha256` changes. Consequently the user
message and its echoed request digest differ too.

The [design evidence](reviews/2026-09-14/R6-009-DESIGN-EVIDENCE.json)
recomputes those comparisons from committed bytes, as well as both integer
contradictions and proof-export hashes. Thus the observation is two distinct
valid outputs under the same mathematical task and instruction template. It
does not isolate sampling randomness from changed metadata or provider/time
effects, and neither draw demonstrates a success/failure transition.
Keep both as development observations, outside a prospective replicate pool.

This is consistent with the earlier
[assurance evaluation research pass](</home/jeans/apocrypha/Passus/Assurance-Conscious Evaluation of Learned Proof Search (2026-09-06).md>):
discovery of one reusable proof and reliable rediscovery are different
operational objectives. In prior work, Chen et al. define the usual
any-success sampling estimator, while Yao et al. distinguish it from
all-trials-success reliability. Neither paper supplies a justified sample
size for this small repository cohort. [Chen et al., 2021, §2.1 and Appendix A](https://arxiv.org/html/2107.03374v2#S2.SS1);
[Yao et al., 2024, §3](https://arxiv.org/html/2406.12045v1#S3).

## Eight draws, with a fixed stopping rule

Use `n = 8` experimental draws and report discovery at `k = 1, 2, 4, 8`.
Here `n` is the fixed data-collection allocation; `k` is the budget at which
the collected outcomes are evaluated. Do not choose a different `n` after
seeing an obligation's first success, failure, support or coefficient size.
Do not stop successful tasks early or add retries to interesting failures.

Eight is a practical exploratory allocation, not a power calculation. The
following planning arithmetic assumes independent, identically distributed
Bernoulli trials **within one task**; it is not an inference from D1:

| Draws | Chance to see at least one success if p = 0.2 | One-sided 95% lower bound after all draws succeed | Reservation for 15 tasks under the retained v7 basis |
| --- | --- | --- | --- |
| 4 | 0.5904 | 0.4729 | $6.144 |
| 8 | 0.8322 | 0.6877 | $12.288 |
| 16 | 0.9719 | 0.8293 | $24.576 |

The bounds come from solving `p^n = 0.05`; even 8/8 does not establish
90% per-task reliability. That particular one-sided lower-bound claim would
require at least 29/29 under the stated assumptions. More repeats do not
create more independent mathematical problems. If resources are constrained,
choose four for every primary task **before** collecting outcomes; do not
quietly switch from eight to four after reading them.

The dollar column is arithmetic from the retained conditional reservation
of 102,400 µUSD per transmission, not refreshed pricing or a bill. Actual
membership may be smaller than 15; 14 tasks at eight draws reserve
$11.4688 on that basis. Native validation, failed episodes, released
pre-send attempts and operator work also cost time. Do not size the campaign
from the two unusually small observed usage estimates. The actual ceiling
must be recomputed from fresh sources and the admitted payload sizes before
authorization; no allocation here authorizes a request.

Use eight blocks, one draw of each task per block, with each block's task
order generated by a preregistered seed and retained before execution.
Keep previous responses, witnesses, errors and deterministic outputs out of
later model contexts. Preserve the supplied reasoning/output settings; do
not sweep temperature, model, prompt, context size or adaptive repair in this
cohort. Omitted sampling settings remain omitted and recorded; neither a
dated model ID nor fixed bytes proves independent samples or fixed weights.

## Stable inputs and authorization are one design decision

The current [request builder](campaign_budget.py#L22) embeds the signed
policy digest in model-visible JSON. The current
[contract](campaign_contract.py) permits one transmission. Creating eight
new one-transmission signatures therefore changes the input eight times,
even if the arithmetic and prose stay fixed. Calling those byte-identical
prompt repetitions would be incorrect.

Recommendation: the next **reviewed** policy should authorize a finite,
explicit task-by-draw schedule under one common policy digest, with one
single-use reservation/grant per scheduled slot. This keeps per-task input
bytes stable while retaining an authorization-scoped ledger and aggregate
spending limit. The slot ID belongs in host/actor receipts, not model text.
Freeze both the total allowance and per-task allocation; a global cap alone
must not allow eight draws intended for one task to be spent on another.

This is a policy and admission extension, not permission to edit or reuse
the spent v7 ledger. A canned checkpoint must establish the task/draw
allowlist, duplicate-slot rejection, wrong-task rejection, global and
per-task limits, release/unknown dispositions, and byte equality of each
task's repeated envelopes. The live sender must still have its own grant,
TLS and credential ordering, and publication/audit path.

If individual signatures are required instead, keep them and explicitly
separate a stable scientific request contract from the changing authorization
envelope in the next version. Bind both at the host and actor and test crossed
responses and authorizations. Simply deleting a hash from the existing
request would weaken its contract. Until either design is implemented,
repetitions measure performance under varying authorization metadata rather
than a single exact input. A response echo still proves association only;
identical request bytes never prove which execution produced a response.

Run a frozen block within its pricing-validity window. A necessary policy,
runtime, model-option or pricing refresh creates an explicitly recorded
boundary; do not pool changed-input runs as exact replications. A halted
collection stays incomplete rather than silently dropping tasks or extending
the budget after seeing results.

## The deterministic comparison has two distinct roles

**Operational comparison.** Run the frozen deterministic broker route once
on every admitted task, whether or not a learned draw succeeds. Preserve
backend choice, input order, bounded and exact-recovery limits, resource
ceilings and the complete certificate/replay acceptance condition. Count
success when that route returns any admissible reconstructed proof; record
the first result and the cost actually incurred. An enlarged catalogue is
not the cost of deploying the original first-result policy.

Keep the learned arm independent: one proposal per draw, no deterministic
fallback hidden inside it, and the same downstream certificate consumption
and proof/axiom checks. Native `omega` is a useful reference control, with
its different evidence path identified. It is not evidence that a broker
certificate was obtained. No model-selection, routing or feedback-repair arm
is needed yet.

**Witness analysis.** First verify the actual returned witness. Then order
its nonzero coefficients by frozen row identity and divide integer
coefficients by their positive gcd. If a future grammar admits rationals,
clear denominators first. Preserve sign; arbitrary sign reversal is not a
positive rescaling. Store this primitive vector, its support, coefficient
bit lengths, and proof-export digest. Keep distinct named rows distinct;
support diversity is a representation-level observation, not automatically
mathematical novelty. Raw contradiction margins scale with the witness and
are not an evidence-strength score.

There is no sensible literal full-witness-set baseline. Mathematically,
positive multiples already give infinitely many witnesses. Quotienting by
scale is not enough: on D1, positive combinations of the two observed
witnesses give infinitely many distinct primitive vectors. For example,
`t*(2*hZ + neg_goal) + (hwidth + 32769*neg_goal)` has `hwidth` coefficient
one and a different `hZ` coefficient for every positive integer `t`.
The actual interface's support and coefficient-length caps make the accepted
encoding space finite, but not a useful exhaustive experimental baseline.
This is a mathematical observation about these retained rows, not a claim
that the experiment enumerated that space.

For a diagnostic, freeze a finite procedure before live results: enumerate
the current exact-recovery support candidates up to four **split columns**,
with the recorded support-space and work caps, collecting verified primitive
witnesses rather than stopping at the first. Equalities generate two signed
columns, so four columns is not simply four arbitrary hypothesis names.
Keep this in a separate diagnostic driver and charge its time separately.
Report completion versus space/work refusal; a missing catalogue entry is
not proof that deterministic search cannot produce it. The
[current implementation](../../sdk/lib/farkas_search.ml) stops at the first
accepted candidate and has all those bounds; it does not implement this
catalogue as an existing result.

Classify a learned witness as matching the operational first result,
matching another catalogued vector, or absent from that bounded catalogue.
Report support equality separately. A run restricted to a model-proposed
support is an assisted diagnostic, never a replacement for the independent
deterministic baseline. The pilot's support-restricted exact-recovery result
already demonstrates why different-first-result and beyond-deterministic
capability cannot be equated. [R6-007 witness qualification](R6-007.md#the-witness).

## Census, outcomes and the smallest result table

Keep the agreed source: `Bracket.lean` at
`c07e03c94884e9084ffaf7a7294fc0907672f6c2`. The retained pristine bytes
contain 15 textual `omega` sites, re-derived in the design evidence. That is
not 15 admitted or independent problems. The next extraction pass must list
every site, its containing declaration/family, exposure history and either
a frozen local-obligation manifest or a specific exclusion. The initial
single-goal task unit should reject or separately classify multi-goal sites;
it should not silently turn one site into several weighted tasks.

Freeze candidate IDs and admission before running either search arm. Retain
deterministically easy tasks. Require the existing statement/context,
source-diff, axiom, payload and reconstruction checks; eligibility must not
require deterministic certificate recovery. Record all omissions. Apply the
existing mechanically justified inadequate-IR rule to P6-like cases before
model results, and keep them in the extraction/diagnostic accounting.
Unknown witness existence stays unknown; failure of both policies does not
establish impossibility or model reasoning failure.

D1/70 remains a development stratum. No additional paid D1 draws are needed
for the primary cohort. If requested, its new prospective replicates need
their own allocation and table; do not add the two historical successes to
them. Other sites from this already-studied file are still September
exploration, not a contamination-free confirmatory test. Group related
sites by containing declaration and record duplicates instead of presenting
each row or each repeat as an independent discovery.

The paper-facing unit is one task, with eight labeled draw outcomes. Each
draw records proposal presence, certificate verification/consumption,
local closure, containing-declaration validation, axioms, publication
readiness and audit integrity separately. Repeated copies of the same proof
are valid successes, not discarded duplicates. Publication readiness must
not be confused with whether a mathematically valid proof was obtained.

Freeze slot completion as well as transmission counting. A confirmed
pre-send release may retry the **same** slot within a fixed pre-send limit
(proposed three); retain all attempts and cost. A durable grant with an
unknown or partial send consumes that draw's allowance and is not replaced.
A slot exhausted before sending is a system failure with model validity
unobserved. A malformed response or rejected witness is also retained, at
its actual boundary. Do not label an unobserved candidate as an invalid one.
Missing audit evidence prevents an assurance-qualified success even when
a proof file exists. If the whole campaign stops before all slots reach
their preregistered terminal states, publish a partial-collection record
without a complete-cohort headline.

Use three result objects:

1. A task table: deterministic result and time; learned qualified successes
   out of eight; actual prefix discovery at 1/2/4/8; failure stages;
   failure-inclusive tokens, cost and latency; evidence and axiom outcomes.
2. A paired summary: task-weighted single-draw qualified yield, discovery
   gain from repetition, and deterministic-only / learned-only / shared /
   neither counts at each budget. Show each declaration family and each
   task. This one-file census supports no repository-population confidence
   claim; eight repeats do not increase its number of independent families.
3. A conditional witness table: primitive vectors and supports among
   verified draws, first-result matches and bounded-catalogue matches.
   Show the number of verified draws beside diversity so rejection-heavy
   policies do not look diverse by construction.

For complete pools with `n = 8` and `c_i` qualified successes on task `i`,
the subset-average any-success statistic is
`1 - C(8-c_i,k)/C(8,k)`. Average over tasks, never treat `8*m` runs as
`8*m` independent tasks. Under IID within-task trials this is the familiar
unbiased pass@k estimator; without that assumption it is an exact summary
of subsets of the observed pool, not a guarantee about future attempts.
Do not use the plug-in `1-(1-c_i/8)^k` instead. Show actual chronological
prefix discovery and its costs alongside the subset average, since the
latter does not retain attempt order. At `k = n`, it is simply whether the
pool contains a success. [Chen et al., §2.1 and Appendix A](https://arxiv.org/html/2107.03374v2#S2.SS1).

All-eight success is descriptive, not a high-reliability certificate.
All-success subset statistics `C(c_i,k)/C(8,k)` may go in the artifact,
following [Yao et al., §3](https://arxiv.org/html/2406.12045v1#S3), but are
secondary here because a saved, checked proof is reusable. Conditional
candidate-verification rates must show their smaller observed-response
denominator alongside the all-slot system result. Do not remove infrastructure
failures from the system denominator or call them model reasoning errors.

One can derive the **coverage** of a proposed deterministic-then-learned
fallback from these independent arms. Label it an offline counterfactual;
do not present it as an executed hybrid or reuse duplicated preparation
costs as a measured hybrid latency. If deterministic recovery solves
everything, the cohort has shown zero added coverage at that budget. Report
it and measure cost/variability; do not remove the easy tasks to manufacture
a gain. A later broader cohort or deliberately held-out theory boundary is
where a stronger complementarity question belongs.

## Decisions and work before any authorization

- Set eight fixed draws and the primary discovery/system-yield endpoint;
  keep witness diversity secondary.
- Choose the stable-input authorization design; the recommendation is a
  bounded cohort schedule under one reviewed policy, not new signatures
  whose digests change the model input on every draw.
- Extract the complete source census, classify exposure and exclusions,
  assign task/family IDs, and freeze the actual primary membership.
- Freeze both independent search budgets, the finite witness diagnostic,
  block ordering, failure denominators and analysis code. Run that analysis
  on canned all-success, all-failure, mixed, missing-response and rescaled
  witness records before examining cohort outputs.
- Exercise the new task/draw admission and ledger relationships in a canned
  checkpoint; preserve R6-008 unchanged. Then prepare fresh pricing and the
  concrete bounded authorization for review.

The [evidence program](reviews/2026-09-14/cohort_design_evidence.py) issues
no search or provider call. It binds 19 inputs to `4b8a7d9`, recomputes the
historical comparison and planning numbers, checks the two rescaling
examples, and checks the subset formulas against all subsets for each
possible success count at `n = 8`. It does not perform the cohort extraction
or implement the proposed policy.

# R6 synthesis — learned Farkas-witness proposal behind a fixed acceptance boundary

Status: **R6 is closed**, 2026-09-29. No further live spending is authorized or planned under R6.

> **Qualification.** The evaluation of R6-014 is an evaluation under **two post-collection amendments**, not an unchanged preregistered
> one. Both changed only what the frozen live auditor (and, for the second, the collection runner) would accept. Neither changed the
> frozen analysis, a recorded outcome or a run. Each is documented with its timing, cause, controls and review:
> - [amendment 1](R6-014-AMENDMENT-1.md): the policy-directory check, after the first frozen audit of block 1 rejected the collection on
>   layout (`live-evaluation-v2`, with its [erratum](policies/live-evaluation-v2.ERRATUM.md));
> - [amendment 2](R6-014-AMENDMENT-2.md): live pre-send releases and retried slots, after block 2 paused on a pre-send connection failure
>   (`live-evaluation-v3`, `dac9f307…`).

## The question

The cohort was designed ([R6-009 proposal](R6-009-PROPOSAL.md)) to ask: *on a prospectively enumerated downstream workload, how often
does one learned proposal yield an admissible reconstructed proof, what does repetition buy, and where does deterministic recovery already
provide that proof?*

- **The model:** one untrusted model proposes a Farkas witness. It has no tools and makes one stateless request (`gpt-5.4-2026-03-05`
  through the Responses API, reasoning effort medium, contract v2).
- **The acceptance boundary** is fixed:
  1. an independent certificate checker verifies the witness;
  2. a pinned closer consumes it;
  3. the kernel validates the local proof and the whole containing declaration;
  4. the axioms are unchanged ([R6-000](PROTOCOL.md)).

  *Qualified 2026-09-30:* in R6, "consumes" means the closer folded the independently verified certificate and the kernel accepted
  the result. The fold's final step ran `omega` with the goal's hypotheses in scope, so R6 does not establish that the certificate
  alone discharged the contradiction ([qualification 1](R6-QUALIFICATION-1.md)).

## Units: obligations, families and draws

These are three different things, and the result is stated in the first two.

- **Obligations.** The census ([R6-010](R6-010.md)) froze **15 primary obligations**: every `omega` site in one pinned file, VerInf's
  `Bracket.lean`, at one commit.
  - 11 are posable. The frozen SDK refuses the goal form of l098, l101, l158 and l180 before any request ([R6-013](R6-013.md)).
  - Of the 11, **10 are certificate-feasible**, and l170 is the **negative control**: its emitted rows are satisfiable, so no valid
    Farkas certificate exists.
- **Declaration families.** The 15 sites fall in **4 declarations**. This is the independence unit that the frozen analysis binds
  (`REVIEWED_FAMILIES` in [`analysis_r6.py`](analysis_r6.py)).

  | family | sites |
  |---|---|
  | `lift_cell` | l069, l070, l071, l078 |
  | `threshold_unique` | l096, l098, l099, l101 |
  | `cell_value_neutral` | l158, l166, l170, l175, l178, l180 |
  | `Row.s1_noninc` | l204 |

- **Draws.** Each posed obligation received **8 preassigned draws** with byte-identical model input: 88 slots.
  - Draws are repeated attempts on the same obligation. They are **not independent observations of coverage**, and they add no
    families.
  - As R6-010 states, the four families support no repository-population claim.

## Result

**Every certificate-feasible slot produced a verified witness: 80 of 80.** Proof coverage nevertheless remained **six of fifteen primary
obligations**, in **two** declaration families, and it did not change from draw 1 to draw 8.

| obligations | family | learned arm, per draw | deterministic arm ([R6-014 §2](R6-014.md)) |
|---|---|---|---|
| l069, l070, l071, l078 | `lift_cell` | proof at all 8 draws (`term_mode_nat`) | proof |
| l096, l099 | `threshold_unique` | proof at all 8 draws (`term_mode_int`) | backend never invoked |
| l166, l175, l178 | `cell_value_neutral` | verified, then refused at all 8 draws (`nat_closer_int_goal`) | reconstruction refused |
| l204 | `Row.s1_noninc` | verified, then refused at all 8 draws (`nat_closer_int_goal`) | reconstruction refused |
| l170 (negative control) | `cell_value_neutral` | rejected by the verifier at all 8 draws | witness not recovered |
| l098, l101 | `threshold_unique`, not posed | — | backend never invoked |
| l158, l180 | `cell_value_neutral`, not posed | — | l158 reconstruction refused; l180 witness not recovered |

- **Against the deterministic arm**, the learned arm's gain is **l096 and l099 only**. Those are one family, and the arm never reached
  its backend there. On l069–l078 both arms prove the same obligations.
- **On this population and interface, reconstruction constrained coverage, not proposal.** The four closer-unreachable obligations
  received verified witnesses at every draw, and the pinned ℕ closer refused them all.
- **The default reference route** (`site_cvc4_default_closer_v1`, closing through `gated_omega`) is a separate control. It was
  recorded beside the frozen arm and never pooled with it.
  - It closed eight sites: l069–l078, and exactly those four, l166, l175, l178 and l204. It missed l096 and l099.
  - `gated_omega` re-proves the original goal with `omega` once the certificate is accepted
    (`lean-bridge/ProofBroker/Tactic.lean`). It does not consume the certificate. Its closures show that those obligations are
    provable; they do not show that a retained witness can be consumed.
  - No route closed all ten certificate-feasible obligations. This motivates the proposed follow-up below; it is not part of this
    result.
- **What repetition bought** was witness diversity, not coverage.
  - l070 returned four distinct verified witnesses, three of its eight slots matching the classification's certificate.
  - l071 returned two, none matching.
  - Every other verified site returned one witness at every draw, equal to the classification's.
  - Draws 2–8 added six whole-validated slots each, on the same six obligations.
- **The negative control held:** 8 of 8 rejected, no false certificate acceptance, no contradictory observation.
- **Exposure sensitivities:**
  - excluding l070 (the R6-000 control site): 40 of 80 whole-validated slots;
  - excluding the `lift_cell` family: 16 of 56.

Records: the [complete-collection record](R6-014-BLOCK2.md) and [block 1 record](R6-014-BLOCK1.md), and the frozen analysis
[R6-014-BLOCK2-ANALYSIS.json](reviews/2026-09-29/R6-014-BLOCK2-ANALYSIS.json) (`analysis-v3`, `69d93ed7…`; reproduced exactly in
the closeout review).

## Harness: what the audits show

**Accounting** (the live campaign ledger, audited):
- **Reservations:** 89 reservation rows total 9,113,600 µUSD gross. One pre-send release returned 102,400 µUSD, leaving **9,011,200
  µUSD net committed**. That equals the authorization, and nothing is open.
- **Usage:** 108,480 input and 44,886 output tokens, provider-reported. Priced at the frozen rates, that gives a ceiling of 944,490
  µUSD. This is an estimate, not a bill.
- **Pricing:** it was admitted before every reservation, from a capture inside its 24-hour window. Captures that expired while
  reviews were pending were replaced by fresh admitted captures: capture 5 for block 2's authorization, then capture 6 through a pricing
  revision under the same authority.

**Publication evidence:** operator disclosure scans used the real credential as the canary.
- **Block 1:** 101,646 files, no disclosures, 11 runs bound.
- **The complete collection:** 132,450 files, no disclosures, 89 runs bound. Each run is bound by its credential commitment and its seal.
- The credential value was never retained.

**Audits:**
- the frozen live auditor accepted block 1 with 550 cases (amendment 1) and the complete collection with **4,327 cases** (amendment 2);
- each audit ran after its lock verified: `live-evaluation-v2` for block 1 and `live-evaluation-v3` for the complete collection;
- the frozen analysis ran only after acceptance.

**Fail-closed pauses.** Each stopped without spending on an unreviewed state or accepting one.

| event | what stopped | resolution |
|---|---|---|
| block 1, first frozen audit | rejected at `revision:history_bound`, before any per-run case | rejection retained; [amendment 1](R6-014-AMENDMENT-1.md) |
| block 2, incident 1 | an interrupted launch before any reservation; the runner paused on the sealed attempt | moved aside byte-for-byte ([record](reviews/2026-09-28/R6-014-BLOCK2-INCIDENT-1.md)) |
| block 2, pause 1 | a pre-send connection failure; the ledger released the slot; the runner had no retry rule and paused | [amendment 2](R6-014-AMENDMENT-2.md); runner revision 7 checked every existing run before resuming |

- **Never triggered:**
  - the integrity stop on a negative-control acceptance;
  - any unknown or partial send;
  - an exhausted slot.
- **Runner review, block 2:** only reviewed and approved revisions of the block 2 runner transmitted: revision 5, then revision 7.
  Revisions 1–4 and 6 were each repaired after review findings, before any transmission. Block 1 ran under its own runner history.
- **Amendment 2's first review** found two defects before any resumption:
  - contradictory send evidence could still authorize a retry;
  - a restart could skip existing attempts.

  Both were repaired and re-reviewed.

## Methodology

**Rehearse the actual production directory layout and the pre-send failure and retry paths before signing.**

Both post-collection amendments came from paths that no rehearsal had exercised:
- **Directory layout.** Every reviewed fixture kept its policy in a directory of its own, while production signs into the shared
  `policies/`. The first frozen audit met that layout only on the collected block.
- **Pre-send failure.** The live-mode auditor and runner had never met a real pre-send failure, although the ledger had a reviewed
  release-and-retry rule and the rehearsal-mode auditor checked releases.

Neither was a defect in the evidence; both were gaps between what was rehearsed and what production does. In practice:
- sign a disabled copy into a copy of the real directory tree;
- inject each pre-send failure the sender can raise, under the live-mode auditor and runner;
- exercise a restart over a partially collected population;
- do all three before the signature, not after the first collection.

Amendment 2's synthetic sources show that the injection is cheap: the reviewed `untrusted_ca` TLS fixture produced a genuine pre-send
release ([`release_sources.py`](reviews/2026-09-28/release_sources.py)).

## Proposed follow-up, not part of this closeout: R6-015

This would be an **offline** test of a changed reconstruction route on retained evidence. Its question: **can an appropriate closer
construct a proof from the retained certificates?** That means consuming the 32 verified witnesses at l166, l175, l178 and l204 with a
closer suited to their ℤ goals.
- It would be preregistered separately.
- It needs no provider, no credential and no spending.
- The reference route stays a separate control. Its `gated_omega` closures re-prove the goals without the certificate, so they cannot
  answer this question.

It would **not revise R6-014's result**, which stands as recorded under its frozen route.

## Records

| record | contribution |
|---|---|
| [R6-000](PROTOCOL.md) | the deterministic golden episode: frozen task, two acceptance predicates, axiom policy |
| [R6-001](R6-001.md) | fixture proposals through the Farkas boundary |
| [R6-002](R6-002.md) | semantic prompt and envelope binding, canned responses |
| [R6-003](R6-003.md) | provider adapter and outbound HTTP capture |
| [R6-004](R6-004.md) | credential delivery and publication disclosure control |
| [R6-005](R6-005.md) | HTTPS client handoff and proposed live settings |
| [R6-006](R6-006.md), [v2](R6-006-V2.md) | pricing admission before reservation and transport |
| [R6-007](R6-007.md) ([preflight](R6-007-PREFLIGHT.md)) | one authorized live call |
| [R6-008](R6-008.md) … [v7](R6-008-V7.md), [v7 live](R6-008-V7-LIVE.md) | executing guards under a new policy; the first signed live transmission |
| [R6-009 proposal](R6-009-PROPOSAL.md), [R6-009](R6-009.md) … [v3](R6-009-V3.md) | the cohort design; the scientific contract, stable campaign identity, durable slot ancestry |
| [R6-010](R6-010.md) | the census: fifteen frozen site obligations |
| [R6-011](R6-011.md) | site tasks on the frozen stages |
| [R6-012](R6-012.md) | corrected classification, contract C, first site rehearsals |
| [R6-013](R6-013.md) | preparation repaired, closer-specific consumption receipts, every site outcome evidenced |
| [R6-014](R6-014.md) … [v4](R6-014-V4.md) | signing lifecycle, deterministic arm, frozen analysis, live auditor |
| [R6-014 amendment 1](R6-014-AMENDMENT-1.md), [block 1](R6-014-BLOCK1.md) | the directory-layout amendment; block 1 audited and analysed |
| [R6-014 amendment 2](R6-014-AMENDMENT-2.md), [block 2](R6-014-BLOCK2.md) | pre-send releases and retries; the complete collection audited and analysed |

The public adaptation of this synthesis belongs on the website and is kept separate from this record.

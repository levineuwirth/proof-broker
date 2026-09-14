# R6-004 review acceptance and closeout

Review complete on 2026-09-09. The v3 credential checkpoint and corrected outer
recount are accepted at the local canned HTTP scope. The R6-003 requirement for
a credential-channel disclosure control before live-policy freeze is satisfied.
HTTPS/client handoff controls remain required before an externally billed call.

The accepted object is the unchanged
[v3 checkpoint](../../runs/credential-checkpoint-v3/checkpoint.json), using
`credential_http_fixture_v3`, plus the corrected
[outer recount](credential_final_checks.py) and its separately recorded
[five supplementary controls](R6-004-V3-GATE-CONTROLS.json).
The [closeout record](R6-004-CLOSEOUT.json) binds the reviewed source and result
files. Earlier review reports and their failing probe observations remain intact.

## What this review verified

The four frozen suites still contain **67 checks: 26 / 5 / 30 / 6**, with exact
case sets, matching hashes/counts, no duplicates and every recorded check
explicitly passing. The public recount verifies **111 event hashes**, **685
sealed entries** and the five expected native cases. It verifies the exact
**9,986-file** preservation inventory against `ac0f50f` Git objects and the
working tree. The source lock still verifies.

V3 retention excluding the regenerable `final-checks.json` remains **701 files,
8,598,395 apparent bytes, 247 distinct contents and 4,821,969 unique bytes**.
Of the prior review's 730 input hashes, 727 are unchanged. The three changed
inputs are the deliberately revised report, outer recount and unsealed recount
result. The v1 review's 719 checkpoint/policy paths, the v2 review's 717
checkpoint paths, and its two policy/lock files remain unchanged.

Fresh execution during this closeout is recorded in separate populations:

| Population | Result | Evidence |
| --- | --- | --- |
| Five supplementary outer-gate controls | 5 pass | [fresh results](R6-004-CLOSEOUT-GATE-CONTROLS.json) |
| Six existing frozen gate controls | 6 pass against the corrected recount | [fresh results](R6-004-CLOSEOUT-EXISTING-GATES.json) |
| Prior independent review program | All four former provenance mutations reject through the actual public command; its four gate-record corruptions, context and safe-path controls also behave as required | [fresh observations](R6-004-CLOSEOUT-PROBES.json) |
| Additional component and coverage controls | 14 pass | [program](credential_closeout_checks.py), [results](R6-004-CLOSEOUT-COMPONENTS.json) |

The five-control helper exercises the recount/gate-suite composition. The
independent provenance probes invoke the actual CLI, including its final
Python compile-result check. The component controls use observations from an
independently re-audited original tree and isolate one relationship at a time;
they are not fourteen additional native episodes or additions to the frozen
67-check checkpoint. The five native episodes and Lean replay were not rerun.

## The remaining bindings are now enforced

The checkpoint's policy/source-lock hashes are compared with the frozen files.
Its derivation, representations, encoded forms and live-call count are checked
against their authoritative constants. The additional source-lock-only mutation
confirms the second hash check is effective even when the policy hash is valid.

Native-suite seal hashes, scan counts, disclosure counts, log results and
coverage now agree with the corresponding re-audited episode. Separate
disclosure-only, log-only and coverage-only mutations reject at their own
comparisons rather than being hidden behind the scan-count rejection of the
combined control.

Preservation now requires the pinned commit's exact path population and blob
digests, current-tree agreement, and agreement with the preservation-suite
record. A same-size path substitution, a wrong content digest, a false recorded
count and a false recorded base all reject. The empty inventory no longer
produces a vacuous success.

The declared bundle still contains **two expected overlapping findings** in
the rejected reflection control, **zero unexpected findings**, and **zero
findings in publication-accepted episodes**. The two findings identify the
same synthetic Authorization header at offsets 52 and 59 under the header and
token representations. The rejected control is deliberately retained as
research evidence; a blanket clean-bundle claim would be false.

## Original-tree and retained-only coverage are distinct

The complete-checkpoint recount requires the original tree's coverage. An
additional control removes D1's unretained build products without changing any
retained bytes. The standalone episode audit still accepts it, reporting
**185 entries recomputed and eight recorded but unavailable**, out of the
original 193. The complete-checkpoint contract rejects this changed coverage.

Consequently the complete recount is not a clean, retained-only checkout
command. Review retained-only episode evidence with:

```bash
python3 -B experiments/r6/credential_episode.py audit --run-dir experiments/r6/runs/credential-checkpoint-v3/d1_valid
```

Unavailable build products remain explicitly unverified there. Neither that
audit nor this closeout attests compilation, host execution or model inference.
The original-tree public recount and retained-only episode audit have different
coverage claims; both are now recorded and exercised.

## Closeout changes and next step

The [live-policy requirements](../../LIVE-POLICY-REQUIREMENTS.md) now mark the
canned credential control satisfied. The report and protocol link this
closeout, state the coverage scope, and separate the episode's scan-before-seal
from the later checkpoint-bundle scan. Frozen sources, policies, suites and
episode evidence are preserved. No model, real credential, remote endpoint or
native replay was used in this closeout.

Next, freeze model/provider identity, sampling/reasoning settings and
token/retry/monetary limits, and exercise the actual HTTPS/client handoff with
canned responses and synthetic credentials. Keep exact outbound capture,
transport association, certificate validity and inference attestation as
separate claims.

Nothing was committed or pushed during this review closeout.

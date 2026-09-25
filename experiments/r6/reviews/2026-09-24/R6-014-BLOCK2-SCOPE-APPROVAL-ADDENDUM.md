# R6-014 block 2 scope approval — addendum: pricing capture 5

This was recorded on 2026-09-25, after [R6-014-BLOCK2-RUNNER-V5-REVIEW.md](R6-014-BLOCK2-RUNNER-V5-REVIEW.md) approved the block 2 runner
(revision 5, `994bf8bc`). The operator's instruction: "Proceed with the fresh pricing capture and approval addendum, then the separate
authorization step for the recorded scope."

The one change to [R6-014-BLOCK2-SCOPE-APPROVAL.md](R6-014-BLOCK2-SCOPE-APPROVAL.md) is the pricing source.
- **Why:** capture 4 left its admission window at 2026-09-25T08:49:14Z, while the runner was in review.
- **Replacement:** `authorize` uses **`sources/pricing-approved-campaign-5`**, captured 2026-09-25T13:18:50Z by `pricing_capture_v2.py`.
- **Admission:** the production review admits it; see [R6-014-CAPTURE-5-ADMISSION.json](R6-014-CAPTURE-5-ADMISSION.json). The rates, listed
  identifiers, prices and conditions are identical to the approved capture. The only difference is the reviewed prose field
  `model.snapshot_section`.
- **Window:** the capture is admissible until **2026-09-26T13:18:48Z**. The pricing gate checks it again at every reservation, so block 2 must
  be collected before then.

Everything else is unchanged:
- **Recorded values:** approver `Levi Neuwirth`, approval time `2026-09-24T12:55:26Z`, the schedule (eleven sites × 8 draws), and the scope
  and reason texts.
- **Money:** the cumulative authorization of 9,011,200 µUSD.
- **Runner:** the approved revision 5.

**Sandbox check.** A sandbox `authorize` at the real time, on copies of the production authority and ledgers, produces:
- revision 2, 88 transmissions and 9,011,200 µUSD;
- block 1's 11 consumed slots and 1,126,400 µUSD committed, preserved, with nothing open.

Production was confirmed unchanged afterwards.

This addendum does not by itself authorize anything. `authorize` is the separate step that follows.

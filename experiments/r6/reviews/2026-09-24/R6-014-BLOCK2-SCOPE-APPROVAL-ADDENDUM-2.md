# R6-014 block 2 scope approval — addendum 2: pricing capture 6, by a pricing revision

This was recorded on 2026-09-28. Block 2 was authorized on 2026-09-25 (`64e6f9e6`, revision 2, priced from capture 5). The operator then
deferred collection until after travel, "To be safe", and returned today: "we're ready to proceed but will need to refresh." Capture 5 left
its admission window at 2026-09-26T13:18:48Z, before any block 2 slot was reserved.

**The refresh.** The authorized policy is moved onto capture 6 by the production pricing revision, `cohort_contract.revise`.
- It creates revision 3 under the **same** authority: approver, approval time, schedule of eleven sites × 8 draws, 9,011,200 µUSD, and the
  scope text.
- Revision 2 is retained beside the policy, and the live ledger registers revision 3.
- Block 1's eleven consumed slots persist, and revision 2's digest can no longer reserve.
- Nothing about the scope changes, and no new authority is created.

**The capture.** Capture 6 is `sources/pricing-approved-campaign-6`, captured 2026-09-28T20:13:39Z.
- **Admission:** the production review admits it; see [R6-014-CAPTURE-6-ADMISSION.json](R6-014-CAPTURE-6-ADMISSION.json). The rates, listed
  identifiers, prices and conditions are identical, and the only difference is the reviewed prose field `model.snapshot_section`.
- **Freshness:** `revise` does not itself check the capture's age; the pricing gate checks it at every reservation. The signing rule
  (`fresh_capture`) was therefore applied explicitly before the revision.
- **Window:** the capture is admissible until **2026-09-29T20:13:37Z**. Block 2 must be collected before then.

**Sandbox check.** A sandbox `revise`, on copies of the production authority and ledgers, produced:
- revision 3 with the same authority, schedule and money, 88 transmissions and 3 ledger revisions;
- block 1's consumption preserved, with nothing open.

Production was confirmed unchanged afterwards.

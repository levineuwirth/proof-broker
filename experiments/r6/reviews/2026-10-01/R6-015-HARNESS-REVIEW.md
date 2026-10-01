# R6-015 replay harness, revision 1 — review

Supplied by the reviewer in session on 2026-10-01, against harness revision 1 (`ef995231`). It is recorded verbatim below.

---

Request changes before harness approval: three P1 findings and one P2.

  1. P1 — direct replay bypasses the pre-lock guard. experiments/r6/r6-015/replay_episode.py:243 calls execute without checking a lock or plan membership. A synthetic probe reached setup without a lock. Enforce admission at the episode boundary, with 
     an explicit pinned-rehearsal exception. Also derive expected bypass events from the spec’s injection flag and verify their certificate; the receipt currently accepts whichever bypass event appears.

  2. P1 — the lock omits validation and sealing code. experiments/r6/r6-015/replay_campaign.py:44 neither binds nor verifies site_network.py, which supplies final validation and sealing. Modifying a copied version leaves the lock record unchanged.    
     Bind and verify the complete source closure used by these paths, including the census lock itself.

  3. P1 — control 8 does not bind outputs to planned episodes. Its input checks (experiments/r6/r6-015/replay_campaign.py:136) accept a sealed proof despite disagreement in the run’s spec, ID, route, coefficients and injection flag. A changed verdict 
     is also silently skipped if its outcome becomes non-proved, before its seal is checked. Verify seals before branching, bind each run’s spec, packet and receipts to the locked plan, and recheck consumed audit artifacts afterwards.

  4. P2 — the residual command record omits the local target. The recorded argument slice (experiments/r6/r6-015/replay_episode.py:155) selects the whole target and -. Record the complete command, with temporary paths normalized, and its runtime      
     environment.

  The isolated synthetic rehearsal passed all four cases. Keeping preparation unchanged is justified by the fresh-reification guard. Running the frozen audit outside the site stage is acceptable with complete input and subprocess records.

  I approve the two proposed pinned-route rehearsals after these repairs, as a limited pre-lock exception: l069 draw 1 learned and l069 deterministic, bridge 476fab31, constrained option false, injection disabled, separately sealed rehearsal records. 
  They test the harness and are excluded from R6-015 results.

  No retained certificate was read or replayed during this review. The working tree is unchanged.

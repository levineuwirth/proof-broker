# R6-015 replay harness, revision 2 — review

Supplied by the reviewer in session on 2026-10-01, against harness revision 2 (`f26ff76b`, code `1425f84b`). It is recorded
verbatim below.

---

Request one remaining P2 repair before harness approval.

  In experiments/r6/r6-015/replay_campaign.py:77, bound() checks the planned identity but ignores the start record’s lock digest, bridge revision and harness digests. It  
  also doesn’t require episode_finished or compare its outcome and verdict digest with verdict.json.

  Synthetic probes showed that it accepts:

  • A start record naming another lock and bridge.
  • A resealed verdict disagreeing with the terminal event.
  • A sealed run with no terminal event.

  For the last case, control 8 reported passed: true. That probe used the actual binding/control code with synthetic lock and packet providers.

  Pass the verified lock into binding, check the recorded program provenance, require a terminal event matching the verdict’s outcome and digest, and require the seal’s   
  acceptance flag to agree. Apply these checks before branching on outcome.

  The four original reproducers are fixed. Admission and bypass checks passed; copied-source mutations changed the lock record. Both pinned rehearsal records verify,      
  including their byte-identical exports and audit results.

  No retained certificate was replayed during this review, no lock was created, and the working tree is unchanged.

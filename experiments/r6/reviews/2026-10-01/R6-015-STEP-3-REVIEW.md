# R6-015 step 3 — review

Supplied by the reviewer in session on 2026-10-01, against step 3 as committed at `b9f73c4d`. It is recorded verbatim below.

---

Request changes before step-3 approval: one P1 and one P2.

  1. P1 — deterministic control-5 maps and expectations are wrong. In experiments/r6/r6-015/mutations.py:281, the deterministic key assignment follows continue inside the exception handler, so it never runs. Matching reuses the last learned-map key.

     The sealed deterministic packets actually contain:
      • l070: hZ: 2, neg_goal: 1, matching learned draws 2, 6, 7. Its expectation is expected pass.
      • l071: hZ: 2, hzsum: 1, neg_goal: 1, matching no learned map. It gets no expectation.

     Thus the claimed l070 draw-5 identity is incorrect. Compute the deterministic key after successful loading, then regenerate the record and correct the write-up. Add regression checks tying each reported map to its packet.

  2. P2 — integrity failures silently remove episodes. The broad except ValueError at experiments/r6/r6-015/mutations.py:280 treats seal failures and other malformed-input errors as absent certificates. A synthetic seal-failure injection for deterministic l069 produced
     a successful 107-episode plan, marking that certificate unretained.

     Record absence only when explicitly established from verified events. Propagate integrity and decoding failures, and check the expected control-5 coverage.

  The existing driver and checker reproduced the committed outputs byte-for-byte. The 36 measurement certificates, 24 invalid mutations, 25 valid mutations and unit counts check out; reproducibility does not catch the stale-key error.

  No certificate was replayed, no closer ran, and the working tree is unchanged.

# Block 2 runner revision 2 — review

Reviewed `9e0e9d0c` on 2026-09-25. **Not ready for activation or transmission: one P1 and two P2 gaps remain.** The shared fresh/restart gate fixes the original unconditional skip, and all 36 supplied controls reproduce. All eleven unchanged block 1 runs return `continue`. The remaining findings concern evidence the new gate does not check.

1. **P1 — Raw acceptance and contradictory observations are ignored** (`run_block2.py:64–67`, `100–120`). The event chain is checked structurally, but its verification, consumption and kernel observations are not compared with the outcome files. On a copy of l170, changing the `independent_certificate_verdict` event to `accepted: true`, rechaining and resealing, still gives `continue / witness_rejected`, because the certificate file says false. Conversely, a proof whose raw verifier receipt says false continues as a proof. Removing the proof's `reconstruction_finished` receipt also continues. Separately, setting l170's summary `proof_accepted: true` continues as a rejected witness. Each probe attempts the next launch in both fresh and restart modes.

   Apply the frozen raw-acceptance rule across the verifier/consumer/kernel evidence, before classifying an ordinary rejection. Check the required receipts and agreement between raw observations, outcome records and summaries, including the terminal payload. Reuse the reviewed evidence relationships where practical. A valid event hash chain proves byte consistency, not semantic consistency. Contradictions must pause, and a negative-control acceptance must stop even when another record rejects it.

2. **P2 — Seal coverage is not established** (`run_block2.py:52–55`). `all(...)` checks only entries supplied by `retained_sha256`; an empty mapping passes. With that one field replaced by `{}`, both paths continue as a proof. Thus records used by the decision can be entirely outside the seal while `seal_intact` returns true. Require the necessary retained inventory and digest coverage of every record the gate consumes, using the existing seal contract and preserving its explicit optional/ephemeral-file distinctions. Add empty-inventory and individual missing-required-entry controls, not only modified-byte controls.

3. **P2 — The ledger terminal is not joined to the requested slot** (`run_block2.py:81–85`). The gate finds a matching terminal by the reconciliation's reservation ID, then independently checks that the requested task/draw is consumed. It never establishes that these are the same reservation and slot. In a stronger probe using the unmodified, valid 23-row final block 1 ledger and its recomputed state, I replaced l069's reconciliation with l099's genuine reconciliation and resealed the copy. Both fresh and restart paths still continued to l070. No authoritative ledger rows or state were forged in that probe. Bind the reconciliation and its reservation to task, draw, episode and the run's permit; agreement with some consumed ledger row is insufficient.

   The supplied fixtures also obscure this omission: `build()` retargets `search-policy.json` to draw 2 but leaves the original draw-1 reconciliation while synthesizing a consumed draw-2 slot. Make positive fixtures internally consistent at these identities, then mutate one relationship at a time.

The probes run the production `main()` with mocked sender and ledger boundaries, stopping at the next attempted launch. They establish continuation behavior, not acceptance of their mutated evidence by the final auditor. Event mutations are rechained and resealed; contradictory relationships are intentionally preserved. No actual subprocess sender was launched, no real credential was read, and no production authority was changed.

Evidence:
- `R6-014-BLOCK2-RUNNER-V2-REVIEW-CONTROLS.json`: fresh supplied suite, 18 cases × 2 modes = 36, with the recorded outcomes and source hashes reproduced.
- `R6-014-BLOCK2-RUNNER-V2-REVIEW-PROBES.json`: six mutations in both modes.
- `R6-014-BLOCK2-RUNNER-V2-REVIEW-LEDGER.json`: eleven genuine baselines and the genuine foreign-reconciliation probe in both modes.
- `R6-014-BLOCK2-RUNNER-V2-REVIEW-REPRODUCED.json` and `block2_runner_v2_review_probes.py --output <fresh-path>`: combined reproducer, 14 unexpected continuations plus eleven clean baselines.

The v2 evaluation lock still verifies 69 files. Production remains revision 1 with eleven authorized slots. These runner repairs do not require changing the frozen block 1 evidence, analysis or evaluation sources. Keep activation and transmission pending re-review.

Minor reporting correction: `R6-014-BLOCK2-RUNNER-REVISION.md` calls `c1b9c91c` the reviewed runner version; that is the earlier defective version. The implementation reviewed here is `9e0e9d0c`.

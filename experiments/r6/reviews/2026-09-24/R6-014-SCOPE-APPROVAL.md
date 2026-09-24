# R6-014 scope approval (prerequisite 1 of 5)

On 2026-09-24 the operator, Levi Neuwirth, approved the concrete execution scope in conversation: "I am hereby approving #1." The time
of approval is recorded as **2026-09-24T08:49:01Z**. Item #1 is the first remaining prerequisite in
[R6-014-V4.md](../../R6-014-V4.md) §4: "an operator approval of the concrete scope (eleven sites × draw 1)".

The approved scope is block 1 of the planned cohort under the R6-014 decision:
- **Contract and policy:** contract v2, `gpt-5.4-2026-03-05` with its frozen generation settings, cohort v9 (campaign `52f5f113…`).
- **Schedule:** draw 1 for each of the eleven posable sites: bracket-l069, l070, l071, l078, l096, l099, l166, l170, l175, l178 and
  l204. This includes l170, the negative control, and the four sites where reconstruction is refused.
- **Money:** the reservation is 11 × 102,400 = **1,126,400 µUSD** ($1.126400). This is a reservation, not a bill.
- **Retention:** every outcome is kept. Any later block needs separate approval on the same ledger.

These are the values `sign` will be given:

| field | value |
|---|---|
| `approved_by` | `Levi Neuwirth` |
| `approved_utc` | `2026-09-24T08:49:01Z` |
| `schedule` | `{site: 1 for site in cohort_contract.POSABLE}` |
| `scope` | `R6-014 block 1: eleven posable sites x draw 1 under contract v2 (cohort v9); reservation 1,126,400 micro-USD; every outcome retained` |

This approval does not sign, activate or fund anything. The other prerequisites each need their own approval:
- a fresh admitted pricing capture;
- `sign` and activation;
- the credential-bearing run and the operator scan;
- the verified, frozen evaluation.

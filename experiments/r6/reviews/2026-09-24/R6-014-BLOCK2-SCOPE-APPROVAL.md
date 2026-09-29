# R6-014 block 2 scope approval

On 2026-09-24 the operator, Levi Neuwirth, chose "Draws 2–8, all 77 slots" as the next block of the planned cohort. The time of approval
is recorded as **2026-09-24T12:55:26Z**. It is later than block 1's approval (08:49:01Z), as `authorize` requires.

The approved scope:
- **Contract, campaign and ledger:** the same as block 1, under contract v2, `gpt-5.4-2026-03-05`, cohort v9, campaign `52f5f113…`.
- **Schedule:** the eleven posable sites, draws 2 to 8 each. The authorized schedule becomes 8 draws per site, which is the planned design.
- **Consumed slots:** block 1's eleven draw-1 slots stay consumed; they cannot be reserved again.
- **Money:**
  - the reservation grows by 77 × 102,400 = 7,884,800 µUSD;
  - the authorization becomes **9,011,200 µUSD** ($9.011200) for all 88 slots;
  - at block 1's reported usage, the estimated ceiling is about 0.81 USD. This is not a bill.
- **Retention:** every outcome is kept. The frozen pause rules apply to every slot.

These are the values `authorize` will be given:

| field | value |
|---|---|
| `approved_by` | `Levi Neuwirth` |
| `approved_utc` | `2026-09-24T12:55:26Z` |
| `schedule` | `{site: 8 for site in cohort_contract.POSABLE}` |
| `sources` | `sources/pricing-approved-campaign-4` (admissible until 2026-09-25T08:49:14Z) |
| `scope` | `R6-014 block 2: eleven posable sites x draws 2-8 under contract v2 (cohort v9); cumulative reservation 9,011,200 micro-USD; every outcome retained` |
| `reason` | `block 2 of the planned cohort (draws 2-8), approved after block 1 was audited and analysed` |

This approval does not by itself authorize, fund or send anything. The following remain separate:
- `authorize`, which creates the spending authority;
- the credential-bearing runs and the operator scan;
- the evaluation under `live-evaluation-v2`.

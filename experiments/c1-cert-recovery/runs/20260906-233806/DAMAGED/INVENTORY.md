# Pass 20260906-233806 — compact inventory of the damaged outputs

The outputs themselves are **omitted from the repository**; this is the record
of what was there and what state the self-test left it in. The cause and the
fix are in `README.md` next to this file.

`results.json` held **1 case(s)** — B1_true_2p21 — where a
complete pass holds 26.

| category | files | empty after the self-test | bytes on disk |
|---|---|---|---|
| corpus run logs | 182 | 7 | 110,843 |
| IR capture logs | 26 | 26 | 0 |
| carry-comparison logs | 10 | 10 | 0 |
| held-out logs | 42 | 42 | 0 |
| generated Lean | 182 | 0 | 131,927 |
| tracer reports | 29 | 0 | 179,745 |
| negative-check JSON | 0 | 0 | 0 |
| solver scripts | 116 | 0 | 65,890 |
| raw solver proofs | 52 | 0 | 150,834 |
| **total** | **639** | **85** | **639,239** |

The tracer reports survived because the self-test's canary stood in for the
tracer, so `diag.exe` was never invoked; everything the canary *did* stand in
for was truncated to empty, and `run_negchecks.sh` deletes its result file
before each case, so those were removed outright.

Nothing in either report cites this pass for a result. Its successor
`20260907-104934` — and in turn `20260907-113052` — reproduced it, and the
comparison recorded there is identical across all 182 runs, so no claim rests
on the lost files.

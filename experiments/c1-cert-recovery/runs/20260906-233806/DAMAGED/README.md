# This pass's artifacts were damaged by the campaign's own self-test

`tools/test_runner_preflight.sh`, in its first version, ran the real runners
against the real `logs/STAMP` as a positive control. It therefore overwrote
and deleted evidence belonging to this pass (20260906-233806), while exiting 0
(R6 checkpoint-2 final review, issue 1). Measured damage:

| artifact | state after the self-test |
|---|---|
| `results.json` | reduced to 1 case (`B1_true_2p21`) of 26 |
| `carrylift/*.log` | 10 of 10 truncated to empty |
| `heldout/*.log` | 42 of 42 truncated to empty |
| `irlogs/*.log` | 26 of 26 truncated to empty |
| `logs/*.log` (corpus) | 7 of 182 truncated to empty |
| `raw/20260906-233806/*.negcheck.json` | 30 of 30 deleted |
| `raw/20260906-233806/*.report.json` | 29 intact (the tracer itself was never invoked) |

The self-test now runs entirely inside temporary campaign roots and asserts
that `runs/`, `raw/` and `logs/` are byte-identical before and after.

This directory is kept as the record of the damage. The pass was regenerated
under a new stamp; see `logs/STAMP`. The earlier pass `20260906-215904`
was never touched and keeps its original provenance — but it was produced
with the stale diagnostics described in checkpoint-2 §1b.3, so it is not a
substitute for the regenerated one.

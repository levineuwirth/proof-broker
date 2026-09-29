# Pass 20260906-215904 — complete, with a stale-diagnostics caveat

This pass is retained in full as the historical comparison: it is the first
checkpoint-2 pass, and the one every later pass is measured against to show
that the corrections changed no corpus outcome.

**Read its diagnostic artifacts with care.** The Lean side is sound — the
probe loaded a correctly rebuilt `proof_broker_ffi.so`, so `runs/.../logs/`,
`carrylift/`, `heldout/` and `results.json` report the SDK this pass was
meant to exercise. But two statically linked diagnostics were stale when it
ran (checkpoint-2 report §1b.3):

| artifact | state during this pass |
|---|---|
| `raw/20260906-215904/*.report.json` | produced by a `diag.exe` predating the budget change; it still printed the superseded 20,000-support cap |
| `raw/20260906-215904/*.negcheck.json` | produced by a `negcheck.exe` predating the repair entirely, so it reports tier 0 where the repaired SDK gives tier 1, and marks mutation testing "not applicable" |

So: the closure results here are citable; the tracer and negative-check
outputs here are **not**, and the reports do not cite them. The regenerated
figures live in `20260907-113052`. `tools/build_diag.sh` now makes this class
of error impossible — every entry point rebuilds and hashes its executables
before any timing, and `tools/probe.sh` refuses to load a shared object the
ledger does not record.

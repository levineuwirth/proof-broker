# Pass 20260907-104934 — retained as a comparison only

The bulk outputs of this pass (per-run logs, solver scripts, raw proofs,
tracer reports) are **omitted from the repository**. What it is kept for is
the single fact below, and the binary identities that make that fact mean
something.

## Why it exists

It was the regeneration run after the checkpoint-2 final review. It was then
superseded by `20260907-113052`, run after one further change: removing a trailing space
inside a doc comment in `farkas_search.ml`. That edit is not semantic, but it
recompiles the library and relinks the FFI shared object, and this campaign's
whole argument is that evidence produced against one binary must not be
reported against another. So the pass was re-run rather than reasoned about.

## The binaries

| pass | `sdk/ffi/proof_broker_ffi.so` |
|---|---|
| `20260907-104934` | `101912b5b4aec7746858469af66c56bbb6982aaa4b9ca4e9da6fbe0f74391c16` |
| `20260907-113052` | `fa0733db6d375be67da6f9e8127668b06b49fd7633d188bef28ee1b851eb8c8b` |

## The comparison

Every closer of every case, both passes:

* cases × closers compared: **182** (26 cases × 7 closers)
* differences: **0**

All outcomes identical. The relink changed nothing observable, which is what a comment-only edit should do — established by measurement rather than assumed.

The omitted files are gone and are not recoverable: a new run produces new
evidence, not these bytes. What survives is the ability to re-run the
experiment — `python3 tools/run.py runs/<stamp>` performs a full pass and
`tools/summarize.py` builds its tables — and the fact recorded above, which is
the only thing this pass was kept for. Nothing in either report cites the
omitted files.

# Phase 0 retrospective

Phase 0 closed with the FFI spike landing end-to-end and the three boundary
decisions (envelope shape, method dispatch, JSON-for-v1) locked in
`sdk/FFI_CONVENTIONS.md`. This note captures what was harder and easier
than expected, which assumptions held up, and what I'd reshape if I were
starting Phase 0 over today. It's deliberately written while the work is
fresh, because the value is asymmetric: most of these observations are
unrecoverable a month from now.

## Easier than expected

The OCaml C-FFI discipline (`CAMLparam` / `CAMLlocal` / `caml_callback_exn` /
`Is_exception_result` / `CAMLreturnT`) came together without a
diagnostic loop on the GC boundary — no segfaults, no early "RSS
climbing during smaller runs" moments, no exception-propagation
surprises. The 100k-iteration RSS reading (5.7 MB stable, no drift)
confirmed the steady-state behavior matches the discipline. GC-boundary
leaks are the class of bug I most expected to chase; not chasing any
was the single most reassuring data point in the spike. Related:
dune's `(modes (native shared_object))` produced a self-contained
`.so` (OCaml runtime + foreign stubs together) without a build-system
fight, which removed a category of friction I had budgeted for.

The 54 µs/call JSON marshaling cost was on the comfortable side of the
budget. Back-of-envelope, even a pathological 100-pass dispatch is 5 ms of
FFI overhead — well inside any interactive use case. The CBOR question
that loomed over delta §2.1 became a "switch later if profiling flags
it" lever rather than a near-term decision. (Correction, audit #18:
this retro originally added "and the codec abstraction made that lever
cheap to keep alive" — there is no such abstraction; the eventual
CBOR switch is a real refactor, not a toggle. See
`sdk/FFI_CONVENTIONS.md` §Wire format. The lever is still "switch
later if profiling flags it"; its cost was understated.)

## Harder than expected

The Lake side of the boundary was where the time actually went. Two
specific frictions: Lake's `staticLibDir` field naming (older docs and
LLM training data both still reference `nativeLibDir`, which fails
silently-then-loudly), and Lean 4.30's bundled lld defaulting to
`--no-allow-shlib-undefined`, which rejects linking against
`proof_broker_ffi.so`'s transitive glibc symbol references. The first
was a half-hour of API spelunking; the second was the kind of error
where the failure mode (`undefined reference: pthread_*@GLIBC_2.32`)
points at a real-looking missing symbol that's actually a linker policy
artifact. Both are now documented in FFI_CONVENTIONS.md "Toolchain
notes" with a pointer comment in `lean-bridge/lakefile.lean`, but a
new contributor hitting either cold would lose a day.

The history-shaping step — splitting the spike's working tree into a
clean foundation/spike commit pair — was more procedural friction than
expected, mostly because four files (delta.md, FFI_CONVENTIONS.md,
validate.yml, .gitignore) had been edited in both phases and needed
careful state-shuttling to get the foundation commit to the right
intermediate state.

The generalizable lesson: if the commit boundary matters, separate the
work physically (branches or stashes) rather than reconstructing it
after the fact. The Lake/lld notes above are this codebase's specific
toolchain potholes; this one is the engineering discipline that
applies to any phase where the audit trail will be read back.

## Assumptions that held up

The architecturally risky call from delta.md — that an OCaml shared
library is a viable host for the Lean side — held. The Phase 0 spike
exercised the predicate that decision rests on (Lean → C → OCaml →
C → Lean round-trip with typed error propagation and stable memory),
and the predicate is true. The §5 condition-6 off-ramp ("Phase 0
surfaces architectural changes that disrupt FFI assumptions") did not
trigger; the lone wrinkle was operational, not architectural.

The +20–30% Lean-side FFI tax estimate also held — Phase 0 came in at
the low end. The number I'd actually flag, though, is that the
estimate's load-bearing concern was always boundary-design durability
across diverse ops, not marshaling code volume. The marshaling code is
small and now front-loaded; the recalibration that matters happens at
the Phase 1 mid-checkpoint, when we can see what fraction of total
Lean-plugin effort the FFI machinery represents across a real
distribution of ops.

The methodological assumption that spike-first sequencing produces
better-informed conventions also held. The spike landed with
`pb_ffi_roundtrip_ir` as a named entry point and the dispatcher
convention was locked in review afterward. This was the right
sequencing — locking the convention before writing concrete FFI code
would have been an under-informed call, and the trade-off (ABI
stability versus per-method coordination tax) was clearer with one
entry point in front of us than it would have been in the abstract.
The cost is that the first entry point doesn't follow the convention
it later established, which folds in cleanly when the second op lands.
The lesson, if any, is the smaller one: when a convention is being
locked retroactively, expect to migrate the precedent-setter and
budget for it.

## What I'd do differently

I'd hit the lakefile linker friction earlier with a minimum reproducer
(a stub `.so` exporting one function) before wiring the real shim.
Discovering both Lake API drift and the lld/glibc quirk in the same
session, with the full glue compiled, made it harder to isolate which
problem was which. A 20-line scaffold first would have saved the "is
this my C ABI or my linker?" diagnostic loop.

## Carried into Phase 1

Open questions:

- Whether the shim should be stateful (parsed registry held across
  calls) or stateless (each call re-loads). Decision deferred to
  whoever writes the dispatcher.
- The Lean-side error type that `{"status": "error", ...}` envelopes
  decode into. Likely an inductive matching the `kind` values in
  FFI_CONVENTIONS.md, with a catch-all for forward compatibility.

Planned actions:

- Phase 1 mid-checkpoint recalibration of the +20–30% band against
  real Lean-plugin effort distribution, once enough ops have landed
  to make the FFI-vs-total ratio meaningful.

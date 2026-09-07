# Can Proof Broker recover checked arithmetic certificates when coefficient sizes and context change?

Campaign directory, two checkpoints. **Checkpoint 1** (`reports/checkpoint-1.md`)
freezes the corpus, reproduces the failure and diagnoses it, changing nothing
outside this directory. **Checkpoint 2** (`reports/checkpoint-2.md`) implements
the repair the diagnosis supports; it is the only part that touches shipped
files, and §7 there lists every one of them.

Everything in this directory is diagnostic: it links `proof_broker` read-only,
no dependency version moves, and the completed VerInf case study is read but
never written.

    baseline/    what the campaign loads, by hash (before and after)
    corpus/      the frozen corpus: the case study's four in-context sites
                 (carrylift/, copied verbatim) + tools/corpus.py's enumeration
    heldout/     held-out variants — defined at checkpoint 1 and NOT run
                 there; run once at checkpoint 2, after the repair was designed
    ir/          IR capture files and the captured IR documents
    diag/        the OCaml stage tracer, the negative-check gate, the
                 exact-recovery cost sweep
    tools/       probe, generators, runners, the drift check, the gate, and
                 the build preflight every entry point runs first
    runs/<stamp>/  one campaign pass: generated Lean, logs, parsed results
    raw/<stamp>/   per-case SMT-LIB scripts, solver stdout, raw proofs, reports
    reports/     checkpoint-1.md (the diagnosis, corrected after review) and
                 checkpoint-2.md (the repair)

`logs/STAMP` names the pass currently in force; the `logs/STAMP.*` files name
the earlier ones. The SDK changed between several of them, so their numbers
are not interchangeable and each report says which pass every table comes
from. What is retained of each pass is below.

## The passes, and what is kept of each

Five campaign passes were run. Each is retained at the level its evidence is
actually cited at; nothing cited by a report has been omitted, and the omitted
files are regenerable from `tools/` (see Reproduce). `raw/` and `runs/` are
NOT blanket-ignored — every retained pass is versioned explicitly.

| pass | kept | why |
|---|---|---|
| `20260906-204453` | **complete** | checkpoint 1's evidence: the pre-repair diagnosis, its tables, its tracer output and raw solver proofs |
| `20260906-215904` | **complete**, + `CAVEAT.md` | the historical comparison every later pass is measured against. Its Lean results are citable; its tracer and negative-check outputs were produced by stale binaries and are not (checkpoint-2 §1b.3) |
| `20260906-233806` | `DAMAGED/README.md` + `DAMAGED/INVENTORY.md` | this pass was destroyed by the campaign's own preflight self-test. The record of the damage is the artifact; the damaged outputs are omitted |
| `20260907-104934` | `COMPARISON.md` | superseded by the final pass after a comment-only edit relinked the FFI. Kept for the binary hashes and the 182-run comparison showing identical outcomes; bulk outputs omitted |
| `20260907-113052` | **complete** | the final evidence, produced against the exact binaries committed here |

## Reproduce

    cd experiments/c1-cert-recovery
    tools/baseline.sh                       # record what is loaded, by hash
    python3 tools/truth_check.py            # recompute every case's truth value
    tools/build_diag.sh                     # sdk/ffi + sdk/lib + the three
                                            # diagnostics, hashed into
                                            # logs/diag_binaries.txt
    tools/test_runner_preflight.sh          # every entry point refuses to run
                                            # when that build fails. Runs in
                                            # throwaway campaign roots and
                                            # asserts runs/ raw/ logs/ are
                                            # byte-identical afterwards — an
                                            # earlier version overwrote the
                                            # evidence it was testing
    tools/probe.sh --olean tools/PbDiag.lean
    python3 tools/gen.py runs/<stamp>
    tools/capture_ir.sh                     # IR capture + stage trace
    python3 tools/run.py runs/<stamp>       # the closer comparison
    python3 tools/summarize.py runs/<stamp> # the tables in the report

`tools/probe.sh` is the case study's probe with this campaign's `.build`
appended to `LEAN_PATH`; the case study's own olean directory is read-only on
that path so `import RmsNormBracket.Model` resolves to the exact artifact
whose hash `baseline/artifacts-before.txt` records.

## What "closes" means here

A case is PROVED by a closer only when the closer closed the ORIGINAL goal
and the file elaborated (probe `EXIT=0`) under the existing axiom policy. A
solver `unsat`, a minted certificate, and `proof_broker`'s `gated_omega`
closer are none of them evidence that a certificate was consumed — the
report keeps those columns separate. A timeout or a refused reconstruction is
UNKNOWN, never a counterexample; the only refutations in this campaign are
the four cases whose statements are false by construction, and their falsity
is established in `tools/truth_check.py`, not by a prover's failure.

# R6-015 analysis, control 3 and lock, revision 2 — review

Supplied by the reviewer in session on 2026-10-01, against revision 2 (`6f674b8a`). It is recorded verbatim below.

---

Request two remaining P2 repairs before locking. The negative-control and control-5 repairs pass.

  1. The after-check verifies seal files, but not the artifacts they seal. experiments/r6/r6-015/analysis.py:310 misses changes to run files when seal.json stays unchanged.

     A synthetic end-to-end probe changed an export after the control checks and still returned complete_success, with 36 consumed. A separate probe using the actual binding and file hashes confirmed that rechecking sealed
     files detects the change.

     Revalidate each run’s retained files against its unchanged seal after analysis, including exports, residuals, events and kernel reports.

  2. Incomplete or contradictory execution metadata still passes.
      • experiments/r6/r6-015/control3.py:53 accepts a missing constrained exit: None == 0 is false. Removing that field still produced complete_success. Require an integer, nonzero exit.

      • experiments/r6/r6-015/analysis.py:167 checks the audit tool and input hashes but ignores its recorded command. A record describing another executable, synthetic mode, wrong targets/toolchain and exit 1 still passed
        beneath an exit-0 report. Validate the complete command against the planned targets and frozen environment, and require its exit code to agree with the report.

  The supplied analysis, binding and mutation tests pass. The lock still computes over 34 Python files, 18 data files, 6 binaries and 108 source entries; all consumed artifacts match their source seals.

  No lock was written, no closer ran, nothing was replayed, and the working tree is unchanged.

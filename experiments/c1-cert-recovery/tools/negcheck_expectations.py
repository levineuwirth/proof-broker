"""Emit `<case-id> <expectation>` for the negative-check runner.

`expectation` is one of:

  unsat   the statement is true; the gate asserts nothing about the adapters
          (a true goal whose reified IR was weakened can still answer sat, and
          the runner tracks that separately rather than failing on it)
  sat     the statement is FALSE by construction; no adapter may mint a cert
  no-ir   the reifier refuses this case outright, so there is no IR to check;
          the gate asserts that no IR exists (an IR appearing here would mean
          the corpus and the campaign have drifted apart)


`sat` is set ONLY for cases whose statement is false by construction,
and the source of that judgement is tools/corpus.py's `truth` field, which
tools/truth_check.py recomputes arithmetically. A prover's failure never sets
it. The four in-context sites (O1..O4) are obligations of a proof that
elaborates, so they are true.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import corpus

# Cases the reifier refuses before any IR exists, with the reason. Keeping
# this list explicit (rather than "skip whatever has no IR file") is what makes
# a newly-refused case a gate failure instead of a silent gap.
NO_IR = {
    "P3_le_pred": "goal contains truncated \u2115 subtraction (P - 1); the "
                  "\u2115\u2192\u2124 specialization refuses it by name",
}

# Hand-built regression fixtures (tools/make_fixtures.py). Each pins a defect
# the gate must keep catching; all are contradictory, so `unsat`.
FIXTURES = ["F1_lra_strict_ground", "F2_eq_negative_multiplier"]

def main():
    rows = [("O%d" % n, "unsat") for n in (1, 2, 3, 4)]
    rows += [(f, "unsat") for f in FIXTURES]
    for c in corpus.CASES:
        if c["id"] in NO_IR:
            rows.append((c["id"], "no-ir"))
        else:
            rows.append((c["id"], "sat" if c["truth"] == "FALSE" else "unsat"))
    for cid, exp in rows:
        print("%s %s" % (cid, exp))

if __name__ == "__main__":
    main()

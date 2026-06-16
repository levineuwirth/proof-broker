#!/usr/bin/env python3
"""Property-based fuzzer for the walker's clausal-resolution algebra.

The Alethe walkers (`binaryResolve` in lean-bridge, `binary_resolve` in
rocq-bridge) reconstruct a kernel proof of a resolution step's clause by
a left-fold of binary resolution over the premises. The *proof* lives in
the kernel; the *clause* each step computes -- which literals survive --
is pure list algebra, and that is where bugs hide. The 636-step
`lia_pigeonhole3` scale point exposed one: the resolvent concatenated the
two premises' leftovers without deduping, so a literal surviving in both
appeared twice and a later single complement only cancelled one copy,
leaving an un-resolvable `X ∨ X`.

This module re-implements that clause algebra exactly as the walkers do
(first complementary pivot, erase both, dedup preserving first-occurrence
order) and fuzzes it against an INDEPENDENT truth-table oracle:

  * soundness   -- every binary resolvent is a logical consequence of its
                   two premises (a wrong pivot / dropped literal / kept
                   pivot would break entailment);
  * set algebra -- no resolvent carries a duplicate literal (the dedup
                   regression guard: the pigeonhole bug exactly);
  * refutation  -- if the n-ary fold reaches the empty clause, the premise
                   set is genuinely unsatisfiable.

Literals are modelled as signed atoms (atom id + polarity); two literals
are complementary iff same atom, opposite polarity. This abstracts away
the syntactic `(not …)` matching (double-negation pivots are covered by
the bridge unit tests) and isolates the clause algebra. The model mirrors
the walkers; the committed corpus replay (`CorpusReplay.v` /
`ProofBroker.Test`, incl. pigeonhole) is what pins the real walkers to
this same algebra. Deterministic: a fixed seed makes any failure
reproducible.

Run: `python tools/fuzz_resolution.py` (exit 1 on any property violation).
"""
from __future__ import annotations

import itertools
import random
import sys

# A literal is a signed int: +a / -a for atom a >= 1. A clause is a list
# of literals (order-significant, mirroring the walker's `List Sexp`).
Lit = int
Clause = list


def first_pivot(a: Clause, b: Clause) -> tuple[int, int] | None:
    """First (i, j), scanning a then b, with complementary literals --
    exactly the walkers' pivot search."""
    for i, la in enumerate(a):
        for j, lb in enumerate(b):
            if la == -lb:
                return (i, j)
    return None


def dedup(xs: Clause) -> Clause:
    """First-occurrence-preserving dedup -- the walkers' resolvent set
    normalization."""
    out: Clause = []
    for x in xs:
        if x not in out:
            out.append(x)
    return out


def binary_resolve(a: Clause, b: Clause) -> Clause | None:
    """The walkers' binary resolvent: erase the pivot pair from each
    premise, concatenate, dedup. None if there is no pivot."""
    piv = first_pivot(a, b)
    if piv is None:
        return None
    i, j = piv
    leftover = [x for k, x in enumerate(a) if k != i] \
        + [x for k, x in enumerate(b) if k != j]
    return dedup(leftover)


def resolve_chain(clauses: list[Clause]) -> Clause | None:
    """Left-fold binary resolution over a premise list, as `elabResolution`
    / `elab_resolution` do. None if any step lacks a pivot."""
    acc = clauses[0]
    for nxt in clauses[1:]:
        acc = binary_resolve(acc, nxt)
        if acc is None:
            return None
    return acc


# --- independent oracle: boolean entailment over the atom alphabet ------

def atoms_of(clauses: list[Clause]) -> list[int]:
    return sorted({abs(l) for c in clauses for l in c})


def clause_true(c: Clause, assign: dict[int, bool]) -> bool:
    # Empty clause is False (the refutation target); otherwise a disjunction.
    return any((l > 0) == assign[abs(l)] for l in c)


def models(clauses: list[Clause]):
    """Every total assignment over the clauses' atoms (small instances)."""
    ats = atoms_of(clauses)
    for bits in itertools.product([False, True], repeat=len(ats)):
        yield dict(zip(ats, bits))


def entails(premises: list[Clause], conclusion: Clause) -> bool:
    """`conclusion` holds in every model of all `premises`."""
    universe = premises + [conclusion]
    ats = atoms_of(universe)
    for bits in itertools.product([False, True], repeat=len(ats)):
        assign = dict(zip(ats, bits))
        if all(clause_true(p, assign) for p in premises) \
                and not clause_true(conclusion, assign):
            return False
    return True


def is_unsat(clauses: list[Clause]) -> bool:
    return not any(all(clause_true(c, m) for c in clauses) for m in models(clauses))


# --- random generation --------------------------------------------------

def rand_clause(rng: random.Random, n_atoms: int, max_width: int) -> Clause:
    width = rng.randint(1, max_width)
    lits: Clause = []
    for _ in range(width):
        a = rng.randint(1, n_atoms)
        lits.append(a if rng.random() < 0.5 else -a)
    return lits


def rand_clause_set(rng: random.Random) -> list[Clause]:
    n_atoms = rng.randint(2, 5)
    n_clauses = rng.randint(2, 6)
    return [rand_clause(rng, n_atoms, max_width=4) for _ in range(n_clauses)]


# --- properties ---------------------------------------------------------

_PASS = 0
_FAIL = 0


def _check(cond: bool, label: str, detail: str = "") -> None:
    global _PASS, _FAIL
    if cond:
        _PASS += 1
    else:
        _FAIL += 1
        print(f"FAIL  {label}  {detail}")


def fuzz(rng: random.Random, rounds: int) -> None:
    for _ in range(rounds):
        cs = rand_clause_set(rng)
        # Binary-resolvent properties over an adjacent pair.
        a, b = cs[0], cs[1]
        r = binary_resolve(a, b)
        if r is not None:
            _check(len(r) == len(set(r)), "no-dup",
                   f"resolvent {r} of {a},{b} has duplicates")
            _check(entails([a, b], r), "sound",
                   f"{r} not entailed by {a},{b}")
        # n-ary fold: a reached empty clause must mean genuine unsat.
        chain = resolve_chain(cs)
        if chain == []:
            _check(is_unsat(cs), "refutation",
                   f"empty clause from satisfiable set {cs}")


def regression_dedup_matters() -> None:
    """A shared-literal refutation that the deduping fold closes but a
    no-dedup fold cannot -- the pigeonhole bug in miniature. Documents
    exactly what the `no-dup` property guards."""
    # (1 ∨ 2), (1 ∨ -2), (-1): resolve first two on 2/-2 -> (1 ∨ 1);
    # dedup -> (1); resolve with (-1) -> []. Without dedup, (1 ∨ 1)
    # resolves with (-1) to (1), never empty.
    cs = [[1, 2], [1, -2], [-1]]
    _check(resolve_chain(cs) == [], "regression-dedup",
           "deduping fold should reach the empty clause")
    _check(is_unsat(cs), "regression-unsat", "the set is unsat")

    def no_dedup_resolve(a, b):
        piv = first_pivot(a, b)
        if piv is None:
            return None
        i, j = piv
        return [x for k, x in enumerate(a) if k != i] \
            + [x for k, x in enumerate(b) if k != j]

    acc = cs[0]
    for nxt in cs[1:]:
        acc = no_dedup_resolve(acc, nxt)
    _check(acc != [], "regression-no-dedup-fails",
           "without dedup the fold must NOT reach empty (residual literal) "
           "-- proving the no-dup property is load-bearing")


def main() -> int:
    rng = random.Random(0xA1E7E)  # fixed seed: reproducible CI
    fuzz(rng, rounds=20000)
    regression_dedup_matters()
    print(f"{_PASS} property checks passed, {_FAIL} failed "
          f"(20000 fuzz rounds + regression).")
    return 1 if _FAIL else 0


if __name__ == "__main__":
    sys.exit(main())

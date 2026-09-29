"""Independent recomputation of every corpus case's truth value.

The `truth` field in tools/corpus.py is a claim; this file is the arithmetic
that backs it, written out per case rather than parsed out of the Lean text
(a parser that agreed with the generator would only be checking itself).
For each case: the largest value the goal's left-hand side can take under the
stated hypotheses, against P. `omega` on the same statement is the second,
kernel-checked opinion; the two must agree.
"""
P = 18446744069414584321

# id -> (description, sup of LHS over the hypothesis box, strict?)
#   strict=True  : goal is  LHS < RHS, so TRUE iff sup_LHS < RHS  (sup attained)
TABLE = {
    "O5_site2_isolated":   ("2^18 * v, v <= 2^42-1",       2**18 * (2**42 - 1), P),
    "O6_E4":               ("g1l + 2^18*B under the window", None, None),
    "V1_chain_support5":   ("x0 <= x1 <= x2 <= x3 <= 0 |- x0 <= 0", None, None),
    "V2_chain_support7":   ("a six-link chain |- x0 <= 0", None, None),
    "C1_coef_1":           ("1 * v",                        1 * (2**42 - 1), P),
    "C2_coef_2":           ("2 * v",                        2 * (2**42 - 1), P),
    "C3_coef_3":           ("3 * v",                        3 * (2**42 - 1), P),
    "C4_coef_4":           ("4 * v",                        4 * (2**42 - 1), P),
    "C5_coef_5":           ("5 * v",                        5 * (2**42 - 1), P),
    "C6_coef_8":           ("8 * v",                        8 * (2**42 - 1), P),
    "C7_coef_2p10":        ("2^10 * v",                     2**10 * (2**42 - 1), P),
    "C8_coef_2p18":        ("2^18 * v",                     2**18 * (2**42 - 1), P),
    "P1_decimal_coef":     ("262144 * v",                   262144 * (2**42 - 1), P),
    "P2_operand_order":    ("v * 2^18",                     (2**42 - 1) * 2**18, P),
    "P3_le_pred":          ("2^18 * v <= P-1",              2**18 * (2**42 - 1), P - 1 + 1),
    "P4_prime_literal":    ("2^18 * v < <numeral>",         2**18 * (2**42 - 1), P),
    "P5_plain_nat":        ("2^18 * v (v : Nat)",           2**18 * (2**42 - 1), P),
    "P6_hyp_le":           ("2^18 * v, v <= 2^42-1",        2**18 * (2**42 - 1), P),
    "R1_reorder":          ("2^18 * v",                     2**18 * (2**42 - 1), P),
    "R2_redundant3":       ("2^18 * v",                     2**18 * (2**42 - 1), P),
    "R3_site2_in_context": ("2^18 * v",                     2**18 * (2**42 - 1), P),
    "R4_redundant6":       ("2^18 * v",                     2**18 * (2**42 - 1), P),
    "B1_true_2p21":        ("2^21 * v",                     2**21 * (2**42 - 1), P),
    "B2_false_2p22":       ("2^22 * v",                     2**22 * (2**42 - 1), P),
    "B3_false_wide_bound": ("2^18 * v, v <= 2^46-1",        2**18 * (2**46 - 1), P),
    "B4_true_exact":       ("2^18 * v, v <= 70368744161280", 2**18 * 70368744161280, P),
    # held out (defined, not run)
    "H1_hyp_succ_form":    ("2^18 * v, v+1 <= 2^42",        2**18 * (2**42 - 1), P),
    "H2_coef_2p36":        ("2^36 * v, v <= 2^24-1",        2**36 * (2**24 - 1), P),
    "H3_two_large_coefs":  ("2^18*a + 2^36*b",
                            2**18 * (2**18 - 1) + 2**36 * (2**24 - 1), P),
    "H4_mixed_small_large": ("3*a + 2^18*b",
                             3 * (2**40 - 1) + 2**18 * (2**40 - 1), P),
    "H5_false_2p19":       ("2^19 * v, v <= 2^45-1",        2**19 * (2**45 - 1), P),
    "H6_other_limb_width": ("2^19 * v, v <= 2^41-1",        2**19 * (2**41 - 1), P),
}

if __name__ == "__main__":
    import sys
    sys.path.insert(0, "tools")
    import corpus
    bad = 0
    for c in corpus.CASES + corpus.HELD_OUT:
        desc, sup, rhs = TABLE[c["id"]]
        if sup is None:
            print(f"  {c['id']:<24} {c['truth']:<5} (symbolic window; "
                  f"checked by omega only)")
            continue
        computed = "TRUE" if sup < rhs else "FALSE"
        ok = computed == c["truth"]
        bad += 0 if ok else 1
        print(f"  {c['id']:<24} {c['truth']:<5} computed={computed:<5} "
              f"{'ok' if ok else 'MISMATCH'}   sup={sup} rhs={rhs}")
    print(f"\n{bad} mismatch(es)")
    raise SystemExit(1 if bad else 0)

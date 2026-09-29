"""The frozen corpus for checkpoint 1, explicitly enumerated.

Every case is one obligation. `truth` is the mathematical status of the
statement, established independently of any prover (`tools/truth_check.py`
recomputes each bound in Python and `omega` is run on every case as a second,
kernel-checked opinion). `relation` says what a variant does to the ORIGINAL
obligation it is derived from:

  same      — meaning-preserving: same mathematical content, different
              presentation or a larger (still consistent) assumption set.
              A closer that handles the original should handle this.
  changed   — a different obligation: the constant, the bound or the truth
              value moved. Not a fairness violation, the point of the axis.

`held_out` cases are DEFINED here and deliberately NOT RUN at this
checkpoint (see reports/checkpoint-1.md §Held-out). They exist so a later
repair can be evaluated on obligations whose results did not steer this
checkpoint's diagnosis.
"""

ZMOD_BINDERS = "(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)"

CASES = [
    # ---- the originals, verbatim from the completed VerInf case study ----
    dict(id="O5_site2_isolated", group="original", truth="TRUE", relation="—",
         source="verinf case study experiments/S2_minimal_pbq.lean (verbatim)",
         binders=ZMOD_BINDERS,
         goal="2^18 * g_hi.val < P",
         note="SITE 2 of carry_stage_lift_production, isolated. The refusal "
              "the case study recorded."),
    dict(id="O6_E4", group="original", truth="TRUE", relation="—",
         source="verinf case study experiments/E4_proof_broker_term.lean (verbatim)",
         binders="(g1l B G2w : ℕ) (hg1l : g1l < 2^18) (hBG : B < 2^G2w)\n    "
                 "(hG2w : 2^(36 + G2w) ≤ 2^62) (hsplit : 2^(36 + G2w) = 2^36 * 2^G2w)\n    "
                 "(hP : P = 18446744069414584321)",
         goal="g1l + 2^18 * B < P",
         note="The related 2^18-multiplier bound that DOES reconstruct, in a "
              "richer context."),

    # ---- preserved coverage: witnesses ABOVE the sparse rescue's support
    #      bound, which the DENSE search currently finds (C1 review, finding 1)
    dict(id="V1_chain_support5", group="coverage", truth="TRUE", relation="—",
         source="C1 review, finding 1 — a witness whose support exceeds "
                "`Farkas_search.max_support`",
         binders="(x0 x1 x2 x3 : \u2124) (h1 : x0 \u2264 x1) (h2 : x1 \u2264 x2)\n    "
                 "(h3 : x2 \u2264 x3) (h4 : x3 \u2264 0)",
         goal="x0 \u2264 0",
         note="the witness is coefficient 1 on each of h1..h4 AND neg_goal — "
              "support 5. Variable cancellation forces all five equal, so no "
              "smaller-support witness exists. The dense enumeration finds it "
              "today (5 inputs at bound 3 = 4^5 = 1024 candidates, inside the "
              "budget); the sparse rescue, capped at support 4, could not. "
              "REGRESSION: any change to the fallback must keep this at "
              "tier 1."),
    dict(id="V2_chain_support7", group="coverage", truth="TRUE", relation="—",
         source="V1 lengthened, to pin coverage well above the support bound",
         binders="(x0 x1 x2 x3 x4 x5 : \u2124) (h1 : x0 \u2264 x1) (h2 : x1 \u2264 x2)\n    "
                 "(h3 : x2 \u2264 x3) (h4 : x3 \u2264 x4) (h5 : x4 \u2264 x5)\n    "
                 "(h6 : x5 \u2264 0)",
         goal="x0 \u2264 0",
         note="support 7; dense space 4^7 = 16384, still inside the budget"),

    # ---- coefficient magnitude: CHANGES the obligation ----
    *[dict(id=f"C{i}_coef_{name}", group="coefficient", truth="TRUE",
           relation="changed", source="O5 with the multiplier replaced",
           binders=ZMOD_BINDERS, goal=f"{lit} * g_hi.val < P",
           note=f"multiplier {val}"
                + (" — identical statement to O5 (determinism check)" if val == 262144 else ""))
      for i, (name, lit, val) in enumerate(
          [("1", "1", 1), ("2", "2", 2), ("3", "3", 3), ("4", "4", 4),
           ("5", "5", 5), ("8", "8", 8), ("2p10", "2^10", 1024),
           ("2p18", "2^18", 262144)], start=1)],

    # ---- presentation: MEANING-PRESERVING w.r.t. O5 ----
    dict(id="P1_decimal_coef", group="presentation", truth="TRUE", relation="same",
         source="O5 with 2^18 written as its decimal literal",
         binders=ZMOD_BINDERS, goal="262144 * g_hi.val < P",
         note="does the literal-vs-power spelling change the reified IR?"),
    dict(id="P2_operand_order", group="presentation", truth="TRUE", relation="same",
         source="O5 with the product's operands swapped",
         binders=ZMOD_BINDERS, goal="g_hi.val * 2^18 < P",
         note="commutativity of the multiplication in the goal"),
    dict(id="P3_le_pred", group="presentation", truth="TRUE", relation="same",
         source="O5 with `< P` written as `≤ P - 1`",
         binders=ZMOD_BINDERS, goal="2^18 * g_hi.val ≤ P - 1",
         note="strict vs loose presentation of the same ℕ fact"),
    dict(id="P4_prime_literal", group="presentation", truth="TRUE", relation="same",
         source="O5 with P replaced by its numeral in the GOAL",
         binders=ZMOD_BINDERS, goal="2^18 * g_hi.val < 18446744069414584321",
         note="removes the definition-unfolding pass from the pipeline"),
    dict(id="P5_plain_nat", group="presentation", truth="TRUE", relation="same",
         source="O5 with a plain ℕ variable instead of a ZMod `.val`",
         binders="(v : ℕ) (hv : v < 2^42) (hP : P = 18446744069414584321)",
         goal="2^18 * v < P",
         note="free variable instead of an opaque nonlinear atom + its "
              "nonnegativity hypothesis"),
    dict(id="P6_hyp_le", group="presentation", truth="TRUE", relation="same",
         source="O5 with the range check written `≤ 2^42 - 1`",
         binders="(g_hi : ZMod P) (hhi : g_hi.val ≤ 2^42 - 1) "
                 "(hP : P = 18446744069414584321)",
         goal="2^18 * g_hi.val < P",
         note="strict vs loose presentation of the same range check"),

    # ---- context: MEANING-PRESERVING (reorder / add true assumptions) ----
    dict(id="R1_reorder", group="context", truth="TRUE", relation="same",
         source="O5 with the hypotheses in the other order",
         binders="(g_hi : ZMod P) (hP : P = 18446744069414584321) "
                 "(hhi : g_hi.val < 2^42)",
         goal="2^18 * g_hi.val < P",
         note="hypothesis order only"),
    dict(id="R2_redundant3", group="context", truth="TRUE", relation="same",
         source="O5 plus three unused true range facts from the same carry stage",
         binders="(q S g_lo g_hi : ZMod P) (hq : q.val ≤ 2^42) (hS : S.val < 2^18)\n    "
                 "(hlo : g_lo.val < 2^18) (hhi : g_hi.val < 2^42)\n    "
                 "(hP : P = 18446744069414584321)",
         goal="2^18 * g_hi.val < P",
         note="redundant context, all of it true and none of it needed"),
    dict(id="R3_site2_in_context", group="context", truth="TRUE", relation="same",
         source="the hypotheses actually in scope at SITE 2 of "
                "carry_stage_lift_production, written standalone",
         binders="(q S g_lo g_hi : ZMod P) (hq : q.val ≤ 2^42) (hS : S.val < 2^18)\n    "
                 "(hlo : g_lo.val < 2^18) (hhi : g_hi.val < 2^42)\n    "
                 "(hP : P = 18446744069414584321) (h2L : (2:ℕ)^18 < P)\n    "
                 "(hpow : ((2:ZMod P)^18).val = 2^18)",
         goal="2^18 * g_hi.val < P",
         note="the four ZMod-equation hypotheses of the real proof are omitted: "
              "the reifier drops them (`proposition outside the reifiable "
              "fragment`), so this should reify to the SAME IR as in-context "
              "O2 — the run checks that by hash"),
    dict(id="R4_redundant6", group="context", truth="TRUE", relation="same",
         source="O5 plus six unrelated true linear ℕ facts",
         binders="(g_hi : ZMod P) (hhi : g_hi.val < 2^42)\n    "
                 "(a b c d e f : ℕ) (ha : a < 7) (hb : b < 11) (hc : c < 13)\n    "
                 "(hd : d < 17) (he : e < 19) (hf : f < 23)\n    "
                 "(hP : P = 18446744069414584321)",
         goal="2^18 * g_hi.val < P",
         note="widens the compiled-input count without touching the obligation"),

    # ---- boundary, true and deliberately false ----
    dict(id="B1_true_2p21", group="boundary", truth="TRUE", relation="changed",
         source="O5 with multiplier 2^21 (2^21·(2^42−1) = 2^63 − 2^21 < P)",
         binders=ZMOD_BINDERS, goal="2^21 * g_hi.val < P",
         note="last power-of-two multiplier that is still true at this bound"),
    dict(id="B2_false_2p22", group="boundary", truth="FALSE", relation="changed",
         source="O5 with multiplier 2^22 (2^22·(2^42−1) = 2^64 − 2^22 ≥ P)",
         binders=ZMOD_BINDERS, goal="2^22 * g_hi.val < P",
         note="DELIBERATELY FALSE. A closer that 'succeeds' here is unsound; "
              "a closer that fails here has produced no counterexample to "
              "anything."),
    dict(id="B3_false_wide_bound", group="boundary", truth="FALSE", relation="changed",
         source="O5 with the range check widened to 2^46",
         binders="(g_hi : ZMod P) (hhi : g_hi.val < 2^46) "
                 "(hP : P = 18446744069414584321)",
         goal="2^18 * g_hi.val < P",
         note="DELIBERATELY FALSE (2^18·(2^46−1) = 2^64 − 2^18 ≥ P)"),
    dict(id="B4_true_exact", group="boundary", truth="TRUE", relation="changed",
         source="O5 with the range check at the exact edge",
         binders="(g_hi : ZMod P) (hhi : g_hi.val ≤ 70368744161280) "
                 "(hP : P = 18446744069414584321)",
         goal="2^18 * g_hi.val < P",
         note="tight: 2^18·70368744161280 = P − 1. The Farkas residual is 1."),
]

# ---- held out: DEFINED, NOT RUN at this checkpoint --------------------
HELD_OUT = [
    dict(id="H1_hyp_succ_form", truth="TRUE", relation="same",
         binders="(g_hi : ZMod P) (hhi : g_hi.val + 1 ≤ 2^42) "
                 "(hP : P = 18446744069414584321)",
         goal="2^18 * g_hi.val < P",
         note="the range check in successor form"),
    dict(id="H2_coef_2p36", truth="TRUE", relation="changed",
         binders="(v : ZMod P) (hv : v.val < 2^24) (hP : P = 18446744069414584321)",
         goal="2^36 * v.val < P",
         note="a different (coefficient, bound) pair with the same product size"),
    dict(id="H3_two_large_coefs", truth="TRUE", relation="changed",
         binders="(a b : ZMod P) (ha : a.val < 2^18) (hb : b.val < 2^24)\n    "
                 "(hP : P = 18446744069414584321)",
         goal="2^18 * a.val + 2^36 * b.val < P",
         note="two multipliers, both far above the enumeration bound"),
    dict(id="H4_mixed_small_large", truth="TRUE", relation="changed",
         binders="(a b : ZMod P) (ha : a.val < 2^40) (hb : b.val < 2^40)\n    "
                 "(hP : P = 18446744069414584321)",
         goal="3 * a.val + 2^18 * b.val < P",
         note="one multiplier inside the enumeration bound, one far outside"),
    dict(id="H5_false_2p19", truth="FALSE", relation="changed",
         binders="(v : ZMod P) (hv : v.val < 2^45) (hP : P = 18446744069414584321)",
         goal="2^19 * v.val < P",
         note="DELIBERATELY FALSE (2^19·(2^45−1) = 2^64 − 2^19 ≥ P)"),
    dict(id="H6_other_limb_width", truth="TRUE", relation="changed",
         binders="(g_hi : ZMod P) (hhi : g_hi.val < 2^41) "
                 "(hP : P = 18446744069414584321)",
         goal="2^19 * g_hi.val < P",
         note="the same carry-stage shape at LIMB_W = 19"),
]

CLOSERS = {
    "omega": "omega",
    "grind": "grind",
    "pb": "proof_broker",
    "pbterm": "proof_broker_term",
    "pbterm_z3": "proof_broker_term [z3]",
    "pbterm_cvc5": "proof_broker_term [cvc5]",
    "pbterm_cvc4": "proof_broker_term [cvc4]",
}

PREAMBLE = """import RmsNormBracket.Model
import ProofBroker
import ProofBrokerMathlib

set_option profiler true
set_option linter.unusedVariables false

open RmsNorm
"""


def render(case, closer_key, closer_tactic):
    return (
        f"/-\n"
        f"{case['id']} — closer: {closer_tactic}\n"
        f"group={case['group']}  truth={case['truth']}  relation={case['relation']}\n"
        f"source: {case['source']}\n"
        f"note: {case['note']}\n"
        f"\n"
        f"GENERATED by tools/corpus.py. One obligation per file; the imports,\n"
        f"options and statement are identical across every closer of this case,\n"
        f"so the only difference inside a comparison is the tactic.\n"
        f"-/\n"
        + PREAMBLE
        + f"\nexample {case['binders']} :\n    {case['goal']} := by\n  {closer_tactic}\n"
    )


def render_dump(case):
    return (
        f"/-\n{case['id']} — IR CAPTURE ONLY (pb_dump_ir, then omega).\n"
        f"Proves nothing that the corpus files do not; it exists so the OCaml\n"
        f"diagnostic can be driven on exactly the IR the tactic would dispatch.\n-/\n"
        + PREAMBLE.replace("import ProofBrokerMathlib",
                           "import ProofBrokerMathlib\nimport PbDiag")
        + f"\nexample {case['binders']} :\n    {case['goal']} := by\n"
        f"  pb_dump_ir \"ir/{case['id']}.json\"\n"
        + ("  omega\n" if case["truth"] == "TRUE" else
           "  -- the goal is FALSE by construction: the capture is the point,\n"
           "  -- and `sorry` here is an admission, never a proof.\n  sorry\n")
    )

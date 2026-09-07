/-
O6_E4 — IR CAPTURE ONLY (pb_dump_ir, then omega).
Proves nothing that the corpus files do not; it exists so the OCaml
diagnostic can be driven on exactly the IR the tactic would dispatch.
-/
import RmsNormBracket.Model
import ProofBroker
import ProofBrokerMathlib
import PbDiag

set_option profiler true
set_option linter.unusedVariables false

open RmsNorm

example (g1l B G2w : ℕ) (hg1l : g1l < 2^18) (hBG : B < 2^G2w)
    (hG2w : 2^(36 + G2w) ≤ 2^62) (hsplit : 2^(36 + G2w) = 2^36 * 2^G2w)
    (hP : P = 18446744069414584321) :
    g1l + 2^18 * B < P := by
  pb_dump_ir "ir/O6_E4.json"
  omega

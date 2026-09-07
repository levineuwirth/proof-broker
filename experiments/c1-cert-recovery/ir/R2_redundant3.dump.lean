/-
R2_redundant3 — IR CAPTURE ONLY (pb_dump_ir, then omega).
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

example (q S g_lo g_hi : ZMod P) (hq : q.val ≤ 2^42) (hS : S.val < 2^18)
    (hlo : g_lo.val < 2^18) (hhi : g_hi.val < 2^42)
    (hP : P = 18446744069414584321) :
    2^18 * g_hi.val < P := by
  pb_dump_ir "ir/R2_redundant3.json"
  omega

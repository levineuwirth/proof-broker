/-
R4_redundant6 — IR CAPTURE ONLY (pb_dump_ir, then omega).
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

example (g_hi : ZMod P) (hhi : g_hi.val < 2^42)
    (a b c d e f : ℕ) (ha : a < 7) (hb : b < 11) (hc : c < 13)
    (hd : d < 17) (he : e < 19) (hf : f < 23)
    (hP : P = 18446744069414584321) :
    2^18 * g_hi.val < P := by
  pb_dump_ir "ir/R4_redundant6.json"
  omega

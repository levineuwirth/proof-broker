/-
B2_false_2p22 — IR CAPTURE ONLY (pb_dump_ir, then omega).
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

example (g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321) :
    2^22 * g_hi.val < P := by
  pb_dump_ir "ir/B2_false_2p22.json"
  -- the goal is FALSE by construction: the capture is the point,
  -- and `sorry` here is an admission, never a proof.
  sorry

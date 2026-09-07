/-
V1_chain_support5 — IR CAPTURE ONLY (pb_dump_ir, then omega).
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

example (x0 x1 x2 x3 : ℤ) (h1 : x0 ≤ x1) (h2 : x1 ≤ x2)
    (h3 : x2 ≤ x3) (h4 : x3 ≤ 0) :
    x0 ≤ 0 := by
  pb_dump_ir "ir/V1_chain_support5.json"
  omega

/-
Lib root for the optional Mathlib-flavored extension. Importing
this module pulls in the `ReifierExt` registration that activates
LRA support for `proof_broker` (Real reifier + linarith closer).

The core `ProofBroker` lib does NOT import this module and stays
Mathlib-free — projects that only need LIA support don't pay the
Mathlib build cost.
-/

import ProofBroker
import ProofBrokerMathlib.Tactic

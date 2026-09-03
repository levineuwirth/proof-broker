/-
Parallel-elaboration stress herd (C4 ROUND 3 finding 1).

Thirty declarations, each with its own numeral-body def and its own
nonlinear ℕ atom, elaborated with Lean v4.32's default parallel
declaration elaboration. Every example runs the REAL `Reify.buildIR`
(no dispatch — `reify_stress_test` asserts the per-call atom/def
table sizes) and then closes by `omega`. Under the pre-fix
module-level accumulator refs this file trips the assertions (or
dies in `buildIR` with `unsupported_symbol`) with high probability
per build — the demo's headline file failed 10/33 runs on exactly
this race; with the per-call `ReifyAcc` it is deterministic. Do NOT
add `set_option Elab.async false` here: the parallelism IS the test.
-/

import ProofBroker

namespace ProofBroker.TestStress

def PBs0 : Nat := 1000003
example (x y : Nat) (h : x * y ≤ PBs0) : x * y ≤ PBs0 + 1 := by
  reify_stress_test 1 1
  omega

def PBs1 : Nat := 1000004
example (x y : Nat) (h : x * y ≤ PBs1) : x * y ≤ PBs1 + 2 := by
  reify_stress_test 1 1
  omega

def PBs2 : Nat := 1000005
example (x y : Nat) (h : x * y ≤ PBs2) : x * y ≤ PBs2 + 3 := by
  reify_stress_test 1 1
  omega

def PBs3 : Nat := 1000006
example (x y : Nat) (h : x * y ≤ PBs3) : x * y ≤ PBs3 + 4 := by
  reify_stress_test 1 1
  omega

def PBs4 : Nat := 1000007
example (x y : Nat) (h : x * y ≤ PBs4) : x * y ≤ PBs4 + 5 := by
  reify_stress_test 1 1
  omega

def PBs5 : Nat := 1000008
example (x y : Nat) (h : x * y ≤ PBs5) : x * y ≤ PBs5 + 6 := by
  reify_stress_test 1 1
  omega

def PBs6 : Nat := 1000009
example (x y : Nat) (h : x * y ≤ PBs6) : x * y ≤ PBs6 + 7 := by
  reify_stress_test 1 1
  omega

def PBs7 : Nat := 1000010
example (x y : Nat) (h : x * y ≤ PBs7) : x * y ≤ PBs7 + 8 := by
  reify_stress_test 1 1
  omega

def PBs8 : Nat := 1000011
example (x y : Nat) (h : x * y ≤ PBs8) : x * y ≤ PBs8 + 9 := by
  reify_stress_test 1 1
  omega

def PBs9 : Nat := 1000012
example (x y : Nat) (h : x * y ≤ PBs9) : x * y ≤ PBs9 + 10 := by
  reify_stress_test 1 1
  omega

def PBs10 : Nat := 1000013
example (x y : Nat) (h : x * y ≤ PBs10) : x * y ≤ PBs10 + 11 := by
  reify_stress_test 1 1
  omega

def PBs11 : Nat := 1000014
example (x y : Nat) (h : x * y ≤ PBs11) : x * y ≤ PBs11 + 12 := by
  reify_stress_test 1 1
  omega

def PBs12 : Nat := 1000015
example (x y : Nat) (h : x * y ≤ PBs12) : x * y ≤ PBs12 + 13 := by
  reify_stress_test 1 1
  omega

def PBs13 : Nat := 1000016
example (x y : Nat) (h : x * y ≤ PBs13) : x * y ≤ PBs13 + 14 := by
  reify_stress_test 1 1
  omega

def PBs14 : Nat := 1000017
example (x y : Nat) (h : x * y ≤ PBs14) : x * y ≤ PBs14 + 15 := by
  reify_stress_test 1 1
  omega

def PBs15 : Nat := 1000018
example (x y : Nat) (h : x * y ≤ PBs15) : x * y ≤ PBs15 + 16 := by
  reify_stress_test 1 1
  omega

def PBs16 : Nat := 1000019
example (x y : Nat) (h : x * y ≤ PBs16) : x * y ≤ PBs16 + 17 := by
  reify_stress_test 1 1
  omega

def PBs17 : Nat := 1000020
example (x y : Nat) (h : x * y ≤ PBs17) : x * y ≤ PBs17 + 18 := by
  reify_stress_test 1 1
  omega

def PBs18 : Nat := 1000021
example (x y : Nat) (h : x * y ≤ PBs18) : x * y ≤ PBs18 + 19 := by
  reify_stress_test 1 1
  omega

def PBs19 : Nat := 1000022
example (x y : Nat) (h : x * y ≤ PBs19) : x * y ≤ PBs19 + 20 := by
  reify_stress_test 1 1
  omega

def PBs20 : Nat := 1000023
example (x y : Nat) (h : x * y ≤ PBs20) : x * y ≤ PBs20 + 21 := by
  reify_stress_test 1 1
  omega

def PBs21 : Nat := 1000024
example (x y : Nat) (h : x * y ≤ PBs21) : x * y ≤ PBs21 + 22 := by
  reify_stress_test 1 1
  omega

def PBs22 : Nat := 1000025
example (x y : Nat) (h : x * y ≤ PBs22) : x * y ≤ PBs22 + 23 := by
  reify_stress_test 1 1
  omega

def PBs23 : Nat := 1000026
example (x y : Nat) (h : x * y ≤ PBs23) : x * y ≤ PBs23 + 24 := by
  reify_stress_test 1 1
  omega

def PBs24 : Nat := 1000027
example (x y : Nat) (h : x * y ≤ PBs24) : x * y ≤ PBs24 + 25 := by
  reify_stress_test 1 1
  omega

def PBs25 : Nat := 1000028
example (x y : Nat) (h : x * y ≤ PBs25) : x * y ≤ PBs25 + 26 := by
  reify_stress_test 1 1
  omega

def PBs26 : Nat := 1000029
example (x y : Nat) (h : x * y ≤ PBs26) : x * y ≤ PBs26 + 27 := by
  reify_stress_test 1 1
  omega

def PBs27 : Nat := 1000030
example (x y : Nat) (h : x * y ≤ PBs27) : x * y ≤ PBs27 + 28 := by
  reify_stress_test 1 1
  omega

def PBs28 : Nat := 1000031
example (x y : Nat) (h : x * y ≤ PBs28) : x * y ≤ PBs28 + 29 := by
  reify_stress_test 1 1
  omega

def PBs29 : Nat := 1000032
example (x y : Nat) (h : x * y ≤ PBs29) : x * y ≤ PBs29 + 30 := by
  reify_stress_test 1 1
  omega

end ProofBroker.TestStress

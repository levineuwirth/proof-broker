/-
Parallel-elaboration stress herd (C4 ROUND 3 High; role re-scoped at
ROUND 4 finding 1).

Thirty NAMED theorems (v4.32 elaborates named theorems
asynchronously; anonymous `example`s it does not — measured 0/435
overlapping `buildIR` windows as examples vs 10/435 as theorems),
each with its own numeral-body def and nonlinear ℕ atom, each
running the REAL `Reify.buildIR` (no dispatch) and asserting its
per-call table sizes via `reify_stress_test`, then closing by
`omega`.

HONEST ROLE: this file EXERCISES concurrent per-call accumulators —
it is not a reliable regression catcher. Measured catch rates with
shared refs restored: 0/30 builds on the ROUND 4 anonymous-example
form; on THIS named-theorem form (ROUND 5), 0/20 under the
all-four-shared mutation and 0/10 under the natDefs-only one — a
dispatch-free `buildIR` window is ~1.5 ms; the demo file raced
because its windows span live solver round trips. The fix's pin is
two-part: `reify_acc_isolation_test` (runtime, the constructor) and
`tools/check.py`'s `check_lean_reify_isolation` (source, the module
state + call-site discipline).
-/

import ProofBroker

namespace ProofBroker.TestStress

def PBs0 : Nat := 1000003
theorem pb_stress_0 (x y : Nat) (h : x * y ≤ PBs0) :
    x * y ≤ PBs0 + 1 := by
  reify_stress_test 1 1
  omega

def PBs1 : Nat := 1000004
theorem pb_stress_1 (x y : Nat) (h : x * y ≤ PBs1) :
    x * y ≤ PBs1 + 2 := by
  reify_stress_test 1 1
  omega

def PBs2 : Nat := 1000005
theorem pb_stress_2 (x y : Nat) (h : x * y ≤ PBs2) :
    x * y ≤ PBs2 + 3 := by
  reify_stress_test 1 1
  omega

def PBs3 : Nat := 1000006
theorem pb_stress_3 (x y : Nat) (h : x * y ≤ PBs3) :
    x * y ≤ PBs3 + 4 := by
  reify_stress_test 1 1
  omega

def PBs4 : Nat := 1000007
theorem pb_stress_4 (x y : Nat) (h : x * y ≤ PBs4) :
    x * y ≤ PBs4 + 5 := by
  reify_stress_test 1 1
  omega

def PBs5 : Nat := 1000008
theorem pb_stress_5 (x y : Nat) (h : x * y ≤ PBs5) :
    x * y ≤ PBs5 + 6 := by
  reify_stress_test 1 1
  omega

def PBs6 : Nat := 1000009
theorem pb_stress_6 (x y : Nat) (h : x * y ≤ PBs6) :
    x * y ≤ PBs6 + 7 := by
  reify_stress_test 1 1
  omega

def PBs7 : Nat := 1000010
theorem pb_stress_7 (x y : Nat) (h : x * y ≤ PBs7) :
    x * y ≤ PBs7 + 8 := by
  reify_stress_test 1 1
  omega

def PBs8 : Nat := 1000011
theorem pb_stress_8 (x y : Nat) (h : x * y ≤ PBs8) :
    x * y ≤ PBs8 + 9 := by
  reify_stress_test 1 1
  omega

def PBs9 : Nat := 1000012
theorem pb_stress_9 (x y : Nat) (h : x * y ≤ PBs9) :
    x * y ≤ PBs9 + 10 := by
  reify_stress_test 1 1
  omega

def PBs10 : Nat := 1000013
theorem pb_stress_10 (x y : Nat) (h : x * y ≤ PBs10) :
    x * y ≤ PBs10 + 11 := by
  reify_stress_test 1 1
  omega

def PBs11 : Nat := 1000014
theorem pb_stress_11 (x y : Nat) (h : x * y ≤ PBs11) :
    x * y ≤ PBs11 + 12 := by
  reify_stress_test 1 1
  omega

def PBs12 : Nat := 1000015
theorem pb_stress_12 (x y : Nat) (h : x * y ≤ PBs12) :
    x * y ≤ PBs12 + 13 := by
  reify_stress_test 1 1
  omega

def PBs13 : Nat := 1000016
theorem pb_stress_13 (x y : Nat) (h : x * y ≤ PBs13) :
    x * y ≤ PBs13 + 14 := by
  reify_stress_test 1 1
  omega

def PBs14 : Nat := 1000017
theorem pb_stress_14 (x y : Nat) (h : x * y ≤ PBs14) :
    x * y ≤ PBs14 + 15 := by
  reify_stress_test 1 1
  omega

def PBs15 : Nat := 1000018
theorem pb_stress_15 (x y : Nat) (h : x * y ≤ PBs15) :
    x * y ≤ PBs15 + 16 := by
  reify_stress_test 1 1
  omega

def PBs16 : Nat := 1000019
theorem pb_stress_16 (x y : Nat) (h : x * y ≤ PBs16) :
    x * y ≤ PBs16 + 17 := by
  reify_stress_test 1 1
  omega

def PBs17 : Nat := 1000020
theorem pb_stress_17 (x y : Nat) (h : x * y ≤ PBs17) :
    x * y ≤ PBs17 + 18 := by
  reify_stress_test 1 1
  omega

def PBs18 : Nat := 1000021
theorem pb_stress_18 (x y : Nat) (h : x * y ≤ PBs18) :
    x * y ≤ PBs18 + 19 := by
  reify_stress_test 1 1
  omega

def PBs19 : Nat := 1000022
theorem pb_stress_19 (x y : Nat) (h : x * y ≤ PBs19) :
    x * y ≤ PBs19 + 20 := by
  reify_stress_test 1 1
  omega

def PBs20 : Nat := 1000023
theorem pb_stress_20 (x y : Nat) (h : x * y ≤ PBs20) :
    x * y ≤ PBs20 + 21 := by
  reify_stress_test 1 1
  omega

def PBs21 : Nat := 1000024
theorem pb_stress_21 (x y : Nat) (h : x * y ≤ PBs21) :
    x * y ≤ PBs21 + 22 := by
  reify_stress_test 1 1
  omega

def PBs22 : Nat := 1000025
theorem pb_stress_22 (x y : Nat) (h : x * y ≤ PBs22) :
    x * y ≤ PBs22 + 23 := by
  reify_stress_test 1 1
  omega

def PBs23 : Nat := 1000026
theorem pb_stress_23 (x y : Nat) (h : x * y ≤ PBs23) :
    x * y ≤ PBs23 + 24 := by
  reify_stress_test 1 1
  omega

def PBs24 : Nat := 1000027
theorem pb_stress_24 (x y : Nat) (h : x * y ≤ PBs24) :
    x * y ≤ PBs24 + 25 := by
  reify_stress_test 1 1
  omega

def PBs25 : Nat := 1000028
theorem pb_stress_25 (x y : Nat) (h : x * y ≤ PBs25) :
    x * y ≤ PBs25 + 26 := by
  reify_stress_test 1 1
  omega

def PBs26 : Nat := 1000029
theorem pb_stress_26 (x y : Nat) (h : x * y ≤ PBs26) :
    x * y ≤ PBs26 + 27 := by
  reify_stress_test 1 1
  omega

def PBs27 : Nat := 1000030
theorem pb_stress_27 (x y : Nat) (h : x * y ≤ PBs27) :
    x * y ≤ PBs27 + 28 := by
  reify_stress_test 1 1
  omega

def PBs28 : Nat := 1000031
theorem pb_stress_28 (x y : Nat) (h : x * y ≤ PBs28) :
    x * y ≤ PBs28 + 29 := by
  reify_stress_test 1 1
  omega

def PBs29 : Nat := 1000032
theorem pb_stress_29 (x y : Nat) (h : x * y ≤ PBs29) :
    x * y ≤ PBs29 + 30 := by
  reify_stress_test 1 1
  omega

end ProofBroker.TestStress

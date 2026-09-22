import Mathlib
import PreparationCapture

namespace R6Diff

def K : ℕ := 7

theorem obligation (c c' : Int) (hlt : c < c') : c ≤ c' - 1 := by
  r6_prepare "R6Diff.obligation.r6_site" "unsafe_name"

end R6Diff

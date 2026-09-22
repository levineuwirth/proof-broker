import Mathlib
import PreparationCapture

namespace R6Diff

def K : ℕ := 7

theorem obligation (c_ c' : Int) (hlt : c_ < c') : c_ ≤ c' - 1 := by
  r6_prepare "R6Diff.obligation.r6_site" "collision_with_safe_name"

end R6Diff

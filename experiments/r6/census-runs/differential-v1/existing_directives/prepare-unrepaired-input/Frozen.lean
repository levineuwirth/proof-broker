import Mathlib
import PreparationCapture

namespace R6Diff

def K : ℕ := 7

theorem obligation (x : ℕ) (hK : R6Diff.K = 7) (hx : x < R6Diff.K) : x < 8 := by
  r6_prepare "R6Diff.obligation.r6_site" "existing_directives"

end R6Diff

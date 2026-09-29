import Mathlib
import ProposalCapture

namespace R6Diff

def K : ℕ := 7

theorem obligation (c_ c' : Int) (hlt : c_ < c') : c_ ≤ c' - 1 := by
  r6_capture_proposal "R6Diff.obligation.r6_site" "collision_with_safe_name"

end R6Diff

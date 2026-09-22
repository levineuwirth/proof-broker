import Mathlib
import ProposalCapture

namespace R6Diff

def K : ℕ := 7

theorem obligation (c c' : Int) (hlt : c < c') : c ≤ c' - 1 := by
  r6_capture_proposal "R6Diff.obligation.r6_site" "unsafe_name"

end R6Diff

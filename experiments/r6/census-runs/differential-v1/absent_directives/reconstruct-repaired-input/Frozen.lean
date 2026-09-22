import Mathlib
import ProposalCapture

namespace R6Diff

def K : ℕ := 7

theorem obligation (a b : Int) (h : a ≤ b) : a ≤ b + 1 := by
  r6_capture_proposal "R6Diff.obligation.r6_site" "absent_directives"

end R6Diff

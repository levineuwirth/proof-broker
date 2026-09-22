import Mathlib
import ProposalCapture

namespace R6Diff

def K : ℕ := 7

theorem obligation (x : ℕ) (hK : R6Diff.K = 7) (hx : x < R6Diff.K) : x < 8 := by
  r6_capture_proposal "R6Diff.obligation.r6_site" "existing_directives"

end R6Diff

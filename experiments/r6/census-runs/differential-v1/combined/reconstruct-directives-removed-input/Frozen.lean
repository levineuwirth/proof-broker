import Mathlib
import ProposalCapture

namespace R6Diff

def K : ℕ := 7

theorem obligation (c_ c' : Int) (hlt : c_ < c') : c_ ≤ c' + 1 := by
  have : c_ ≤ c' := by omega
  have : c' ≤ c' + 1 := by omega
  r6_capture_proposal "R6Diff.obligation.r6_site" "combined"

end R6Diff

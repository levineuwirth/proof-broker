import Mathlib
import ProposalCapture

namespace R6Diff

def K : ℕ := 7

theorem obligation (a b : Int) (h : a ≤ b) : a ≤ b + 2 := by
  have : a ≤ b := h
  have : b ≤ b + 1 := by omega
  r6_capture_proposal "R6Diff.obligation.r6_site" "duplicate_this"

end R6Diff

import LRX.Small4
import LRX.Small5
import LRX.Small6

namespace LRX

/-- The sharp bound is proved unconditionally here for every size from 4 to 6. -/
theorem sharp_ediam_small (n : ℕ) [NeZero n] (hlo : 4 ≤ n) (hhi : n ≤ 6) :
    (graph n).ediam ≤ (n.choose 2 : ℕ∞) := by
  interval_cases n
  · exact Small4.sharp_ediam
  · exact Small5.sharp_ediam
  · exact Small6.sharp_ediam

end LRX

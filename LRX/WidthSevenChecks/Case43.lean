import LRX.WidthSevenCaseSplit
namespace LRX.FiniteCuts
set_option maxHeartbeats 0
set_option maxRecDepth 10000
/-- Complete pair-state check for one width7 dimension pair.
https://oeis.org/A186783 -/
theorem seven_arrow_43 : ∀ a : State 4,∀ b : State 3,SevenArrowGuard ⟨4,a⟩ ⟨3,b⟩ := by
  decide +kernel
/-- Complete empty-catalogue check for the same dimension pair.
https://oeis.org/A186783 -/
theorem seven_empty_43 : ∀ a : State 4,∀ b : State 3,SevenEmptyGuard ⟨4,a⟩ ⟨3,b⟩ := by
  decide +kernel
#print axioms seven_arrow_43
#print axioms seven_empty_43
end LRX.FiniteCuts

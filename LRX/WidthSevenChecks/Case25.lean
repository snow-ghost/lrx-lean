module

public import LRX.WidthSevenCaseSplit

@[expose] public section
namespace LRX.FiniteCuts
set_option maxHeartbeats 0
set_option maxRecDepth 10000
/-- Complete pair-state check for one width7 dimension pair.
https://oeis.org/A186783 -/
theorem seven_arrow_25 : ∀ a : State 2,∀ b : State 5,SevenArrowGuard ⟨2,a⟩ ⟨5,b⟩ := by
  decide +kernel
/-- Complete empty-catalogue check for the same dimension pair.
https://oeis.org/A186783 -/
theorem seven_empty_25 : ∀ a : State 2,∀ b : State 5,SevenEmptyGuard ⟨2,a⟩ ⟨5,b⟩ := by
  decide +kernel
#print axioms seven_arrow_25
#print axioms seven_empty_25
end LRX.FiniteCuts

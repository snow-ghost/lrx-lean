module

public import LRX.WidthSevenCaseSplit

@[expose] public section
namespace LRX.FiniteCuts
set_option maxHeartbeats 0
set_option maxRecDepth 10000
/-- Complete pair-state check for one width7 dimension pair.
https://oeis.org/A186783 -/
theorem seven_arrow_52 : ∀ a : State 5,∀ b : State 2,SevenArrowGuard ⟨5,a⟩ ⟨2,b⟩ := by
  decide +kernel
/-- Complete empty-catalogue check for the same dimension pair.
https://oeis.org/A186783 -/
theorem seven_empty_52 : ∀ a : State 5,∀ b : State 2,SevenEmptyGuard ⟨5,a⟩ ⟨2,b⟩ := by
  decide +kernel
#print axioms seven_arrow_52
#print axioms seven_empty_52
end LRX.FiniteCuts

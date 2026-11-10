module

public import LRX.WidthSevenCaseSplit

@[expose] public section
namespace LRX.FiniteCuts
set_option maxHeartbeats 0
set_option maxRecDepth 10000
/-- Complete pair-state check for one width7 dimension pair.
https://oeis.org/A186783 -/
theorem seven_arrow_34 : ∀ a : State 3,∀ b : State 4,SevenArrowGuard ⟨3,a⟩ ⟨4,b⟩ := by
  decide +kernel
/-- Complete empty-catalogue check for the same dimension pair.
https://oeis.org/A186783 -/
theorem seven_empty_34 : ∀ a : State 3,∀ b : State 4,SevenEmptyGuard ⟨3,a⟩ ⟨4,b⟩ := by
  decide +kernel
#print axioms seven_arrow_34
#print axioms seven_empty_34
end LRX.FiniteCuts

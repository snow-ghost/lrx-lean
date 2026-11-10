module

public import LRX.FiniteCutRegularity
public import Research.CayleyPy.FiniteGapService

@[expose] public section

/-! A cut profile constructed from a real finite permutation. The left/right
values are maxima of actual cut loads; this is a scalar envelope, not a claim
that one closed service attains all those discounts. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

def leftPeak (p : State b) (y : ℕ) : ℕ := (Finset.range (y+1)).sup (halfLoad p)

def rightPeak (p : State b) (x : ℕ) : ℕ := (Finset.Icc x b).sup (halfLoad p)

end LRX.FiniteCuts

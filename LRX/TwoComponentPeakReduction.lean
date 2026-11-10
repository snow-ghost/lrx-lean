module

public import LRX.ExteriorGapRecenter

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Every two-component cursor pair has a sharp original-target word or the
true peak geometry. Both internal and exterior gaps are paid. -/
theorem two_component_sharp_or_peak (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
      (start ≠ finish ∧ JoinedPositiveArcs p hc start finish) := by
  rcases two_component_sharp_or_peak_or_outer hn p hmaj hc root hlarge start finish with hw | hp | ho
  · exact Or.inl hw
  · exact Or.inr hp
  · exact Or.inl (two_component_exterior_sharp_word hn p hmaj hc root hlarge start finish ho)

#print axioms two_component_sharp_or_peak
end LRX.FiniteCuts

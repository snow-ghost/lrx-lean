module

public import LRX.UnitEnergyPeakTwoRigidity
public import LRX.OriginalZeroDefectShellPayment

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The budget-one unit-energy possibility is paid by the existing shell
word. The only remaining possibility has exactly four units of defect. -/
theorem unit_energy_peak_two_sharp_or_defect_four (hn : 10 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc)
    (hf : n-p.support.card=2) (he : canonicalEnergyDeficit p=1)
    (hU : sourceHalfPeak p=2) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (bridgeBudget (componentBridges p hc)=2 ∧ cycleDefect p=4 ∧ peakExcess p hc=1 ∧
      isolatedVertices p=p.supportᶜ) := by
  rcases two_component_unit_energy_peak_two_rigidity (by omega) p hmaj hmax hc hpos hf he hU with hzero | hfour
  · left
    exact original_zero_defect_shell_sharp_word_except_eight_nine (by omega) (by omega) (by omega)
      p hmaj hc root hlarge hzero.2.1 hU start finish
  · exact Or.inr hfour

#print axioms unit_energy_peak_two_sharp_or_defect_four
end LRX.FiniteCuts

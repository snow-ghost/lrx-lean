module

public import LRX.EnergyOnePayment

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- All energy regimes in the genuine large-component t>=2 branch are paid. -/
theorem many_component_final_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  by_cases hz : canonicalEnergyDeficit p=0
  · exact zero_energy_many_component_sharp_word hn p hmaj hmax hc hk root hlarge ht hz start finish
  by_cases hhigh : 2 ≤ canonicalEnergyDeficit p
  · exact high_energy_many_component_sharp_word hn p hmaj hmax hc hk root hlarge ht hhigh start finish
  have he0 : 0 ≤ canonicalEnergyDeficit p := by
    unfold canonicalEnergyDeficit
    have hh := majorized_canonical_energy p hmaj
    omega
  have he1 : canonicalEnergyDeficit p=1 := by omega
  rcases original_cut_sharp_or_two_arc hn p hmaj hc hk root hlarge ht start finish with h | h
  · exact h
  · apply joined_peak_word_of_nonpositive_excess (by omega) p hc hk start finish h.1 h.2
    by_contra hpos
    exact actual_energy_one_impossible (by omega) p hmaj hmax hc hk root hlarge ht (by omega) he1

#print axioms many_component_final_sharp_word
end LRX.FiniteCuts

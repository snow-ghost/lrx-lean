import LRX.OddZeroWidthFourCatalogue
import LRX.ZeroEnergyWidthFourPayment

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem zero_energy_width_four_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (he : canonicalEnergyDeficit p=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)

 (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  by_cases hp : n%2=0
  · exact zero_energy_even_width_four_sharp_word hn p hmaj hmax hc hk root hlarge ht he hp hv start finish
  · have hodd : n%2=1 := by omega
    rcases original_cut_sharp_or_two_arc hn p hmaj hc hk root hlarge ht start finish with h | h
    · exact h
    · apply joined_peak_word_of_nonpositive_excess (by omega) p hc hk start finish h.1 h.2
      by_contra hpos
      exact actual_odd_zero_width_four_impossible (by omega) p hmaj hmax hc hk root hlarge ht
        (by omega) he hodd hv

#print axioms zero_energy_width_four_sharp_word
end LRX.FiniteCuts

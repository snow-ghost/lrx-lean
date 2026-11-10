import LRX.PeakFourNoFillings
import LRX.ExceptionalSourcePeakRoute

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem zero_width_four_peak_four_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (hU : sourceHalfPeak p=4)
 (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  rcases original_cut_sharp_or_two_arc hn p hmaj hc hk root hlarge ht start finish with h | h
  · exact h
  · by_cases hpay : peakExcess p hc ≤ 0
    · exact joined_peak_word_of_nonpositive_excess (by omega) p hc hk start finish h.1 h.2 hpay
    · have hpos : 1 ≤ peakExcess p hc := by omega
      have hsize := actual_peak_four_sizes (by omega) p hmaj hmax hc hk root hlarge ht hpos he hp hv hU
      have hfill := actual_peak_four_no_fillings (by omega) p hmaj hmax hc hk root hlarge ht hpos he hp hv hU
      obtain ⟨hroots,_,_,hz,_,_,hcycles⟩ := peak_four_source_rigidity (by omega) p hmaj hmax hc hk root
        hlarge ht hpos he hp hv hU
      rw [hfill,Finset.card_empty,zero_add] at hcycles
      have hf := zero_energy_even_full_support p hmaj he hp
      exact exceptional_large_component_sharp_word hsize p hmaj (by omega) hf hcycles hz
        (by omega) root hlarge start finish

theorem zero_width_four_peak_at_least_four_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (hU : 4 ≤ sourceHalfPeak p)
 (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  by_cases hfour : sourceHalfPeak p=4
  · exact zero_width_four_peak_four_sharp_word hn p hmaj hmax hc hk root hlarge ht he hp hv hfour start finish
  · exact zero_width_four_high_peak_sharp_word hn p hmaj hmax hc hk root hlarge ht he hp hv
      (by omega) start finish

#print axioms zero_width_four_peak_four_sharp_word
#print axioms zero_width_four_peak_at_least_four_sharp_word
end LRX.FiniteCuts

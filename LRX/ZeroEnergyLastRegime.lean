module

public import LRX.ZeroEnergyTwoOddRegimes
public import LRX.OddFullWidthSevenExclusion

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem zero_energy_full_support_many_component_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (he : canonicalEnergyDeficit p=0) (hfix : n-p.support.card=0)
    (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  rcases zero_energy_sharp_or_two_odd_regimes hn p hmaj hmax hc hk root hlarge ht he start finish with h | h
  · exact h
  · obtain ⟨_,hp,_,hv⟩ := h
    rcases hv with ⟨_,hv⟩ | hv
    · exact zero_energy_odd_full_width_five_sharp_word hn p hmaj hmax hc hk root hlarge ht he hp hfix hv start finish
    · rcases original_cut_sharp_or_two_arc hn p hmaj hc hk root hlarge ht start finish with h | h
      · exact h
      · apply joined_peak_word_of_nonpositive_excess (by omega) p hc hk start finish h.1 h.2
        by_contra hpos
        exact actual_odd_full_width_seven_impossible (by omega) p hmaj hmax hc hk root hlarge ht
          (by omega) he hp hfix hv

/-- The only zero-deficit regime still needing payment has one fixed position. -/
theorem zero_energy_sharp_or_last_regime (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (he : canonicalEnergyDeficit p=0) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (n ≤ 73 ∧ n%2=1 ∧ n-p.support.card=1 ∧
      (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card).card=2 ∧
      (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card, C.card : ℕ)=7) := by
  rcases zero_energy_sharp_or_two_odd_regimes hn p hmaj hmax hc hk root hlarge ht he start finish with h | h
  · exact Or.inl h
  · obtain ⟨hn73,hp,ht2,hv⟩ := h
    rcases hv with ⟨hf,hv⟩ | hv
    · exact Or.inl (zero_energy_odd_full_width_five_sharp_word hn p hmaj hmax hc hk root hlarge ht
        he hp hf hv start finish)
    · by_cases hf : n-p.support.card=0
      · exact Or.inl (zero_energy_full_support_many_component_sharp_word hn p hmaj hmax hc hk root
          hlarge ht he hf start finish)
      · have hfixed := canonical_fixed_activity_square p hmaj
        change (((n-p.support.card : ℕ) : ℤ))^2 ≤ 4*canonicalEnergyDeficit p+(n%2 : ℕ) at hfixed
        rw [he,hp] at hfixed
        norm_num only [Nat.cast_one,mul_zero,zero_add] at hfixed
        have hfi : ((n-p.support.card : ℕ) : ℤ) ≤ 1 := by
          nlinarith [sq_nonneg (((n-p.support.card : ℕ) : ℤ)-1)]
        exact Or.inr ⟨hn73,hp,by omega,ht2,hv⟩

#print axioms zero_energy_full_support_many_component_sharp_word
#print axioms zero_energy_sharp_or_last_regime
end LRX.FiniteCuts

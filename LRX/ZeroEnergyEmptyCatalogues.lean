import LRX.OddZeroWidthFourCatalogue
import LRX.ZeroEnergyUnitCapacity

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators

/-- Dropping isolated vertices only relaxes the fixed-position budget. -/
theorem filtered_catalogue_drop_isolated (A B : SmallExteriorMap) (parity eps : ℤ)
    (fixed isolated width : ℕ)
    (h : (A,B) ∈ filteredExteriorCatalogue parity eps fixed isolated width) :
    (A,B) ∈ filteredExteriorCatalogue parity eps fixed 0 width := by
  obtain ⟨ha,hb,⟨hw,hf⟩,hc⟩ := (filtered_catalogue_mem_iff A B parity eps fixed isolated width).mp h
  exact (filtered_catalogue_mem_iff A B parity eps fixed 0 width).mpr
    ⟨ha,hb,⟨hw,by omega⟩,hc⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem even_zero_width_seven_empty : filteredExteriorCatalogue 0 0 0 0 7=[] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem even_zero_width_five_empty : filteredExteriorCatalogue 0 0 0 0 5=[] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem odd_zero_width_six_empty : ∀ f : Fin 2,
    filteredExteriorCatalogue 1 0 f.val 0 6=[] := by
  decide +kernel

variable {n k : ℕ} [NeZero n]

theorem actual_zero_empty_catalogue_impossible (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0)
    (hcase :
      (n%2=0 ∧ ((∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card, C.card : ℕ)=5 ∨
        (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
          (componentSet p root).card, C.card : ℕ)=7)) ∨
      (n%2=1 ∧ (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card, C.card : ℕ)=6)) : False := by
  obtain ⟨A,B,_,_,_,_,hmem⟩ :=
    actual_unpaid_filtered_exterior_pair hn p hmaj hmax hc hk root hlarge ht hpos
  have hm := filtered_catalogue_drop_isolated _ _ _ _ _ _ _ hmem
  rcases hcase with ⟨hp,hv⟩ | ⟨hp,hv⟩
  · have hfull := zero_energy_even_full_support p hmaj he hp
    have hf : n-p.support.card=0 := by omega
    rw [hp,he,hf] at hm
    norm_num only [Nat.cast_zero] at hm
    rcases hv with hv | hv
    · rw [hv,even_zero_width_five_empty] at hm
      simp only [List.not_mem_nil] at hm
    · rw [hv,even_zero_width_seven_empty] at hm
      simp only [List.not_mem_nil] at hm
  · have hfixed := canonical_fixed_activity_square p hmaj
    change (((n-p.support.card : ℕ) : ℤ))^2 ≤ 4*canonicalEnergyDeficit p+(n%2 : ℕ) at hfixed
    rw [he,hp] at hfixed
    norm_num only [Nat.cast_one,mul_zero,zero_add] at hfixed
    have hfi : ((n-p.support.card : ℕ) : ℤ) ≤ 1 := by
      nlinarith [sq_nonneg (((n-p.support.card : ℕ) : ℤ)-1)]
    have hf : n-p.support.card < 2 := by omega
    rw [hp,he,hv] at hm
    norm_num only [Nat.cast_one] at hm
    rw [odd_zero_width_six_empty ⟨n-p.support.card,hf⟩] at hm
    simp only [List.not_mem_nil] at hm

theorem zero_energy_empty_catalogue_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (he : canonicalEnergyDeficit p=0)
    (hcase :
      (n%2=0 ∧ ((∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card, C.card : ℕ)=5 ∨
        (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
          (componentSet p root).card, C.card : ℕ)=7)) ∨
      (n%2=1 ∧ (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card, C.card : ℕ)=6))
    (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  rcases original_cut_sharp_or_two_arc hn p hmaj hc hk root hlarge ht start finish with h | h
  · exact h
  · apply joined_peak_word_of_nonpositive_excess (by omega) p hc hk start finish h.1 h.2
    by_contra hpos
    exact actual_zero_empty_catalogue_impossible (by omega) p hmaj hmax hc hk root hlarge ht
      (by omega) he hcase

#print axioms filtered_catalogue_drop_isolated
#print axioms even_zero_width_five_empty
#print axioms even_zero_width_seven_empty
#print axioms odd_zero_width_six_empty
#print axioms actual_zero_empty_catalogue_impossible
#print axioms zero_energy_empty_catalogue_sharp_word
end LRX.FiniteCuts

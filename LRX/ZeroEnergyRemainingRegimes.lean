module

public import LRX.ZeroEnergyEmptyCatalogues
public import LRX.ZeroEnergyWidthFourAllParity
public import LRX.OddWidthFivePayment

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- The still-unpaid zero-deficit shapes; this is not a routing assertion. -/
def ZeroEnergyRemainingRegime (p : State n) (root : Fin n) : Prop :=
  let q := localTarget p 0 (componentLeft p root)
  let v := (∑ C ∈ nontrivialSuffixComponents q (componentSet p root).card, C.card : ℕ)
  (n%2=0 ∧ v=6) ∨ (n%2=1 ∧ ((n-p.support.card=0 ∧ v=5) ∨ v=7))

/-- Collect all verified zero-deficit payments in the original cursor problem. -/
theorem zero_energy_sharp_or_three_regimes (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (he : canonicalEnergyDeficit p=0) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (n ≤ 73 ∧
      (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card).card=2 ∧ ZeroEnergyRemainingRegime p root) := by
  rcases original_cut_sharp_or_two_arc hn p hmaj hc hk root hlarge ht start finish with h | h
  · exact Or.inl h
  by_cases hpos : 1 ≤ peakExcess p hc
  · have hb := original_unpaid_two_size_cutoff (by omega) p hmaj hmax hc hk root hlarge ht hpos
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let v := (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ)
    have hvlo : 4 ≤ v := by
      have hh := nontrivial_suffix_size_sum q L
      change 2*(nontrivialSuffixComponents q L).card ≤ v at hh
      change 2 ≤ (nontrivialSuffixComponents q L).card at ht
      omega
    have hvhi : v ≤ 7 := hb.2.2.2
    have hv : v=4 ∨ v=5 ∨ v=6 ∨ v=7 := by omega
    rcases hv with hv | hv | hv | hv
    · exact Or.inl (zero_energy_width_four_sharp_word hn p hmaj hmax hc hk root hlarge ht he hv start finish)
    · by_cases hp : n%2=0
      · exact Or.inl (zero_energy_empty_catalogue_sharp_word hn p hmaj hmax hc hk root hlarge ht he
          (Or.inl ⟨hp,Or.inl hv⟩) start finish)
      · have hp1 : n%2=1 := by omega
        by_cases hf : n-p.support.card=1
        · exact Or.inl (zero_energy_odd_one_fixed_width_five_sharp_word hn p hmaj hmax hc hk root
            hlarge ht he hp1 hf hv start finish)
        · have hfixed := canonical_fixed_activity_square p hmaj
          change (((n-p.support.card : ℕ) : ℤ))^2 ≤ 4*canonicalEnergyDeficit p+(n%2 : ℕ) at hfixed
          rw [he,hp1] at hfixed
          norm_num only [Nat.cast_one,mul_zero,zero_add] at hfixed
          have hfi : ((n-p.support.card : ℕ) : ℤ) ≤ 1 := by
            nlinarith [sq_nonneg (((n-p.support.card : ℕ) : ℤ)-1)]
          refine Or.inr ⟨hb.2.2.1,hb.1,?_⟩
          change (n%2=0 ∧ v=6) ∨ (n%2=1 ∧ ((n-p.support.card=0 ∧ v=5) ∨ v=7))
          exact Or.inr ⟨hp1,Or.inl ⟨by omega,hv⟩⟩
    · by_cases hp : n%2=0
      · refine Or.inr ⟨hb.2.2.1,hb.1,?_⟩
        exact Or.inl ⟨hp,hv⟩
      · exact Or.inl (zero_energy_empty_catalogue_sharp_word hn p hmaj hmax hc hk root hlarge ht he
          (Or.inr ⟨by omega,hv⟩) start finish)
    · by_cases hp : n%2=0
      · exact Or.inl (zero_energy_empty_catalogue_sharp_word hn p hmaj hmax hc hk root hlarge ht he
          (Or.inl ⟨hp,Or.inr hv⟩) start finish)
      · refine Or.inr ⟨hb.2.2.1,hb.1,?_⟩
        exact Or.inr ⟨by omega,Or.inr hv⟩
  · exact Or.inl (joined_peak_word_of_nonpositive_excess (by omega) p hc hk start finish h.1 h.2 (by omega))

#print axioms zero_energy_sharp_or_three_regimes
end LRX.FiniteCuts

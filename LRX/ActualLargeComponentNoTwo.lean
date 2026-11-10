import LRX.ExternalUnitPairsNoTwo
import LRX.ActualLargeComponentNoUnit

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords FiniteWindow
variable {n k : ℕ} [NeZero n]

/-- Actual exterior unit pairs exclude length-two arrows everywhere. -/
theorem actual_zero_width_four_no_two (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4) :
    let q := localTarget p 0 (componentLeft p root)
    ∀ i : Fin n, |displacement q.symm i| ≠ 2 := by
  have hf : n-p.support.card=0 := by
    have h := canonical_fixed_activity_square p hmaj
    change (((n-p.support.card : ℕ) : ℤ))^2 ≤ 4*canonicalEnergyDeficit p+(n%2 : ℕ) at h
    rw [he,hp] at h
    have hsquare : (((n-p.support.card : ℕ) : ℤ))^2=0 :=
      le_antisymm (by simpa using h) (sq_nonneg _)
    have hz : ((n-p.support.card : ℕ) : ℤ)=0 := sq_eq_zero_iff.mp hsquare
    omega
  obtain ⟨A,B,hlist,hma,hmb,hab,hA,hB⟩ :=
    actual_unpaid_external_unit_pairs hn p hmaj hmax hc hk root hlarge ht hpos hf hv
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  change suffixComponentFamily q L=[A,B] at hlist
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hqe : canonicalEnergyDeficit q=0 := by
    unfold canonicalEnergyDeficit
    dsimp only [q]
    rw [component_cut_displacement_mass]
    exact he
  change ∀ i : Fin n, |displacement q.symm i| ≠ 2
  intro i
  exact two_unit_windows_no_two A B q hqm hqe hp hma hmb hab hA hB i

theorem actual_zero_width_four_large_min_arrow (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4) :
    let q := localTarget p 0 (componentLeft p root)
    ∀ i : Fin n, i.val < (componentSet p root).card → 3 ≤ |displacement q.symm i| := by
  let q := localTarget p 0 (componentLeft p root)
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hqe : canonicalEnergyDeficit q=0 := by
    unfold canonicalEnergyDeficit
    dsimp only [q]
    rw [component_cut_displacement_mass]
    exact he
  have hf := zero_energy_even_full_support q hqm hqe hp
  have hfull : q.support=Finset.univ :=
    Finset.eq_univ_of_card q.support (by simpa only [Fintype.card_fin] using hf)
  have h1 := actual_zero_width_four_large_no_unit hn p hmaj hmax hc hk root hlarge ht hpos he hp hv
  have h2 := actual_zero_width_four_no_two hn p hmaj hmax hc hk root hlarge ht hpos he hp hv
  change ∀ i : Fin n, i.val < (componentSet p root).card → 3 ≤ |displacement q.symm i|
  intro i hi
  have hmove : q.symm i ≠ i := (mem_support_inverse q i).mp (by rw [hfull]; exact Finset.mem_univ _)
  have hne : displacement q.symm i ≠ 0 := by
    intro hz
    apply hmove
    apply Fin.ext
    unfold displacement at hz
    omega
  have hz : |displacement q.symm i| ≠ 0 := abs_ne_zero.mpr hne
  have hnon := abs_nonneg (displacement q.symm i)
  have hu := h1 i hi
  have ht2 := h2 i
  change |displacement q.symm i| ≠ 1 at hu
  change |displacement q.symm i| ≠ 2 at ht2
  omega

#print axioms actual_zero_width_four_no_two
#print axioms actual_zero_width_four_large_min_arrow
end LRX.FiniteCuts

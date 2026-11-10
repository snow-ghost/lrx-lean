import LRX.ExternalUnitPairsNoUnit

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords FiniteWindow
variable {n k : ℕ} [NeZero n]

/-- The actual even zero-deficit,width-four M4 remainder has no unit arrow
inside its large component. Full support and external unit pairs are derived. -/
theorem actual_zero_width_four_large_no_unit (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4) :
    let q := localTarget p 0 (componentLeft p root)
    ∀ i : Fin n, i.val < (componentSet p root).card → |displacement q.symm i| ≠ 1 := by
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
  have hLn : L ≤ n := by simpa only [L,Fintype.card_fin] using Finset.card_le_univ (componentSet p root)
  have hboundary := (suffix_component_family_spec q L hLn (component_recenter_cut p root).1).2.2
  have hAb : L ≤ A.window.offset := hboundary A (by rw [hlist]; simp)
  have hBb : L ≤ B.window.offset := hboundary B (by rw [hlist]; simp)
  change ∀ i : Fin n, i.val < L → |displacement q.symm i| ≠ 1
  intro i hi
  apply two_unit_windows_no_unit_outside A B q hqm hqe hp hma hmb hab hA hB i
  · intro h
    have hlow := h.1
    change i.val < L at hi
    omega
  · intro h
    have hlow := h.1
    change i.val < L at hi
    omega

#print axioms actual_zero_width_four_large_no_unit
end LRX.FiniteCuts

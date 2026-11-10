import LRX.OddWidthFiveWindowArrows

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords FiniteWindow
variable {n k : ℕ} [NeZero n]

/-- The catalogue and the original fixed count force long arrows throughout
 the genuine large component, including all of its internal fillings. -/
theorem actual_odd_zero_width_five_large_min_arrow (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=5) :
    let q := localTarget p 0 (componentLeft p root)
    ∀ i : Fin n, i.val < (componentSet p root).card → 3 ≤ |displacement q.symm i| := by
  obtain ⟨_,A,B,hlist,hma,hmb,_,hshape⟩ :=
    actual_unpaid_odd_width_five_pair hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv
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
  have hqf : n-q.support.card=1 := by
    have hsupport : q.support.card=p.support.card := by
      dsimp only [q]
      rw [local_target_zero]
      simpa only [inv_inv] using Equiv.Perm.card_support_conj
        (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
    rwa [hsupport]
  have hLn : L ≤ n := by
    simpa only [L,Fintype.card_fin] using Finset.card_le_univ (componentSet p root)
  have hboundary := (suffix_component_family_spec q L hLn (component_recenter_cut p root).1).2.2
  have hAb : L ≤ A.window.offset := hboundary A (by rw [hlist]; simp)
  have hBb : L ≤ B.window.offset := hboundary B (by rw [hlist]; simp)
  change ∀ i : Fin n, i.val < L → 3 ≤ |displacement q.symm i|
  intro i hi
  have hia : ¬Contains A.window i := by intro h; have hh := h.1; omega
  have hib : ¬Contains B.window i := by intro h; have hh := h.1; omega
  rcases hshape with ⟨hA,hB⟩ | ⟨hA,hB⟩
  · exact odd_unit_span_windows_min_arrow A B q hqm hqe hp hqf hma hmb hA hB i hia hib
  · exact odd_unit_span_windows_min_arrow B A q hqm hqe hp hqf hmb hma hB hA i hib hia

#print axioms actual_odd_zero_width_five_large_min_arrow
end LRX.FiniteCuts

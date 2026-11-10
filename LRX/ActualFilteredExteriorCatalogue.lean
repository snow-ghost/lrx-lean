import LRX.FilteredExteriorCatalogue

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords FiniteWindow
variable {n k : ℕ} [NeZero n]

/-- A genuine unpaid exterior pair survives the executable catalogue filter. -/
theorem actual_unpaid_filtered_exterior_pair (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    ∃ A B : FillingWindow n, suffixComponentFamily q L=[A,B] ∧
      A.Matches q.symm ∧ B.Matches q.symm ∧ A.Apart B ∧
      ((⟨A.size,A.filling⟩,⟨B.size,B.filling⟩) : SmallExteriorMap × SmallExteriorMap) ∈
        filteredExteriorCatalogue (n%2 : ℕ) (canonicalEnergyDeficit p)
          (n-p.support.card) (singletonSuffixComponents q L).card
          (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ) := by
  classical
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  obtain ⟨A,B,xp,xm,hlist,ha,hb,hsize,hma,hmb,hab,_,hsum,hxp,hxm,hsg⟩ :=
    actual_unpaid_exterior_pair_signs hn p hmaj hmax hc hk root hlarge ht hpos
  change suffixComponentFamily q L=[A,B] at hlist
  have hfix := component_cut_filling_fixed_partition p (by omega) root (by omega)
  change ((positiveSourceFamily q L).map (fun C => C.size-C.filling.support.card)).sum+
    ((suffixComponentFamily q L).map (fun C => C.size-C.filling.support.card)).sum+
      (singletonSuffixComponents q L).card=n-p.support.card at hfix
  rw [hlist] at hfix
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hfix
  refine ⟨A,B,hlist,hma,hmb,hab,?_⟩
  apply (filtered_catalogue_mem_iff _ _ _ _ _ _ _).mpr
  refine ⟨local_map_mem_catalogue A.size A.filling ha.1 ha.2,
    local_map_mem_catalogue B.size B.filling hb.1 hb.2,⟨hsize,?_⟩,?_⟩
  · change (A.size-A.filling.support.card)+(B.size-B.filling.support.card)+
      (singletonSuffixComponents q L).card ≤ n-p.support.card
    omega
  · apply (compatible_sign_offsets_iff _ _ _ _ _).mpr
    exact ⟨xp,xm,hsum,hxp,hxm,hsg⟩

#print axioms actual_unpaid_filtered_exterior_pair
end LRX.FiniteCuts

import LRX.OddZeroWidthFourCatalogue

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators

def spanTwoExteriorMap : SmallExteriorMap := ⟨3,Equiv.swap (0 : Fin 3) 2⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem odd_one_fixed_width_five_check :
    (filteredExteriorCatalogue 1 0 1 0 5).all (fun z => decide
      ((z.1=unitExteriorMap ∧ z.2=spanTwoExteriorMap) ∨
       (z.1=spanTwoExteriorMap ∧ z.2=unitExteriorMap)))=true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem odd_one_isolated_width_five_empty : filteredExteriorCatalogue 1 0 1 1 5=[] := by
  decide +kernel

theorem odd_one_fixed_width_five_shape (A B : SmallExteriorMap) (isolated : ℕ)
    (h : (A,B) ∈ filteredExteriorCatalogue 1 0 1 isolated 5) :
    isolated=0 ∧ ((A=unitExteriorMap ∧ B=spanTwoExteriorMap) ∨
      (A=spanTwoExteriorMap ∧ B=unitExteriorMap)) := by
  have hinfo := (filtered_catalogue_mem_iff A B 1 0 1 isolated 5).mp h
  have ha : isolated ≤ 1 := by have hh := hinfo.2.2.1.2; omega
  have hz : isolated=0 := by
    by_contra hh
    have he : isolated=1 := by omega
    rw [he,odd_one_isolated_width_five_empty] at h
    simp only [List.not_mem_nil] at h
  refine ⟨hz,?_⟩
  rw [hz] at h
  have hh := List.all_eq_true.mp odd_one_fixed_width_five_check (A,B) h
  exact of_decide_eq_true hh

theorem actual_unpaid_odd_width_five_pair {n k : ℕ} [NeZero n]
    (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1)
    (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=5) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    (singletonSuffixComponents q L).card=0 ∧
    ∃ A B : FillingWindow n, suffixComponentFamily q L=[A,B] ∧
      A.Matches q.symm ∧ B.Matches q.symm ∧ A.Apart B ∧
      (((⟨A.size,A.filling⟩ : SmallExteriorMap)=unitExteriorMap ∧
        (⟨B.size,B.filling⟩ : SmallExteriorMap)=spanTwoExteriorMap) ∨
       ((⟨A.size,A.filling⟩ : SmallExteriorMap)=spanTwoExteriorMap ∧
        (⟨B.size,B.filling⟩ : SmallExteriorMap)=unitExteriorMap)) := by
  obtain ⟨A,B,hlist,hma,hmb,hab,hmem⟩ :=
    actual_unpaid_filtered_exterior_pair hn p hmaj hmax hc hk root hlarge ht hpos
  rw [hp,he,hf,hv] at hmem
  norm_num only [Nat.cast_one] at hmem
  obtain ⟨ha,hshape⟩ := odd_one_fixed_width_five_shape _ _ _ hmem
  exact ⟨ha,A,B,hlist,hma,hmb,hab,hshape⟩

#print axioms actual_unpaid_odd_width_five_pair

#print axioms odd_one_fixed_width_five_check
#print axioms odd_one_isolated_width_five_empty
#print axioms odd_one_fixed_width_five_shape
end LRX.FiniteCuts

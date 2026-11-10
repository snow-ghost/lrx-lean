import LRX.FixedCorrectedDensity

/-! M4: exact local fixed-position bookkeeping for the actual area family.
Internal and external fillings are kept distinct. -/
namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ}

/-- For matching disjoint windows, local fixed counts sum to exactly the
selected fixed positions of the original permutation. -/
theorem window_family_fixed_count (As : List (FillingWindow n)) (p : State n)
    (hm : ∀ A ∈ As, A.Matches p) (hd : As.Pairwise FillingWindow.Apart) :
    (familyPositions As \ p.support).card=
      (As.map (fun A => A.size-A.filling.support.card)).sum := by
  classical
  induction As with
  | nil => simp [familyPositions]
  | cons A As ih =>
    obtain ⟨hA,hAs⟩ := List.pairwise_cons.mp hd
    have hmA := hm A (List.mem_cons_self ..)
    have hmAs := fun B hB => hm B (List.mem_cons_of_mem _ hB)
    have hrest := ih hmAs hAs
    have hdis : Disjoint (windowPositions A.window) (familyPositions As) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      obtain ⟨B,hB,hBi⟩ := (mem_family_positions As i).mp hj
      exact hA B hB i (Finset.mem_filter.mp hi).2 hBi
    have hdisFixed : Disjoint (windowPositions A.window \ p.support) (familyPositions As \ p.support) :=
      hdis.mono Finset.sdiff_subset Finset.sdiff_subset
    simp only [familyPositions,Finset.union_sdiff_distrib,
      Finset.card_union_of_disjoint hdisFixed,matching_window_fixed_count A.window p A.filling hmA,
      hrest,List.map_cons,List.sum_cons]

end LRX.FiniteWindow

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

/-- Exact partition f = f_internal + f_external + a, on real local fillings. -/
theorem prefix_external_filling_fixed_partition (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    ((positiveSourceFamily p (componentSet p 0).card).map (fun A => A.size-A.filling.support.card)).sum+
      ((suffixComponentFamily p (componentSet p 0).card).map (fun A => A.size-A.filling.support.card)).sum+
      (singletonSuffixComponents p (componentSet p 0).card).card=n-p.support.card := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card := by
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  obtain ⟨hm,ha⟩ := area_window_family_spec p (componentSet p 0).card hproper.le hcut
  have hlocal := window_family_fixed_count _ p.symm hm ha
  have hpart := area_selected_fixed_partition p hc hproper
  rw [hlocal] at hpart
  simpa only [areaWindowFamily,List.map_append,List.sum_append] using hpart

#print axioms window_family_fixed_count
#print axioms prefix_external_filling_fixed_partition
end LRX.FiniteCuts

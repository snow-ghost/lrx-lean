import LRX.FillingFamilyResource
import LRX.SourceGapReversalFamily
import LRX.FiniteWindowSupport
import LRX.FiniteRootRoute
import LRX.ShallowShellWindowFamily

/-! M4: inject actual window cycles into the original filling cycles.
Only a lower bound on the ambient peak is needed for the resource budget. -/
namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n b : ℕ}

theorem peak_le_embedded_peak (W : Window n b) (p : State b) :
    leftPeak p b ≤ leftPeak (permutation W p) n := by
  apply Finset.sup_le
  intro e he
  rw [← half_load_window W p e]
  apply Finset.le_sup
  apply Finset.mem_range.mpr
  have := Finset.mem_range.mp he
  have := W.fits
  omega

theorem disjoint_embedded (W : Window n b) (p q : State b) (hd : p.Disjoint q) :
    (permutation W p).Disjoint (permutation W q) := by
  intro i
  by_cases hi : Contains W i
  · obtain ⟨j,rfl⟩ := (contains_iff W i).mp hi
    rcases hd j with h | h
    · left; rw [permutation_embed,h]
    · right; rw [permutation_embed,h]
  · exact Or.inl (permutation_outside W p i hi)

noncomputable def FillingWindow.embeddedCycles (A : FillingWindow n) : List (State n) :=
  (factorList A.filling).map (permutation A.window)

noncomputable def windowFamilyCycles (As : List (FillingWindow n)) : List (State n) :=
  As.flatMap FillingWindow.embeddedCycles

theorem embedded_cycles_is_cycle (A : FillingWindow n) (q : State n)
    (hq : q ∈ A.embeddedCycles) : q.IsCycle := by
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
  exact permutation_is_cycle A.window c ((factor_list_spec A.filling).1 c hc)

theorem embedded_cycles_support_inside (A : FillingWindow n) (q : State n)
    (hq : q ∈ A.embeddedCycles) (i : Fin n) (hi : i ∈ q.support) : Contains A.window i := by
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hq
  by_contra hh
  exact (Equiv.Perm.mem_support.mp hi) (permutation_outside A.window c i hh)

theorem window_family_cycles_pairwise (As : List (FillingWindow n))
    (hd : As.Pairwise FillingWindow.Apart) : (windowFamilyCycles As).Pairwise Equiv.Perm.Disjoint := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro A _
    apply List.pairwise_map.mpr
    exact (factor_list_spec A.filling).2.1.imp (fun h => disjoint_embedded A.window _ _ h)
  · apply hd.imp
    intro A B hAB q hq r hr
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact hAB i (embedded_cycles_support_inside A q hq i hi)
      (embedded_cycles_support_inside B r hr i hj)

theorem window_family_cycles_nodup (As : List (FillingWindow n))
    (hd : As.Pairwise FillingWindow.Apart) : (windowFamilyCycles As).Nodup := by
  apply Equiv.Perm.nodup_of_pairwise_disjoint ?_ (window_family_cycles_pairwise As hd)
  intro h
  obtain ⟨A,_,hA⟩ := List.mem_flatMap.mp h
  exact Equiv.Perm.not_isCycle_one (embedded_cycles_is_cycle A 1 hA)

theorem window_cycle_peak_sum_le (A : FillingWindow n) :
    (cyclePeakSum A.filling : ℤ) ≤
      (A.embeddedCycles.map (fun q => (leftPeak q n : ℤ))).sum := by
  have aux (qs : List (State A.size)) :
      (qs.map (fun q => (leftPeak q A.size : ℤ))).sum ≤
      (qs.map (fun q => (leftPeak (permutation A.window q) n : ℤ))).sum := by
    induction qs with
    | nil => simp
    | cons q qs ih =>
      simp only [List.map_cons,List.sum_cons]
      exact add_le_add (by exact_mod_cast peak_le_embedded_peak A.window q) ih
  have hsum : (cyclePeakSum A.filling : ℤ)=
      ((factorList A.filling).map (fun q => (leftPeak q A.size : ℤ))).sum := by
    simpa only [cyclePeakSum,Nat.cast_sum,factorList,Finset.toList_toFinset] using
      List.sum_toFinset (fun q : State A.size => (leftPeak q A.size : ℤ))
        (Finset.nodup_toList A.filling.cycleFactorsFinset)
  rw [hsum]
  simpa only [FillingWindow.embeddedCycles,List.map_map,Function.comp_def] using
    aux (factorList A.filling)

theorem window_family_peak_sum_le (As : List (FillingWindow n)) :
    (As.map (fun A => (cyclePeakSum A.filling : ℤ))).sum ≤
      ((windowFamilyCycles As).map (fun q => (leftPeak q n : ℤ))).sum := by
  induction As with
  | nil => simp [windowFamilyCycles]
  | cons A As ih =>
    have h := window_cycle_peak_sum_le A
    simpa only [windowFamilyCycles,List.flatMap_cons,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons] using add_le_add h ih

variable [NeZero n]

omit [NeZero n] in
theorem matched_window_cycle_mem_fillings (p : State n) (A : FillingWindow n)
    (hm : A.Matches p.symm)
    (ha : ∀ i ∈ sourcePackets p, ¬Contains A.window i)
    (q : State n) (hq : q ∈ A.embeddedCycles) : q ∈ fillingCycles p := by
  classical
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
  have hcf : c ∈ A.filling.cycleFactorsFinset := Finset.mem_toList.mp hc
  obtain ⟨hcy,hact⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcf
  apply Finset.mem_filter.mpr
  constructor
  · apply Equiv.Perm.mem_cycleFactorsFinset_iff.mpr
    refine ⟨permutation_is_cycle A.window c hcy,?_⟩
    intro i hi
    rw [permutation_support] at hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    rw [permutation_embed,hact j hj]
    exact (hm j).symm
  · apply Finset.disjoint_left.mpr
    intro i hi hs
    have hout := ha i hs
    exact (Equiv.Perm.mem_support.mp hi) (permutation_outside A.window c i hout)

/-- Distinct actual window cycles contribute no more peak than all original fillings. -/
theorem window_family_peak_le_fillings (p : State n) (As : List (FillingWindow n))
    (hm : ∀ A ∈ As, A.Matches p.symm) (hd : As.Pairwise FillingWindow.Apart)
    (ha : ∀ A ∈ As, ∀ i ∈ sourcePackets p, ¬Contains A.window i) :
    (As.map (fun A => (cyclePeakSum A.filling : ℤ))).sum ≤ fillingHalfPeakSum p := by
  classical
  let qs := windowFamilyCycles As
  have hnd : qs.Nodup := window_family_cycles_nodup As hd
  have hsub : qs.toFinset ⊆ fillingCycles p := by
    intro q hq
    obtain ⟨A,hA,hqA⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hq)
    exact matched_window_cycle_mem_fillings p A (hm A hA) (ha A hA) q hqA
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun q : State n => (leftPeak q n : ℤ)) (fun _ _ _ => by positivity)
  rw [List.sum_toFinset _ hnd] at hs
  have he : fillingHalfPeakSum p=∑ q ∈ fillingCycles p, (leftPeak q n : ℤ) := by
    symm
    simpa only [Finset.toList_toFinset,fillingHalfPeakSum] using
      List.sum_toFinset (fun q : State n => (leftPeak q n : ℤ)) (Finset.nodup_toList (fillingCycles p))
  rw [← he] at hs
  exact (window_family_peak_sum_le As).trans hs

end LRX.FiniteWindow

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

/-- Peak resource of the actual positive internal windows is charged to the
original map's own filling cycles, with no counting or peak certificate supplied. -/
theorem positive_filling_peak_sum_le (p : State n) (L : ℕ) :
    ((positiveSourceFamily p L).map (fun A => (cyclePeakSum A.filling : ℤ))).sum ≤
      fillingHalfPeakSum p := by
  have hs := positive_source_family_spec p L
  exact window_family_peak_le_fillings p _ hs.1 hs.2.1
    (fun A hA i hi => positive_family_avoids_source p L A hA i hi)

#print axioms positive_filling_peak_sum_le
end LRX.FiniteCuts

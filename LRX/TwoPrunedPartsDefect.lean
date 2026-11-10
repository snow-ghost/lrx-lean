import LRX.PacketComponentDefectBound

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

theorem disjoint_pruned_union_product (p : State n) (S T : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hT : ∀ i, p i ∈ T ↔ i ∈ T)
    (hdis : Disjoint S T) :
    PrunedLift.permutation p S hS*PrunedLift.permutation p T hT=
      PrunedLift.permutation p (S ∪ T) (by intro i; simp only [Finset.mem_union,hS,hT]) := by
  classical
  apply Equiv.ext
  intro i
  by_cases hiS : i ∈ S
  · have hiT : i ∉ T := fun hh => Finset.disjoint_left.mp hdis hiS hh
    simp [Equiv.Perm.mul_apply,PrunedLift.permutation_apply,hiS,hiT]
  · by_cases hiT : i ∈ T
    · simp [Equiv.Perm.mul_apply,PrunedLift.permutation_apply,hiS,hiT,hS]
    · simp [Equiv.Perm.mul_apply,PrunedLift.permutation_apply,hiS,hiT]

theorem two_pruned_parts_defect_le_component (p : State n) (S T C : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hT : ∀ i, p i ∈ T ↔ i ∈ T)
    (hC : ∀ i, p i ∈ C ↔ i ∈ C) (hdis : Disjoint S T) (hSC : S ⊆ C) (hTC : T ⊆ C) :
    cycleDefect (PrunedLift.permutation p S hS)+cycleDefect (PrunedLift.permutation p T hT) ≤
      cycleDefect (PrunedLift.permutation p C hC) := by
  classical
  have hd : (PrunedLift.permutation p S hS).Disjoint (PrunedLift.permutation p T hT) := by
    intro i
    by_cases hiS : i ∈ S
    · right
      have hiT : i ∉ T := fun hh => Finset.disjoint_left.mp hdis hiS hh
      simp [PrunedLift.permutation_apply,hiT]
    · left
      simp [PrunedLift.permutation_apply,hiS]
  have hu : ∀ i, p i ∈ S ∪ T ↔ i ∈ S ∪ T := by intro i; simp only [Finset.mem_union,hS,hT]
  have hsum := cycle_defect_disjoint_superadditive _ _ hd
  rw [disjoint_pruned_union_product p S T hS hT hdis] at hsum
  have hupper := cycle_defect_nested_pruned_le p (S ∪ T) C hu hC (Finset.union_subset hSC hTC)
  exact hsum.trans hupper

theorem matched_window_positions_invariant (p : State n) (A : FillingWindow n)
    (hm : A.Matches p.symm) : ∀ i, p i ∈ windowPositions A.window ↔ i ∈ windowPositions A.window := by
  apply invariant_of_inverse_closed
  intro i hi
  have hic : Contains A.window i := by simpa only [windowPositions,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  obtain ⟨j,rfl⟩ := (contains_iff A.window i).mp hic
  rw [hm j]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,contains_embed A.window _⟩

theorem matched_window_pruned_inverse (p : State n) (A : FillingWindow n)
    (hm : A.Matches p.symm) :
    (PrunedLift.permutation p (windowPositions A.window)
      (matched_window_positions_invariant p A hm)).symm=permutation A.window A.filling := by
  classical
  let q := PrunedLift.permutation p (windowPositions A.window) (matched_window_positions_invariant p A hm)
  have hq : q.symm=permutation A.window A.filling := by
    apply Equiv.ext
    intro i
    by_cases hi : Contains A.window i
    · obtain ⟨j,rfl⟩ := (contains_iff A.window i).mp hi
      have hiW : embed A.window j ∈ windowPositions A.window :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,contains_embed A.window j⟩
      simp only [q,PrunedLift.permutation_symm_apply,if_pos hiW,permutation_embed]
      exact hm j
    · have hiW : i ∉ windowPositions A.window := by simpa only [windowPositions,Finset.mem_filter,Finset.mem_univ,true_and] using hi
      simp only [q,PrunedLift.permutation_symm_apply,if_neg hiW,permutation_outside A.window A.filling i hi]
  exact hq

theorem matched_window_pruned_defect (p : State n) (A : FillingWindow n)
    (hm : A.Matches p.symm) :
    cycleDefect (PrunedLift.permutation p (windowPositions A.window)
      (matched_window_positions_invariant p A hm))=cycleDefect A.filling := by
  classical
  let q := PrunedLift.permutation p (windowPositions A.window) (matched_window_positions_invariant p A hm)
  have hq : q.symm=permutation A.window A.filling := by
    apply Equiv.ext
    intro i
    by_cases hi : Contains A.window i
    · obtain ⟨j,rfl⟩ := (contains_iff A.window i).mp hi
      have hiW : embed A.window j ∈ windowPositions A.window :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,contains_embed A.window j⟩
      simp only [q,PrunedLift.permutation_symm_apply,if_pos hiW,permutation_embed]
      exact hm j
    · have hiW : i ∉ windowPositions A.window := by simpa only [windowPositions,Finset.mem_filter,Finset.mem_univ,true_and] using hi
      simp only [q,PrunedLift.permutation_symm_apply,if_neg hiW,permutation_outside A.window A.filling i hi]
  change cycleDefect q=cycleDefect A.filling
  rw [← cycle_defect_inverse q,hq,cycle_defect_embedded_window]

#print axioms two_pruned_parts_defect_le_component
#print axioms matched_window_pruned_defect
end LRX.FiniteCuts

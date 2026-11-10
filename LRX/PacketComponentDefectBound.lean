import LRX.UnitEnergyExactComponentDefects
import LRX.CycleDefectMonotonicity
import LRX.ExtractedPacketDefect

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem cycle_defect_pruned_le (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) :
    cycleDefect (PrunedLift.permutation p S hS) ≤ cycleDefect p := by
  let q := PrunedLift.permutation p S hS
  let r := PrunedLift.permutation p Sᶜ (PrunedLift.complement_invariant p S hS)
  have hh := cycle_defect_disjoint_superadditive q r (PrunedLift.permutation_disjoint p S hS)
  have hp := PrunedLift.permutation_partition p S hS
  change q*r=p at hp
  rw [hp] at hh
  have hr := finite_depth_rank r
  have hnon : 0 ≤ cycleDefect r := by unfold cycleDefect; omega
  change cycleDefect q ≤ cycleDefect p
  omega

theorem cycle_defect_nested_pruned_le (p : State n) (S T : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hT : ∀ i, p i ∈ T ↔ i ∈ T) (hST : S ⊆ T) :
    cycleDefect (PrunedLift.permutation p S hS) ≤ cycleDefect (PrunedLift.permutation p T hT) := by
  classical
  let q := PrunedLift.permutation p T hT
  have hSq : ∀ i, q i ∈ S ↔ i ∈ S := by
    intro i
    by_cases hi : i ∈ T
    · simp only [q,PrunedLift.permutation_apply,if_pos hi,hS]
    · simp only [q,PrunedLift.permutation_apply,if_neg hi]
  have heq : PrunedLift.permutation q S hSq=PrunedLift.permutation p S hS := by
    apply Equiv.ext
    intro i
    by_cases hi : i ∈ S
    · simp [PrunedLift.permutation_apply,q,hi,hST hi]
    · simp [PrunedLift.permutation_apply,hi]
  rw [← heq]
  exact cycle_defect_pruned_le q S hSq

theorem cycle_defect_embedded_window (A : FillingWindow n) :
    cycleDefect (permutation A.window A.filling)=cycleDefect A.filling := by
  simp only [cycleDefect,displacement_mass,inversion_number_window,permutation_support_card,permutation_cycle_count]

theorem packet_defect_le_matched_component (p : State n) (root : Fin n) (A : FillingWindow n)
    (hwhere : ∀ i, Contains A.window i ↔ i ∈ componentSet p root)
    (hmatch : A.Matches p.symm) :
    cycleDefect (canonicalRootPacket p root) ≤ cycleDefect A.filling := by
  classical
  let S := PrunedLift.core p (displacement p.symm) root
  let T := componentSet p root
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hS := PrunedLift.core_invariant p (displacement p.symm) root
  have hT : ∀ i, p i ∈ T ↔ i ∈ T := CycleFootprint.component_invariant hd root
  have hST : S ⊆ T := by
    intro i hi
    have hh := (PrunedLift.mem_core p (displacement p.symm) root i).mp hi
    exact (CycleFootprint.mem_component _ _ _).mpr (CycleFootprint.service_path_load_path hd hh.1)
  let q := PrunedLift.permutation p T hT
  have hq : q.symm=permutation A.window A.filling := by
    apply Equiv.ext
    intro i
    by_cases hi : Contains A.window i
    · obtain ⟨j,rfl⟩ := (contains_iff A.window i).mp hi
      have hiT : embed A.window j ∈ T := (hwhere _).mp (contains_embed A.window j)
      simp only [q,PrunedLift.permutation_symm_apply,if_pos hiT,permutation_embed]
      exact hmatch j
    · have hiT : i ∉ T := fun hh => hi ((hwhere i).mpr hh)
      simp only [q,PrunedLift.permutation_symm_apply,if_neg hiT,permutation_outside A.window A.filling i hi]
  have hqZ : cycleDefect q=cycleDefect A.filling := by
    rw [← cycle_defect_inverse q,hq,cycle_defect_embedded_window]
  have hup := cycle_defect_nested_pruned_le p S T hS hT hST
  change cycleDefect (canonicalRootPacket p root) ≤ cycleDefect q at hup
  rw [hqZ] at hup
  exact hup

theorem packet_strong_cycle_defect_bound (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (root : Fin n) (hr : root ∈ p.support) :
    2*(((canonicalRootPacket p root).cycleFactorsFinset.card : ℤ)-1) ≤
      cycleDefect (canonicalRootPacket p root) := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hlow := extracted_packet_strong_defect p (FiniteWindow.majorized_short hd hmaj) root hr
  change 2*(((canonicalRootPacket p root).cycleFactorsFinset.card : ℤ)-1) ≤ _ at hlow
  have hI : LiftedModel.inversionCount (fun i : Fin n => ((canonicalRootPacket p root).symm i : ℤ))=
      inversionNumber (canonicalRootPacket p root).symm := canonical_inversion_count _
  have hInv : inversionNumber (canonicalRootPacket p root).symm=inversionNumber (canonicalRootPacket p root) := inversion_number_inverse _
  rw [hI,hInv] at hlow
  have hform : (∑ i, |displacement (canonicalRootPacket p root).symm i|)-
      (inversionNumber (canonicalRootPacket p root) : ℤ)-
      ((canonicalRootPacket p root).support.card : ℤ)+
      ((canonicalRootPacket p root).cycleFactorsFinset.card : ℤ)=cycleDefect (canonicalRootPacket p root) := by
    simp only [cycleDefect,displacement_mass_inverse]
  rw [hform] at hlow
  exact hlow

theorem packet_cycle_count_le_two_of_component_defect_two (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (root : Fin n)
    (hr : root ∈ p.support) (A : FillingWindow n)
    (hwhere : ∀ i, Contains A.window i ↔ i ∈ componentSet p root)
    (hmatch : A.Matches p.symm) (hZ : cycleDefect A.filling=2) :
    (canonicalRootPacket p root).cycleFactorsFinset.card ≤ 2 := by
  have hup := packet_defect_le_matched_component p root A hwhere hmatch
  rw [hZ] at hup
  have hlow := packet_strong_cycle_defect_bound p hmaj root hr
  omega

theorem exact_defect_two_windows_packet_cycles_le_two (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hgeom : ExactDefectTwoComponentWindows p) :
    ∀ root ∈ componentRoots p, (canonicalRootPacket p root).cycleFactorsFinset.card ≤ 2 := by
  classical
  obtain ⟨a,b,A,B,_,hroots,_,_,hAw,hBw,_,hAm,hBm,_,hAZ,hBZ⟩ := hgeom
  intro root hr
  have hmove : root ∈ p.support := (Finset.mem_filter.mp hr).1
  have hcases : root=a ∨ root=b := by rw [hroots] at hr; simpa using hr
  rcases hcases with rfl | rfl
  · exact packet_cycle_count_le_two_of_component_defect_two p hmaj _ hmove A hAw hAm hAZ
  · exact packet_cycle_count_le_two_of_component_defect_two p hmaj _ hmove B hBw hBm hBZ

#print axioms packet_cycle_count_le_two_of_component_defect_two
#print axioms exact_defect_two_windows_packet_cycles_le_two
end LRX.FiniteCuts

import LRX.ZeroEnergyPeakRigidity
import LRX.CycleDefectMonotonicity
import LRX.ExtractedPacketDefect

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- A genuine canonical root packet of a zero-defect majorized map is one
shallow cycle. Neither cyclicity nor packet defect is supplied as a premise. -/
theorem canonical_root_packet_shallow_of_zero_defect (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (root : Fin n)
    (hroot : root ∈ p.support) (hz : cycleDefect p=0) :
    (canonicalRootPacket p root).IsCycle ∧ Shallow (canonicalRootPacket p root) := by
  classical
  let S := PrunedLift.core p (displacement p.symm) root
  let hS := PrunedLift.core_invariant p (displacement p.symm) root
  let q := canonicalRootPacket p root
  have hqz : cycleDefect q=0 := zero_defect_pruned_factor p S hS hz
  have hrS : root ∈ S := (PrunedLift.mem_core p (displacement p.symm) root root).mpr
    ⟨Relation.ReflTransGen.refl,Relation.ReflTransGen.refl⟩
  have hqroot : q root=p root := by
    change PrunedLift.permutation p S hS root=p root
    simp only [PrunedLift.permutation_apply,if_pos hrS]
  have hqne : q ≠ 1 := by
    intro hh
    have hmove := Equiv.Perm.mem_support.mp hroot
    apply hmove
    rw [← hqroot,hh]
    rfl
  have hkpos := Equiv.Perm.card_cycleType_pos.mpr hqne
  simp only [Equiv.Perm.cycleType,Multiset.card_map,Finset.card_val] at hkpos
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hstrong := extracted_packet_strong_defect p (FiniteWindow.majorized_short hd hmaj) root hroot
  change 2*((q.cycleFactorsFinset.card : ℤ)-1) ≤
    (∑ i, |displacement q.symm i|)-
      (LiftedModel.inversionCount (fun i : Fin n => (q.symm i : ℤ)) : ℤ)-
      (q.support.card : ℤ)+(q.cycleFactorsFinset.card : ℤ) at hstrong
  rw [canonical_inversion_count,displacement_mass_inverse] at hstrong
  have hI : inversionNumber q.symm=inversionNumber q := inversion_number_inverse q
  rw [hI] at hstrong
  change 2*((q.cycleFactorsFinset.card : ℤ)-1) ≤ cycleDefect q at hstrong
  have hk : q.cycleFactorsFinset.card=1 := by omega
  have hcycle : q.IsCycle := Equiv.Perm.card_cycleType_eq_one.mp (by
    simpa only [Equiv.Perm.cycleType,Multiset.card_map,Finset.card_val] using hk)
  refine ⟨hcycle,(shallow_iff_direct q).mpr ?_⟩
  unfold cycleDefect at hqz
  rw [hk] at hqz
  norm_num only [Nat.cast_one] at hqz
  omega

#print axioms canonical_root_packet_shallow_of_zero_defect
end LRX.FiniteCuts

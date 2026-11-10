import LRX.PacketExteriorReduction
import LRX.ActiveSetSlack

namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem zero_displacement_fixed {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (i : Fin n) (hi : d i=0) : i ∉ p.support := by
  have h := AffineLift.lift_residue hd i
  have hf : p⁻¹ i=i := by simpa only [Equiv.Perm.inv_def,hi,Int.cast_zero,add_zero] using h.symm
  have hm : i ∉ (p⁻¹).support := Equiv.Perm.notMem_support.mpr hf
  simpa only [Equiv.Perm.support_inv] using hm

theorem fixed_gap_size_le {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (a : Fin n)
    (hz : ∀ i ∈ positions (PrunedLift.core p d 0) a, d i=0) :
    size (PrunedLift.core p d 0) a ≤ fixedCount p := by
  have hsub : positions (PrunedLift.core p d 0) a ⊆ p.supportᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (zero_displacement_fixed hd i (hz i hi))
  have hc := Finset.card_le_card hsub
  simpa only [positions_card,Finset.card_compl,Finset.card_univ,Fintype.card_fin,fixedCount] using hc

theorem noninternal_gap_size_le_fixed {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ PrunedLift.core p d 0) (hnot : ¬Internal p d a) :
    size (PrunedLift.core p d 0) a ≤ fixedCount p := by
  apply fixed_gap_size_le hd a
  intro i hi
  by_contra hdi
  exact hnot (nonzero_gap_internal hd hcover hroot a ha i hi hdi)

theorem moving_core_card_ge_two {p : State n} {d : Fin n → ℤ}
    (hroot : p⁻¹ 0 ≠ 0) : 2 ≤ (PrunedLift.core p d 0).card := by
  classical
  have hpartner : p.symm 0 ∈ PrunedLift.core p d 0 := (PrunedLift.mem_core p d 0 _).mpr
    (PrunedLift.in_core_same_cycle p d 0 ⟨Relation.ReflTransGen.refl,Relation.ReflTransGen.refl⟩
      (Equiv.Perm.SameCycle.refl _ _).apply_right)
  have hsub : {0,p.symm 0} ⊆ PrunedLift.core p d 0 := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact core_zero p d
    · have he := Finset.mem_singleton.mp hi
      simpa only [he] using hpartner
  have hc := Finset.card_le_card hsub
  have hne : (0 : Fin n) ≠ p.symm 0 := Ne.symm hroot
  simpa [hne] using hc

#print axioms fixed_gap_size_le
#print axioms moving_core_card_ge_two
end LRX.FiniteGaps

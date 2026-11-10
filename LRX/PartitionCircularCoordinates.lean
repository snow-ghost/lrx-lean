import LRX.CircularArcCoordinates
import LRX.ConsecutivePacketGap

/-! The final linear gap ends at n; its circular right endpoint is zero. -/
namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem cut_interval_endpoint (a : Fin n) (t : ℕ) (hat : a.val ≤ t) (hlt : t-a.val<n) :
    ((t : Fin n)-a).val=t-a.val := by
  have he : (t : Fin n)-a=((t-a.val : ℕ) : Fin n) := by
    rw [Nat.cast_sub hat]
    simp
  rw [he]
  exact Nat.mod_eq_of_lt hlt

theorem cut_interval_membership (a i : Fin n) (t : ℕ) (hat : a.val < t) (ht : t ≤ n) :
    (i-a).val < t-a.val ↔ a.val ≤ i.val ∧ i.val < t := by
  by_cases hai : a.val ≤ i.val
  · rw [Fin.sub_val_of_le hai]
    omega
  · have hia : i.val < a.val := by omega
    rw [Fin.coe_sub_iff_lt.mpr hia]
    omega

theorem cut_interval_open (a i : Fin n) (t : ℕ) (hat : a.val < t) (ht : t ≤ n) :
    (0 < (i-a).val ∧ (i-a).val < t-a.val) ↔ a.val < i.val ∧ i.val < t := by
  by_cases hai : a.val ≤ i.val
  · rw [Fin.sub_val_of_le hai]
    omega
  · have hia : i.val < a.val := by omega
    rw [Fin.coe_sub_iff_lt.mpr hia]
    omega

theorem next_circular_width {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (hroot : d 0 ≠ 0) (a : Fin n) :
    next (PrunedLift.core p d 0) a-a.val<n := by
  by_cases ha : a=0
  · subst a
    have hmov : p⁻¹ 0 ≠ 0 := fun h => hroot (BufferProgram.fixed_short_displacement hd 0 (hshort 0) h)
    have hpartner : p.symm 0 ∈ PrunedLift.core p d 0 := (PrunedLift.mem_core p d 0 _).mpr
      (PrunedLift.in_core_same_cycle p d 0 ⟨Relation.ReflTransGen.refl,Relation.ReflTransGen.refl⟩
        (Equiv.Perm.SameCycle.refl _ _).apply_right)
    have hpos : 0 < (p.symm 0).val := by
      have hne : (p.symm 0).val ≠ 0 := fun h => hmov (Fin.ext h)
      omega
    have hnext := next_le_member (PrunedLift.core p d 0) 0 (p.symm 0) hpartner (by simpa using hpos)
    have hlt := (p.symm 0).isLt
    simp only [Fin.val_zero,Nat.sub_zero]
    omega
  · have hpos : 0 < a.val := by
      have hne : a.val ≠ 0 := fun h => ha (Fin.ext h)
      omega
    have hnext := next_le (PrunedLift.core p d 0) a
    omega

theorem next_circular_mem (S : Finset (Fin n)) (hzero : (0 : Fin n) ∈ S) (a : Fin n) :
    (next S a : Fin n) ∈ S := by
  by_cases hn : next S a=n
  · simpa [hn] using hzero
  · obtain ⟨i,hi,he⟩ := next_is_member S a (by have := next_le S a; omega)
    have hcast : (next S a : Fin n)=i := by rw [← he]; simp
    simpa [hcast] using hi

#print axioms cut_interval_membership
#print axioms next_circular_width
#print axioms next_circular_mem
end LRX.FiniteGaps

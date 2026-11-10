import LRX.AffineLift

/-! Turn the finite balanced lift into a genuine periodic bijection of integers.
This supplies the object on which affine crossings and routing are defined. -/
namespace LRX.AffineLift
open scoped Fin.IntCast Fin.NatCast

variable {n : ℕ} [NeZero n]

theorem modulus_pos : (0 : ℤ) < n := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

theorem residue_val (z : ℤ) : ((Fin.intCast z : Fin n) : ℤ) = z % (n : ℤ) := by
  change ((z : Fin n).val : ℤ) = _
  rw [Fin.val_intCast]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt modulus_pos))

omit [NeZero n] in
theorem fin_mod (i : Fin n) : (i : ℤ) % n = (i : ℤ) :=
  Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)

theorem modEq_residue (z : ℤ) :
    Int.ModEq (n : ℤ) z ((Fin.intCast z : Fin n) : ℤ) := by
  rw [residue_val]
  simp [Int.ModEq]

theorem normalize_phase {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) : IsLift p ((Fin.intCast c : Fin n) : ℤ) d := by
  refine ⟨hd.1, ?_⟩
  intro i
  exact (hd.2 i).trans ((modEq_residue c).add_left (p.symm i : ℤ))

theorem exists_cyclic_lift (p : State n) :
    ∃ c : Fin n, ∃ d : Fin n → ℤ, IsLift p (c : ℤ) d ∧ Majorized d := by
  obtain ⟨c, d, hd, hm⟩ := exists_majorized (Nat.pos_of_ne_zero (NeZero.ne n)) p
  exact ⟨Fin.intCast c, d, normalize_phase hd, hm⟩

#print axioms exists_cyclic_lift
end LRX.AffineLift

import LRX.WordReflection

/-! Reflection transports balanced phase lifts and preserves their affine price. -/
namespace LRX.WordReflection
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

@[simp] theorem reflection_inv : (reflection : State n)⁻¹=reflection := rfl

def reflectedTarget (p : State n) : State n := reflection*p*reflection

def reflectedDisplacement (d : Fin n → ℤ) (i : Fin n) : ℤ := -d (reflection i)

theorem reflected_target_inverse (p : State n) (i : Fin n) :
    (reflectedTarget p).symm i=reflection (p.symm (reflection i)) := by
  change (reflectedTarget p)⁻¹ i= _
  simp only [reflectedTarget, mul_inv_rev, reflection_inv, Equiv.Perm.mul_apply]
  rfl

theorem reflected_lift {p : State n} {d : Fin n → ℤ} (c : Fin n)
    (hd : AffineLift.IsLift p (c : ℤ) d) :
    AffineLift.IsLift (reflectedTarget p) ((-c : Fin n) : ℤ) (reflectedDisplacement d) := by
  constructor
  · unfold reflectedDisplacement
    rw [Finset.sum_neg_distrib, Equiv.sum_comp reflection d, hd.1, neg_zero]
  · intro i
    apply (LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_add, Int.cast_natCast, Fin.cast_val_eq_self,
      reflected_target_inverse, reflectedDisplacement, Int.cast_neg, reflection_apply]
    have h := AffineLift.lift_residue hd (reflection i)
    simp only [Int.cast_natCast, Fin.cast_val_eq_self, reflection_apply] at h
    linear_combination -h

theorem reflected_mass (d : Fin n → ℤ) :
    (∑ i : Fin n, |reflectedDisplacement d i|)=∑ i : Fin n, |d i| := by
  simp only [reflectedDisplacement, abs_neg]
  exact Equiv.sum_comp reflection (fun i => |d i|)

#print axioms reflected_lift
end LRX.WordReflection

module

public import LRX.ReflectedPortLoad

@[expose] public section

/-! Reflected closed services are genuine route tasks at the opposite ports,
with identical letter counts and no extra coordinate-change cost. -/
namespace LRX.WordReflection
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem rotation_reflection (r : Fin n) :
    reflection*rotation r*reflection=rotation (-r) := by
  apply Equiv.ext
  intro i
  simp only [Equiv.Perm.mul_apply, RotationWords.rotation, AffineLift.rotation_power_apply,
    Fin.cast_val_eq_self, reflection_apply]
  ring

omit [NeZero n] in
theorem mirror_increment (w : List Letter) :
    ((mirror w).map LiftedModel.increment).sum=-(w.map LiftedModel.increment).sum := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a <;> simp_all [mirror, Letter.inverse, LiftedModel.increment] <;> omega

@[simp] theorem reflected_target_twice (p : State n) :
    reflectedTarget (reflectedTarget p)=p := by
  simp only [reflectedTarget, mul_assoc, ← mul_assoc (reflection : State n) reflection,
    reflection_square, one_mul, mul_one]

def mirrorService (s : ClosedService n) : ClosedService n where
  port := -s.port
  word := mirror s.word
  target := reflectedTarget s.target
  correct := by
    rw [mirror_eval, s.correct, ← rotation_reflection]
    simp only [reflectedTarget, mul_inv_rev, reflection_inv, mul_assoc,
      ← mul_assoc (reflection : State n) reflection, reflection_square, one_mul]
  closed := by rw [mirror_increment, s.closed, neg_zero]

#print axioms mirror_increment
end LRX.WordReflection

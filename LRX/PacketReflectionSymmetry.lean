import LRX.PacketCoordinateSymmetry

namespace LRX.PrunedLift
variable {n : ℕ} [NeZero n]

theorem in_core_reroot {p : State n} {d : Fin n → ℤ} {r s i : Fin n}
    (hs : InCore p d r s) : InCore p d s i ↔ InCore p d r i := by
  constructor
  · intro h
    exact ⟨hs.1.trans h.1,h.2.trans hs.2⟩
  · intro h
    exact ⟨hs.2.trans h.1,h.2.trans hs.1⟩
end LRX.PrunedLift

namespace LRX.WordReflection
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem reaches_unreflected (p : State n) (d : Fin n → ℤ) {a b : Fin n}
    (h : PrunedLift.Reaches (reflectedTarget p) (reflectedDisplacement d) a b) :
    PrunedLift.Reaches p d (reflection a) (reflection b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail i j hp he ih =>
    exact ih.tail ((service_edge_reflected p d (reflection i) (reflection j)).mp (by simpa using he))

theorem core_reflected (p : State n) (d : Fin n → ℤ) (r i : Fin n) :
    PrunedLift.InCore (reflectedTarget p) (reflectedDisplacement d) (reflection r) (reflection i) ↔
      PrunedLift.InCore p d r i := by
  constructor
  · intro h
    exact ⟨by simpa using reaches_unreflected p d h.1,by simpa using reaches_unreflected p d h.2⟩
  · intro h
    exact ⟨reaches_reflected p d h.1,reaches_reflected p d h.2⟩

theorem mirror_word_target (p : State n) (start finish : Fin n) :
    reflection*((rotation (-start))⁻¹*reflectedTarget p*rotation (-finish))*reflection=
      (rotation start)⁻¹*p*rotation finish := by
  rw [← rotation_reflection,← rotation_reflection]
  simp only [reflectedTarget,mul_inv_rev,reflection_inv]
  simp only [mul_assoc,← mul_assoc (reflection : State n) reflection,reflection_square,one_mul,mul_one]

#print axioms core_reflected
#print axioms mirror_word_target
end LRX.WordReflection

import LRX.ReflectedClosedService

/-! Reachability for a single nontrivial cycle is derived from cycle structure.
Both incident-port services are consequently available without a routing premise. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem cycle_root_reaches {p : State n} {d : Fin n → ℤ}
    (hp : p.IsCycle) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n) (hroot : d r ≠ 0) :
    ∀ i : Fin n, localDisplacement d r i ≠ 0 →
      Relation.ReflTransGen (BufferProgram.ServiceEdge (localTarget p 0 r)
        (localDisplacement d r)) 0 i := by
  have hd0 : AffineLift.IsLift p ((0 : Fin n) : ℤ) d := by simpa using hd
  have hlift := recentered_lift 0 r hd0
  have hc : (localTarget p 0 r).IsCycle := by
    rw [local_target_zero]
    simpa only [inv_inv] using hp.conj (g := (rotation r)⁻¹)
  have hm (i : Fin n) (hi : localDisplacement d r i ≠ 0) :
      (localTarget p 0 r)⁻¹ i ≠ i := by
    intro hf
    exact hi (BufferProgram.fixed_short_displacement hlift i (hshort _) hf)
  have hz : (localTarget p 0 r)⁻¹ 0 ≠ 0 := by
    apply hm
    simpa only [local_displacement_zero] using hroot
  intro i hi
  exact Relation.ReflTransGen.single (Or.inl (hc.inv.sameCycle hz (hm i hi)))

#print axioms cycle_root_reaches
end LRX.RotationWords

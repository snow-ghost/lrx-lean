import LRX.InvariantCutRecenter
import LRX.FiniteSupportPeakBounds

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

/-- A cycle containing both physical endpoints crosses every internal cut. -/
theorem enclosing_cycle_port_load_ge_two (C : State n) (hC : C.IsCycle)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (r : Fin n) (hr : r.val+1 < n) : 2 ≤ portLoad (displacement C) r := by
  have hpos : 0 < halfLoad C (r.val+1) := by
    by_contra h
    have hz : halfLoad C (r.val+1)=0 := by omega
    have hcut := (half_load_zero_iff_invariant_cut C (r.val+1)).mp hz
    let z : Fin n := ⟨n-1,by omega⟩
    have hsame : C.SameCycle 0 z := hC.sameCycle
      (Equiv.Perm.mem_support.mp hzero) (Equiv.Perm.mem_support.mp hlast)
    obtain ⟨k,hk⟩ := hsame.exists_nat_pow_eq
    have hpow : ∀ k : ℕ, ((C^k) 0).val < r.val+1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ',Equiv.Perm.mul_apply]
        exact (hcut _).mpr ih
    have hh := hpow k
    rw [hk] at hh
    dsimp only [z] at hh
    omega
  rw [port_load_eq_twice_half]
  omega

#print axioms enclosing_cycle_port_load_ge_two
end LRX.FiniteCuts

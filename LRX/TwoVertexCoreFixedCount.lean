import LRX.FixedGapCardinality

/-! A two-vertex packet with at most two fixed vertices is impossible for
n >= 7: both partition gaps would be strictly shorter than half the circle. -/
namespace LRX.FiniteGaps
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem two_vertex_core_fixed_count (hn : 7 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d)
    (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (hcard : (PrunedLift.core p d 0).card=2) : 3 ≤ fixedCount p := by
  classical
  by_contra hsmall
  have hf : fixedCount p ≤ 2 := by omega
  let S := PrunedLift.core p d 0
  have hgap : ∀ a ∈ S, 2*(size S a+1)<n := by
    intro a ha
    by_cases hi : Internal p d a
    · exact internal_size_bound hd hm a hi
    · have hb := noninternal_gap_size_le_fixed hd hcover hroot a ha hi
      change size S a ≤ fixedCount p at hb
      omega
  have hne : S.Nonempty := ⟨0,core_zero p d⟩
  have hsum : (∑ a ∈ S, 2*(size S a+1)) < S.card*n := by
    calc
      _ < ∑ a ∈ S, n := Finset.sum_lt_sum_of_nonempty hne hgap
      _ = _ := by simp
  rw [← Finset.mul_sum,Finset.sum_add_distrib,sum_gap_sizes S (core_zero p d)] at hsum
  change S.card=2 at hcard
  simp only [Finset.sum_const,smul_eq_mul,mul_one,hcard] at hsum
  omega

#print axioms two_vertex_core_fixed_count
end LRX.FiniteGaps

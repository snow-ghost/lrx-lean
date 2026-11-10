module

public import LRX.PacketGapWidth
public import LRX.FiniteCoordinateCapacity

@[expose] public section

/-! Finite coordinates on the complement of a packet gap retain every
physical distance. A shortest lifted arrow is no longer than its finite representative. -/
namespace LRX.PrunedLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem shortest_representative {N a b : ℤ} (hN : 0 < N) (hshort : 2*|a| < N)
    (hm : Int.ModEq N a b) : |a| ≤ |b| := by
  by_contra h
  have hdiff : |a-b| < N := by have := abs_sub a b; omega
  have hmod : Int.ModEq N (a-b) 0 := by simpa using hm.sub_right b
  have hz : a-b=0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.modEq_zero_iff_dvd.mp hmod)
    have hh : ((a-b).natAbs : ℤ) < (N.natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs,abs_of_pos hN] using hdiff
    exact_mod_cast hh
  have hab : a=b := by omega
  exact h (by rw [hab])

end LRX.PrunedLift

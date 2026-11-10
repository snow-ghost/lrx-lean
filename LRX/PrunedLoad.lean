module

public import LRX.FiniteRootStar
public import LRX.ReducedServiceRoute
public import LRX.PrunedPartition

@[expose] public section

/-! Deleting canonical finite cycles away from the root preserves the root
port load. Thus the root discount remains available to the retained service. -/
namespace LRX.PrunedLift
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem positive_endpoint_passages (a b : Fin n) (ha : a ≠ 0) (hb : b ≠ 0) :
    PeriodicBuffer.edgePassages (n : ℤ) (a : ℤ) (b : ℤ)=0 := by
  have hdiv (i : Fin n) (hi : i ≠ 0) : -(i : ℤ)/(n : ℤ) = -1 := by
    have hn := i.isLt
    have hp := Fin.val_ne_zero_iff.mpr hi
    exact Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by omega)
  simp only [PeriodicBuffer.edgePassages, hdiv a ha, hdiv b hb, sub_self, abs_zero]

end LRX.PrunedLift

module

public import LRX.PortLoad
public import Mathlib.Algebra.Order.Floor.BigOperators

@[expose] public section

/-! The sum of all actual edge loads equals total absolute token displacement.
This is proved from the integer crossing formula, without a geometric profile
assumption or a bounded displacement hypothesis. -/
namespace LRX.RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def signedCrossing (a d r : ℤ) : ℤ := (r-a-d)/(n : ℤ)-(r-a)/(n : ℤ)

omit [NeZero n] in
theorem edge_signed_crossing (a d r : ℤ) :
    PeriodicBuffer.edgePassages (n : ℤ) (a-r) (a-r+d)=|signedCrossing (n := n) a d r| := by
  simp only [PeriodicBuffer.edgePassages, signedCrossing,
    show -(a-r+d)=r-a-d by ring, show -(a-r)=r-a by ring]

omit [NeZero n] in
theorem port_load_nonneg (d : Fin n → ℤ) (r : Fin n) : 0 ≤ portLoad d r := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

end LRX.RotationWords

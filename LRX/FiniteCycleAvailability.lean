module

public import LRX.FinitePeakPorts
public import LRX.SingleCycleServices

@[expose] public section

/-! A single finite cycle has actual closed services attaining the left/right
peak discounts in their allowed regions. No reachability premise is required. -/
namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {b : ℕ} [NeZero b]

omit [NeZero b] in
theorem displacement_short (p : State b) (i : Fin b) : |displacement p i| < (b : ℤ) := by
  have hi := i.isLt
  have hp := (p i).isLt
  rw [abs_lt]
  unfold displacement
  omega

omit [NeZero b] in
theorem displacement_ne_of_moved (p : State b) (i : Fin b) (hi : p i ≠ i) : displacement p i ≠ 0 := by
  intro h
  apply hi
  apply Fin.ext
  unfold displacement at h
  omega

omit [NeZero b] in
theorem displacement_endpoint (p : State b) :
    (fun i : Fin b => (i : ℤ)+displacement p i)=(fun i => (p i : ℤ)) := by
  funext i
  simp [displacement]

end LRX.FiniteCuts

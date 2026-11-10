module

public import LRX.SharpDiameterAll

@[expose] public section

/-!
# Exact diameter of the LRX Cayley graph

Entry point of the publication package.  The Cayley graph of `Equiv.Perm (Fin n)`
with generators `L = finRotate n`, `R = L⁻¹`, `X = Equiv.swap 0 1`
has diameter `n * (n - 1) / 2` for every `n ≥ 4` (OEIS A186783).
-/

namespace LRXDiameter

/-- Main theorem. -/
theorem exact_diameter (n : ℕ) [NeZero n] (hn : 4 ≤ n) :
    (LRX.graph n).diam = n * (n - 1) / 2 :=
  LRX.exact_diameter_all n hn

/-- The upper bound for all `n ≥ 4`. -/
theorem upper : LRX.SharpDiameterTheorem := LRX.sharp_diameter_all

end LRXDiameter

import LRX.NinePeakPayment
import LRX.ExactDiameter

namespace LRX

/-- Unconditional routing for every nonzero majorized lift at n>=4. -/
theorem nonzero_lift_routing : NonzeroLiftRouting :=
  nonzero_routing_of_nine nine_zero_energy_peak_routing

/-- The sharp upper bound for every size n>=4, with no routing premise. -/
theorem sharp_diameter_all : SharpDiameterTheorem :=
  sharp_upper_of_nonzero_routing nonzero_lift_routing

/-- Resolves the diameter formula in OEIS A186783 for every n >= 4.
https://oeis.org/A186783
This theorem states the diameter; uniqueness of its antipode is a separate claim. -/
theorem exact_diameter_all (n : ℕ) [NeZero n] (hn : 4 ≤ n) :
    (graph n).diam=n*(n-1)/2 :=
  exact_diameter_of_upper sharp_diameter_all n hn

#print axioms nonzero_lift_routing
#print axioms sharp_diameter_all
#print axioms exact_diameter_all
end LRX

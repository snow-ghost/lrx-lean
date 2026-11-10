import Mathlib.Algebra.Ring.Fin
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-!
Phase51: arithmetic for paying every invariant finite packet gap.
The quadratic load lemma, finite depth inequality and strict-band
inversion capacity are mathematical premises, not formalized here.
The completion is used only to certify an inversion budget; the route
still serves the original fillers in the original integer lift.
-/
namespace CayleyPy.GapInversionBudget

theorem triangular_inversion_deficit (b Delta I K B : ℤ)
    (hquad : 2*Delta+K^2 ≤ b^2)
    (hdepth : 2*I ≤ 2*Delta-b+K)
    (hB : 2*B=b*(b-1)) :
    K*(K-1) ≤ 2*(B-I) := by nlinarith

theorem integer_linear_deficit (K d : ℤ) (hd : 0 ≤ d)
    (htri : K*(K-1) ≤ 2*d) : K ≤ d+1 := by
  by_cases hK : K ≤ 1
  · omega
  · have hp := mul_nonneg (show 0 ≤ K-1 by omega)
      (show 0 ≤ K-2 by omega)
    nlinarith

#print axioms triangular_inversion_deficit
#print axioms integer_linear_deficit

end CayleyPy.GapInversionBudget

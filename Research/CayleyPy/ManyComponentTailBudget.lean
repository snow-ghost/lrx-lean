module

public import Mathlib.Algebra.Ring.Fin
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic

@[expose] public section

/-! Phase60: general finite component bridges and short-tail certificates.
The component and permutation geometry is proved in the accompanying note. -/
namespace CayleyPy.ManyComponentTailBudget

theorem tail_pays_fixed_positions (r p x f b epsilon : ℤ)
    (hr : 2 ≤ r) (hp : 0 ≤ p) (hx : 0 ≤ x) (hf : f ≤ 2*x+p)
    (he : (x+r)*(x+r+p)-2*b ≤ epsilon) : 2*f+r*r-2*b ≤ epsilon := by
  have hxx := sq_nonneg x
  have hpx := mul_nonneg hp hx
  have hrx := mul_nonneg (show 0 ≤ 2*r-4 by omega) hx
  have hrp := mul_nonneg (show 0 ≤ r-2 by omega) hp
  nlinarith

theorem external_cross_minimum (t v a fixedPairs M : ℤ)
    (ht : 2 ≤ t) (hv : 2*t ≤ v) (ha : 0 ≤ a) (hfixed : 0 ≤ fixedPairs)
    (hM : 2*(t-1)*(v-t)+a*v+fixedPairs ≤ M) : 2*(a+t) ≤ M := by
  have htv := mul_nonneg (show 0 ≤ t-1 by omega) (show 0 ≤ v-2*t by omega)
  have htt := mul_nonneg (show 0 ≤ t by omega) (show 0 ≤ t-2 by omega)
  have hav := mul_nonneg ha (show 0 ≤ v-2 by omega)
  nlinarith

#print axioms tail_pays_fixed_positions
#print axioms external_cross_minimum

end CayleyPy.ManyComponentTailBudget

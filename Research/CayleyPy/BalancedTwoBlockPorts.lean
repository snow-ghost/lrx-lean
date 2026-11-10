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

namespace BalancedTwoBlockPorts

def lee (n x y : ℤ) : ℤ := min |x-y| (n-|x-y|)

theorem even_antipodes (H x y : ℤ) (hH : 1 ≤ H)
    (hx : 0 ≤ x) (hxn : x < 2*H) (hy : 0 ≤ y) (hyH : y < H) :
    lee (2*H) x y + lee (2*H) x (y+H) = H := by
  unfold lee
  simp only [abs_eq_max_neg]
  omega

theorem odd_one_two (H x y : ℤ) (hH : 1 ≤ H)
    (hx : 0 ≤ x) (hxn : x < 2*H+1) (hy : 0 ≤ y) (hyH : y < H) :
    lee (2*H+1) x y +
      min (lee (2*H+1) x (y+H)) (lee (2*H+1) x (y+H+1)) = H := by
  unfold lee
  simp only [abs_eq_max_neg]
  omega

theorem odd_two_one (H x y : ℤ) (hH : 1 ≤ H)
    (hx : 0 ≤ x) (hxn : x < 2*H+1) (hy : 0 ≤ y) (hyH : y < H) :
    min (lee (2*H+1) x y) (lee (2*H+1) x (y+1)) +
      lee (2*H+1) x (y+H+1) = H := by
  unfold lee
  simp only [abs_eq_max_neg]
  omega

end BalancedTwoBlockPorts

#print axioms BalancedTwoBlockPorts.even_antipodes
#print axioms BalancedTwoBlockPorts.odd_one_two
#print axioms BalancedTwoBlockPorts.odd_two_one

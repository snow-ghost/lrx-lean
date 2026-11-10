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

set_option linter.style.header false

/-!
Kernel-checked arithmetic for the phase34 root-gap argument.

The passage from permutations and global Lorenz bounds to the displayed
integer hypotheses is NOT formalized here. In particular, these theorems
do not assert an unconditional Cayley-graph diameter bound.
-/

namespace CayleyPy.RootGapArithmetic

/-- A half-size bound on every gap bounds the sum of their squared sizes. -/
theorem nondominant_square_sum {ι : Type*} (T : Finset ι) (g : ι → ℤ)
    (s : ℤ) (hs : 0 ≤ s)
    (hgap : ∀ i ∈ T, 0 ≤ g i ∧ 2 * g i ≤ s)
    (hsum : ∑ i ∈ T, g i ≤ s) :
    2 * (∑ i ∈ T, (g i) ^ 2) ≤ s ^ 2 := by
  calc
    2 * (∑ i ∈ T, (g i) ^ 2) = ∑ i ∈ T, 2 * (g i) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ T, s * g i := by
      apply Finset.sum_le_sum
      intro i hi
      have h := hgap i hi
      nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]
    _ = s * ∑ i ∈ T, g i := by rw [Finset.mul_sum]
    _ ≤ s * s := mul_le_mul_of_nonneg_left hsum hs
    _ = s ^ 2 := by ring

end CayleyPy.RootGapArithmetic

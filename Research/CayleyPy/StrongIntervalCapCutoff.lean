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

/-! Phase75: exact finite-profile square capacity with a stronger interval cap.
The existence and lengths of the original invariant intervals are geometric
inputs. No assertion about all permutations is an axiom of this file. -/
namespace CayleyPy.StrongIntervalCapCutoff

theorem lower_mass_square {ι : Type*} [DecidableEq ι]
    (S A : Finset ι) (x : ι → ℤ) (b : ℤ)
    (hsub : A ⊆ S) (hb : 0 ≤ b)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hA : ∀ i ∈ A, b ≤ x i) :
    ∑ i ∈ S, (x i)^2 ≤
      ((∑ i ∈ S, x i)-b*((A.card : ℤ)-1))^2+b^2*((A.card : ℤ)-1) := by
  let y : ι → ℤ := fun i => x i-if i ∈ A then b else 0
  have hy : ∀ i ∈ S, 0 ≤ y i := by
    intro i hi
    by_cases h : i ∈ A
    · simp only [y, h, ↓reduceIte]
      exact sub_nonneg.mpr (hA i h)
    · simpa only [y, h, ↓reduceIte, sub_zero] using hx i hi
  have hf : S.filter (fun i => i ∈ A)=A := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h,h⟩⟩
  have hind (c : ℤ) : (∑ i ∈ S, if i ∈ A then c else 0)=(A.card : ℤ)*c := by
    rw [← Finset.sum_filter, hf]
    simp
  have hsum : (∑ i ∈ S, y i)=(∑ i ∈ S, x i)-(A.card : ℤ)*b := by
    simp only [y, Finset.sum_sub_distrib, hind]
  have hpoint : ∀ i ∈ S,
      (x i)^2 ≤ (y i)^2+2*b*y i+(if i ∈ A then b^2 else 0) := by
    intro i hi
    by_cases h : i ∈ A
    · simp only [y, h, ↓reduceIte]
      nlinarith
    · simp only [y, h, ↓reduceIte, sub_zero, add_zero]
      nlinarith [mul_nonneg hb (hx i hi)]
  have htotal := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hind] at htotal
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg hy
  rw [hsum] at hsq htotal
  nlinarith

theorem exact_cap_envelope (V M x w C S2 : ℤ)
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hw : 0 ≤ w) (hC : 0 ≤ C)
    (hcap : x ≤ M) (hVcap : V ≤ 2*M)
    (hsmall : S2 ≤ x*V) (hrest : S2 ≤ x*x+(V-x-w)^2+C) :
    S2 ≤ M*M+(V-M-w)^2+C := by
  by_cases hx : x ≤ V-M-w
  · have h1 := mul_nonneg hV (show 0 ≤ V-M-w-x by omega)
    have h2 := mul_nonneg (show 0 ≤ M+w by omega) (show 0 ≤ 2*M-V by omega)
    nlinarith [sq_nonneg w]
  · have hprod := mul_nonneg (show 0 ≤ M-x by omega)
      (show 0 ≤ x-(V-M-w) by omega)
    nlinarith

#print axioms lower_mass_square
#print axioms exact_cap_envelope

end CayleyPy.StrongIntervalCapCutoff

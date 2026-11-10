import LRX.FiniteRankSorting
import LRX.FiniteAdjacentInversions
import Mathlib.Data.Fin.Tuple.Sort

namespace LRX.FiniteRankOrder
open FiniteCuts
variable {n : ℕ}

theorem exists_adjacent_descent_of_ne_one (q : State n) (hne : q ≠ 1) :
    ∃ a b : Fin n, b.val=a.val+1 ∧ (q b).val < (q a).val := by
  classical
  cases n with
  | zero =>
    apply False.elim
    apply hne
    ext i
    exact Fin.elim0 i
  | succ n =>
    by_contra h
    have hm : Monotone q := Fin.monotone_iff_le_succ.mpr (by
      intro i
      change (q i.castSucc).val ≤ (q i.succ).val
      by_contra hh
      exact h ⟨i.castSucc,i.succ,rfl,by omega⟩)
    exact hne ((Equiv.Perm.monotone_iff q).mp hm)

/-- Finite rank order never increases the inversion count of the lower
map. Each descending adjacent comparator lowers the upper count by one
and lowers the lower count by either zero or one. -/
theorem below_inversion_mono (p q : State n) (hpq : Below p q) :
    inversionNumber p ≤ inversionNumber q := by
  classical
  have main : ∀ k : ℕ, ∀ q p : State n, inversionNumber q=k → Below p q →
      inversionNumber p ≤ inversionNumber q := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro q p hk hp
      by_cases hq : q=1
      · subst q
        rw [eq_one_of_below_one p hp]
      · obtain ⟨a,b,hab,hdesc⟩ := exists_adjacent_descent_of_ne_one q hq
        have hqprice := adjacent_swap_inversion_price q a b hab hdesc
        have hnext := below_compare p q hp a b hab
        have hqcompare : compareAt q a b=q*Equiv.swap a b := by
          simp only [compareAt,ite_eq_right (not_le.mpr hdesc)]
        rw [hqcompare] at hnext
        have hrec := ih (inversionNumber (q*Equiv.swap a b)) (by omega)
          (q*Equiv.swap a b) (compareAt p a b) rfl hnext
        by_cases horder : (p a).val ≤ (p b).val
        · simp only [compareAt,ite_eq_left horder] at hrec
          omega
        · have hpprice := adjacent_swap_inversion_price p a b hab (by omega)
          simp only [compareAt,ite_eq_right horder] at hrec
          omega
  exact main (inversionNumber q) q p rfl hpq

#print axioms below_inversion_mono
end LRX.FiniteRankOrder

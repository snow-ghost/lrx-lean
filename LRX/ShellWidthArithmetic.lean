module

public import LRX.ShellPriceIdentity

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators

theorem nat_list_square_sum_le (xs : List ℕ) :
    (xs.map (fun x : ℕ => (x : ℤ)^2)).sum ≤ (xs.sum : ℤ)^2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    have hx : (0 : ℤ) ≤ x := by positivity
    have hs : (0 : ℤ) ≤ xs.sum := by positivity
    nlinarith [mul_nonneg hx hs]

theorem member_square_sum_bound (xs : List ℕ) (b : ℕ) (hb : b ∈ xs) :
    (xs.map (fun x : ℕ => (x : ℤ)^2)).sum ≤ (b : ℤ)^2+((xs.sum-b : ℕ) : ℤ)^2 := by
  have hp := List.perm_cons_erase hb
  have hsum := hp.sum_eq
  simp only [List.sum_cons] at hsum
  have hsquares := (hp.map (fun x : ℕ => (x : ℤ)^2)).sum_eq
  simp only [List.map_cons,List.sum_cons] at hsquares
  have hrest := nat_list_square_sum_le (xs.erase b)
  have he : (xs.erase b).sum=xs.sum-b := by omega
  rw [he] at hrest
  linarith

theorem half_bounded_square_sum (xs : List ℕ) (s : ℤ)
    (hbound : ∀ x ∈ xs, 2*(x : ℤ) ≤ s) :
    2*(xs.map (fun x : ℕ => (x : ℤ)^2)).sum ≤ s*(xs.sum : ℤ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hbound x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hbound y (List.mem_cons_of_mem _ hy))
    have hp := mul_nonneg (show (0 : ℤ) ≤ x by positivity) (show 0 ≤ s-2*(x : ℤ) by omega)
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    nlinarith

/-- The internal geometric reserve pays the actual shell price using only
positivity of the root peak (the constant 2 rather than 1). -/
theorem internal_shell_positive_peak_paid (E H t outside : ℤ)
    (hH : 1 ≤ H) (ht : 1 ≤ t) (he : 2 ≤ outside)
    (hprice : E ≤ 2-2*(H-t^2/4))
    (hgeom : t^2-t%2+8*(t/2)*outside ≤ 4*H) : E ≤ 0 := by
  by_cases hsmall : t/2=0
  · have ht1 : t=1 := by omega
    rw [ht1] at hprice
    norm_num at hprice
    omega
  · have hhalf : 1 ≤ t/2 := by omega
    have hprod := mul_nonneg (show 0 ≤ t/2-1 by omega) (show 0 ≤ outside by omega)
    have hfloor : 4*(t^2/4) ≤ t^2 := by omega
    have hpar : t%2 ≤ 1 := by omega
    nlinarith

#print axioms member_square_sum_bound
#print axioms internal_shell_positive_peak_paid
end LRX.FiniteCuts

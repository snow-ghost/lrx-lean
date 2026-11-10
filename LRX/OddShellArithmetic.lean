module

public import LRX.ShellWidthArithmetic

@[expose] public section

namespace LRX.FiniteCuts

theorem odd_shell_member_price_bound (n : ℕ) (l c b U H squares : ℤ)
    (hsize : (n : ℤ)=2*l+c+b+1) (hsquares : squares ≤ c^2) :
    3-U-2*H-(n%2 : ℕ)-(2*(((n : ℤ)-2*l)^2/4)-(squares+b^2)) ≤
      2-U-2*c-2*(H-(b-c-1)^2/4) := by
  have hs := floor_square_even_shift n l
  have ht := floor_square_even_shift n (l+c+1)
  have heq : (n : ℤ)-2*(l+c+1)=b-c-1 := by omega
  rw [heq] at ht
  rw [hsize] at hs ⊢
  nlinarith

theorem odd_shell_nondominant_paid (n : ℕ) (l U H : ℤ) (xs : List ℕ)
    (hsize : (n : ℤ)=2*l+(xs.sum : ℤ)+1) (hU : 1 ≤ U) (hH : 0 ≤ H)
    (hs : 2 ≤ xs.sum) (hbound : ∀ b ∈ xs, 2*b ≤ xs.sum+1) :
    3-U-2*H-(n%2 : ℕ)-(2*(((n : ℤ)-2*l)^2/4)-
      (xs.map (fun x : ℕ => (x : ℤ)^2)).sum) ≤ 0 := by
  have hcap := half_bounded_square_sum xs ((xs.sum : ℤ)+1) (by
    intro b hb
    have hh := hbound b hb
    exact_mod_cast hh)
  have hfloor := floor_square_even_shift n l
  have heq : (n : ℤ)-2*l=(xs.sum : ℤ)+1 := by omega
  rw [heq] at hfloor ⊢
  have hp : 0 ≤ ((n%2 : ℕ) : ℤ) := by positivity
  have hs' : (2 : ℤ) ≤ xs.sum := by exact_mod_cast hs
  nlinarith

#print axioms odd_shell_member_price_bound
#print axioms odd_shell_nondominant_paid
end LRX.FiniteCuts

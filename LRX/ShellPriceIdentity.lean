module

public import LRX.FirstGapSharpWord

@[expose] public section

namespace LRX.FiniteCuts

theorem floor_square_even_shift (n : ℕ) (k : ℤ) :
    4*(((n : ℤ)-2*k)^2/4)=((n : ℤ)-2*k)^2-(n%2 : ℕ) := by
  have hshift : ((n : ℤ)-2*k)^2/4=(n : ℤ)^2/4+(k^2-(n : ℤ)*k) := by
    rw [show ((n : ℤ)-2*k)^2=(n : ℤ)^2+(k^2-(n : ℤ)*k)*4 by ring]
    exact Int.add_mul_ediv_right _ _ (by norm_num)
  have hh := FiniteGaps.floor_square_identity n
  rw [hshift]
  nlinarith

theorem shell_exterior_price_bound (n : ℕ) (l c e U H squares : ℤ)
    (hsize : (n : ℤ)=2*l+c+e) (hU : 1 ≤ U) (hsquares : squares ≤ c^2) :
    3-U-2*H-(n%2 : ℕ)-(2*(((n : ℤ)-2*l)^2/4)-(squares+e^2)) ≤
      2-2*(H-(e-c)^2/4) := by
  have hs := floor_square_even_shift n l
  have ht := floor_square_even_shift n (l+c)
  have heq : (n : ℤ)-2*(l+c)=e-c := by omega
  rw [heq] at ht
  rw [hsize] at hs ⊢
  nlinarith

theorem shell_price_identity (n l : ℕ) (hn : 1 ≤ n) (D U squares : ℤ) :
    (2*D-(n : ℤ)+3+(n/2 : ℕ)-U+squares)-(n.choose 2 : ℤ)=
      3-U-2*((l : ℤ)*((n : ℤ)-l)-D)-(n%2 : ℕ)-
        (2*(((n : ℤ)-2*(l : ℤ))^2/4)-squares) := by
  letI : NeZero n := ⟨by omega⟩
  have hshift : ((n : ℤ)-2*(l : ℤ))^2/4=
      (n : ℤ)^2/4+((l : ℤ)^2-(n : ℤ)*l) := by
    rw [show ((n : ℤ)-2*(l : ℤ))^2=(n : ℤ)^2+
      ((l : ℤ)^2-(n : ℤ)*l)*4 by ring]
    exact Int.add_mul_ediv_right _ _ (by norm_num)
  have hquarter := FiniteGaps.quarter_budget hn
  have hpar : (n : ℤ)=2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ) := by omega
  rw [hshift]
  nlinarith

#print axioms shell_price_identity
end LRX.FiniteCuts

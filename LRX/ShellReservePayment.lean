module

public import LRX.ActualTwoNeighborReserve

@[expose] public section

/-! Scalar consequences for manuscript E4/E5. E is the prospective shell
word's upper excess, not the original peakExcess. Constructing that word
and identifying its price remain separate obligations. -/
namespace LRX.ShellReservePayment

/-- The new linear reserve removes all t=1 and positive-hole exceptions.
Only two small configurations survive the exterior scalar inequalities. -/
theorem even_exterior_unpaid_cases (l c t H E variance : ℤ)
    (hc : 0 ≤ c) (ht : 1 ≤ t) (htop : t ≤ 2*l-2)
    (he : 2 ≤ c+t) (hlinear : c+t-1 ≤ H)
    (hquadratic : t^2/4 ≤ H)
    (harea : l*(l+2*c+t)-4*(2*l+c-2) ≤ H)
    (hparity : (l*(l+2*c+t)-H)%2=0)
    (hv : 0 ≤ variance)
    (hprice : E ≤ 1-2*(H-t^2/4)-variance) (hunpaid : 0 < E) :
    (l=3 ∧ c=0 ∧ t=2 ∧ H=1) ∨ (l=3 ∧ c=0 ∧ t=3 ∧ H=2) := by
  have hl : 2 ≤ l := by omega
  have hHeq : H=t^2/4 := by omega
  have ht2 : 2 ≤ t := by
    by_contra hh
    have ht1 : t=1 := by omega
    rw [ht1] at hHeq hlinear he
    norm_num at hHeq
    omega
  have hfloor : 4*(t^2/4) ≤ t^2 := by omega
  have hmon := mul_nonneg (show 0 ≤ t-2 by omega) (show 0 ≤ 4*l-t-2 by omega)
  have hcp := mul_nonneg (show 0 ≤ 2*l-4 by omega) hc
  have hl4 : l ≤ 4 := by
    by_contra hh
    have hprod := mul_nonneg (show 0 ≤ l-5 by omega) (show 0 ≤ l-1 by omega)
    nlinarith only [harea,hHeq,hfloor,hmon,hcp,hprod]
  interval_cases l <;> interval_cases t <;> norm_num at hHeq harea hlinear hparity
  all_goals omega

#print axioms even_exterior_unpaid_cases
end LRX.ShellReservePayment

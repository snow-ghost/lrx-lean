import LRX.CoupledPeakCutoff

namespace CoupledPeakCutoff
theorem coupled_residual_precise_cutoff (m p t U eps a r S2 : ℤ)
    (ht : 2 ≤ t) (hm : 2*t+1 ≤ m) (hp : p=0 ∨ p=1)
    (hU0 : 1 ≤ U) (hU : U ≤ 3*t+1) (he : eps ≤ 3*t+6) (ha : 0 ≤ a)
    (hr : 4 ≤ r)
    (harea : 2*(m*(m+p)-eps) ≤ 4*U*(2*m+p-2*t-a-U)+S2)
    (hcap : S2 ≤ (m-1)*(2*m+p-r))
    (henv : 3 ≤ t ∨ 200 ≤ m →
      S2 ≤ (m-1)^2+(m+1-(r-p)-width t)^2+(width t)^2)
    (hH : (2*m+p-r)^2-2*S2 ≤ 6*t-3)
    (hcubic : 3 ≤ t → t^3-3*t^2+3*t+1 ≤ m) :
    m < cutoff t := by
  have hp0 : 0 ≤ p := by omega
  have hp1 : p ≤ 1 := by omega
  have hrbound := support_cap_all_sizes m p t U eps a r S2 ht hm hp hU0 he ha harea hcap
  have hu : 3 ≤ r-p := by omega
  have huupper : r-p ≤ 24*t+9 := by omega
  have hdensity (hg : 3 ≤ t ∨ 200 ≤ m) :
      4*width t*(m-1) ≤ (r-p+2*width t-2)^2+6*t-3 := by
    have h := coupled_density m (r-p) (width t) S2 ((2*m+p-r)^2-2*S2)
      (by ring) (henv hg)
    linarith
  have hcoarse (hg : 3 ≤ t ∨ 200 ≤ m) (hmb : 6*t+2 ≤ m) :
      areaGap t (width t) m (r-p) ≤ 0 :=
    coarse_area m p t U eps a S2 (r-p) (width t)
      hp0 (by omega) hU hmb ha he harea (henv hg)
  have ht9 : t ≤ 9 := by
    by_cases h2 : t=2
    · omega
    have ht3 : 3 ≤ t := by omega
    apply component_count_le_nine t m ht3 (hcubic ht3)
    by_cases hmb : 6*t+2 ≤ m
    · exact linear_cutoff t m (r-p) ht3 hu huupper
        (hdensity (Or.inl ht3)) (hcoarse (Or.inl ht3) hmb)
    · omega
  have hcut : m < cutoff t := by
    by_contra h
    have hmb : 6*t+2 ≤ m := le_trans (certificate_table t ht ht9).2.2.1 (by omega)
    have hg : 3 ≤ t ∨ 200 ≤ m := by
      by_cases h2 : t=2
      · subst t
        norm_num [cutoff] at h
        exact Or.inr h
      · exact Or.inl (by omega)
    exact no_large_scalar t m (r-p) ht ht9 (by omega) hu huupper
      (hdensity hg) (hcoarse hg hmb)
  exact hcut

theorem precise_cutoff_of_unpaid_peak (m p t f a v B U eps r S2 : ℤ)
    (ht : 2 ≤ t) (hm : 2*t+1 ≤ m) (hp : p=0 ∨ p=1)
    (hf : 0 ≤ f) (ha : 0 ≤ a) (haf : a ≤ f) (hv : 2*t ≤ v) (hU : 1 ≤ U)
    (hBzero : a=0 → B ≤ t) (hBpos : 1 ≤ a → B ≤ a+t-1)
    (hactivity : f^2 ≤ 4*eps+p) (hcredit : 0 ≤ 2*eps+p-f)
    (hpeak : 1 ≤ 2*B+t-U-(2*eps+p-f))
    (hreserve : 1 ≤ 2*B+m-U-2-2*(t-1)*(v-t)-a*v-eps)
    (htail : 2*f+t^2-2*(v-t) ≤ eps)
    (hr : 4 ≤ r) (hV : 3 ≤ 2*m+p-r)
    (hC9 : (2*m+p-r)^2-2*S2+2*(2*m+p-r-1)*a+a^2+p ≤
      2*(2*eps+p-f))
    (hC10 : 2*(m*(m+p)-eps) ≤ 4*U*(2*m+p-v-a-U)+S2)
    (hcap : S2 ≤ (m-1)*(2*m+p-r))
    (henv : 3 ≤ t ∨ 200 ≤ m →
      S2 ≤ (m-1)^2+(m+1-(r-p)-width t)^2+(width t)^2) :
    m < cutoff t := by
  obtain ⟨he,hu,hcubic,hA⟩ := unpaid_prebounds m p t f a v B U eps
    ht (by omega) (by omega) hf ha haf hv hU hBzero hBpos
    hactivity hcredit hpeak hreserve htail
  have hH := unpaid_density_allowance (2*m+p-r) S2 a p (2*eps+p-f) t
    hV ha (by omega) hC9 hA
  have hprod := mul_nonneg (show 0 ≤ U by omega) (show 0 ≤ v-2*t by omega)
  have harea : 2*(m*(m+p)-eps) ≤ 4*U*(2*m+p-2*t-a-U)+S2 := by nlinarith
  exact coupled_residual_precise_cutoff m p t U eps a r S2 ht hm hp hU hu he ha hr
    harea hcap henv hH hcubic


#print axioms precise_cutoff_of_unpaid_peak
end CoupledPeakCutoff

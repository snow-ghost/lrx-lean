import LRX.FinitePeakProfile

namespace LRX.FinitePeak.Profile

/-- C11 and the two reserves constrain the resource before x is examined. -/
theorem admissible_resource_linear (r : Profile) (hr : r.Admissible) :
    2*r.T ≤ 2*r.m-2*r.t^3+5*r.t^2-4*r.t-4-(r.t+2)*r.fixed := by
  obtain ⟨hd,hs,_⟩ := hr
  obtain ⟨ht,_,_,_,hf,_,_,_,ha,haf,hU,_,_,_,hv,_,_⟩ := hd
  obtain ⟨_,_,hfirst,htail,_,_⟩ := hs
  have hB : r.B ≤ r.isolated+r.t := by
    unfold B
    split_ifs <;> omega
  have hBf : r.B ≤ r.fixed+r.t := by omega
  have he : 2*r.eps ≤ 3*r.fixed+3*r.t-2 := by
    unfold A at hfirst
    linarith
  have hchoose : 0 ≤ (r.isolated.toNat.choose 2 : ℤ) := by positivity
  have hav : 0 ≤ r.isolated*(r.exterior-2) :=
    mul_nonneg ha (by omega)
  have hT : r.T ≤ r.m+2*r.t^2-4-2*(r.t-1)*r.exterior-r.eps := by
    unfold T M
    nlinarith only [hB,hU,hchoose,hav]
  have hc11 := mul_nonneg (show 0 ≤ r.t-1 by omega)
    (show 0 ≤ r.eps-2*r.fixed-r.t^2+2*(r.exterior-r.t) by linarith only [htail])
  have hE := mul_nonneg (show 0 ≤ r.t-2 by omega)
    (show 0 ≤ 3*r.fixed+3*r.t-2-2*r.eps by omega)
  nlinarith only [hT,hc11,hE]

set_option maxHeartbeats 800000 in
/-- The extreme count t=7 is incompatible with actual necessary energy filters. -/
theorem admissible_count_ne_seven (r : Profile) (hr : r.Admissible) : r.t ≠ 7 := by
  intro ht7
  have hlin := admissible_resource_linear r hr
  obtain ⟨hd,hs,hfilters⟩ := hr
  obtain ⟨ht,_,hp0,hp1,hf0,_,he0,he1,ha0,_,hU0,hU1,_,hm1,hv0,_,_,_,_,_,_⟩ := hd
  obtain ⟨_,_,_,_,hT0,_,_,_⟩ := hs
  have hB : r.B ≤ r.isolated+r.t := by unfold B; split_ifs <;> omega
  have hchoose : 0 ≤ (r.isolated.toNat.choose 2 : ℤ) := by positivity
  have hav : 0 ≤ r.isolated*(r.exterior-2) := mul_nonneg ha0 (by omega)
  have hTupper : r.T ≤ r.m+95-12*r.exterior-r.eps := by
    unfold T M
    rw [ht7]
    rw [ht7] at hB
    nlinarith only [hB,hU0,hchoose,hav]
  have hT52 : r.T ≤ 52 := by rw [ht7] at hlin; nlinarith only [hlin,hm1,hf0]
  have hm236 : 236 ≤ r.m := by rw [ht7] at hlin; nlinarith only [hlin,hT0,hf0]
  have hv31 : r.exterior ≤ 31 := by omega
  have hL : r.L ≤ 577 := by unfold L n; omega
  have henergy : 55600 ≤ r.energy := by
    unfold energy
    have hp := mul_nonneg (show 0 ≤ r.m by omega) hp0
    nlinarith only [sq_nonneg (r.m-236),hm236,he1,hp,ht7]
  have hprod : r.peak*(r.L-r.peak) ≤ 22*577 := by
    have h1 := mul_nonneg (show 0 ≤ r.peak by omega) (show 0 ≤ 577-(r.L-r.peak) by omega)
    have h2 := mul_nonneg (show 0 ≤ 22-r.peak by omega) (show (0:ℤ) ≤ 577 by norm_num)
    nlinarith only [h1,h2]
  have hE2 : r.E2 ≤ 385 := by
    unfold E2
    rw [ht7]
    have hp := mul_nonneg (show 0 ≤ r.exterior-14 by omega) (show 0 ≤ 31-r.exterior by omega)
    nlinarith only [hp,hv0,hv31,ht7]
  have hc : r.correction ≤ 1 := by unfold correction; split_ifs <;> omega
  have hTe : 4*r.T*(r.T+r.correction) ≤ 11024 := by
    have h1 := mul_nonneg hT0 (show 0 ≤ 1-r.correction by omega)
    have h2 := mul_nonneg (show 0 ≤ 52-r.T by omega) (show 0 ≤ r.T+53 by omega)
    nlinarith only [h1,h2]
  have he := hfilters.2.2.1
  have hmod : 0 ≤ r.exterior%2 := Int.emod_nonneg _ (by norm_num)
  unfold need at he
  linarith only [he,hmod,hE2,hTe,henergy,hprod]

set_option maxHeartbeats 800000 in
theorem admissible_count_ne_six (r : Profile) (hr : r.Admissible) : r.t ≠ 6 := by
  intro ht6
  have hlin := admissible_resource_linear r hr
  obtain ⟨hd,hs,hfilters⟩ := hr
  obtain ⟨ht,_,hp0,hp1,hf0,_,he0,he1,ha0,_,hU0,hU1,_,hm1,hv0,_,_,_,_,_,_⟩ := hd
  obtain ⟨_,_,_,_,hT0,_,_,_⟩ := hs
  have hB : r.B ≤ r.isolated+r.t := by unfold B; split_ifs <;> omega
  have hchoose : 0 ≤ (r.isolated.toNat.choose 2 : ℤ) := by positivity
  have hav : 0 ≤ r.isolated*(r.exterior-2) := mul_nonneg ha0 (by omega)
  have hTupper : r.T ≤ r.m+68-10*r.exterior-r.eps := by
    unfold T M
    rw [ht6]
    rw [ht6] at hB
    nlinarith only [hB,hU0,hchoose,hav]
  have hTm : r.T ≤ r.m-140 := by rw [ht6] at hlin; nlinarith only [hlin,hf0]
  have hm140 : 140 ≤ r.m := by omega
  have hv35 : r.exterior ≤ 35 := by omega
  have hL : r.L ≤ 2*r.m+1 := by unfold L n; omega
  have henergy : r.m^2-24 ≤ r.energy := by
    unfold energy
    have hp := mul_nonneg (show 0 ≤ r.m by omega) hp0
    nlinarith only [he1,hp,ht6]
  have hprod : r.peak*(r.L-r.peak) ≤ 19*(2*r.m+1) := by
    have h1 := mul_nonneg (show 0 ≤ r.peak by omega)
      (show 0 ≤ 2*r.m+1-(r.L-r.peak) by omega)
    have h2 := mul_nonneg (show 0 ≤ 19-r.peak by omega)
      (show 0 ≤ 2*r.m+1 by omega)
    nlinarith only [h1,h2]
  have hE2 : r.E2 ≤ 645 := by
    unfold E2
    rw [ht6]
    have hp := mul_nonneg (show 0 ≤ r.exterior-12 by omega) (show 0 ≤ 35-r.exterior by omega)
    nlinarith only [hp,hv0,hv35,ht6]
  have hc : r.correction ≤ 1 := by unfold correction; split_ifs <;> omega
  have hTe : 4*r.T*(r.T+r.correction) ≤ 4*(r.m-140)*(r.m-139) := by
    have h1 := mul_nonneg hT0 (show 0 ≤ 1-r.correction by omega)
    have h2 := mul_nonneg (show 0 ≤ r.m-140-r.T by omega)
      (show 0 ≤ r.m-139+r.T by omega)
    nlinarith only [h1,h2]
  have he := hfilters.2.2.1
  have hmod : 0 ≤ r.exterior%2 := Int.emod_nonneg _ (by norm_num)
  have hconcave := mul_nonneg (show 0 ≤ r.m-140 by omega) (show 0 ≤ 288-r.m by omega)
  unfold need at he
  nlinarith only [he,hmod,hE2,hTe,henergy,hprod,hconcave,hm140]

theorem admissible_count_le_five (r : Profile) (hr : r.Admissible) : r.t ≤ 5 := by
  have h6 := admissible_count_ne_six r hr
  have h7 := admissible_count_ne_seven r hr
  have ht := hr.1.2.1
  omega

#print axioms admissible_resource_linear
#print axioms admissible_count_ne_six
#print axioms admissible_count_le_five
#print axioms admissible_count_ne_seven
end LRX.FinitePeak.Profile

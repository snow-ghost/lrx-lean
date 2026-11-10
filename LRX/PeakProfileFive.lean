module

public import LRX.PeakProfileLargeCount
public import LRX.CoupledPeakCutoff

@[expose] public section

namespace LRX.FinitePeak.Profile

/-- Retain the peak in the resource bound instead of replacing it by one. -/
theorem admissible_resource_peak_linear (r : Profile) (hr : r.Admissible) :
    2*r.T ≤ 2*r.m-2*r.t^3+5*r.t^2-3*r.t-4-r.t*r.peak-(r.t+2)*r.fixed := by
  obtain ⟨hd,hs,_⟩ := hr
  obtain ⟨ht,_,_,_,_,_,_,_,ha,haf,_,_,_,_,hv,_,_⟩ := hd
  obtain ⟨_,_,hfirst,htail,_,_⟩ := hs
  have hB : r.B ≤ r.isolated+r.t := by unfold B; split_ifs <;> omega
  have hBf : r.B ≤ r.fixed+r.t := by omega
  have he : 2*r.eps ≤ 3*r.fixed+3*r.t-r.peak-1 := by
    unfold A at hfirst
    linarith
  have hchoose : 0 ≤ (r.isolated.toNat.choose 2 : ℤ) := by positivity
  have hav : 0 ≤ r.isolated*(r.exterior-2) := mul_nonneg ha (by omega)
  have hT : r.T ≤ r.m+2*r.t^2-3-r.peak-2*(r.t-1)*r.exterior-r.eps := by
    unfold T M
    nlinarith only [hB,hchoose,hav]
  have hc11 := mul_nonneg (show 0 ≤ r.t-1 by omega)
    (show 0 ≤ r.eps-2*r.fixed-r.t^2+2*(r.exterior-r.t) by linarith only [htail])
  have hE := mul_nonneg (show 0 ≤ r.t-2 by omega)
    (show 0 ≤ 3*r.fixed+3*r.t-r.peak-1-2*r.eps by omega)
  nlinarith only [hT,hc11,hE]

set_option maxHeartbeats 800000 in
/-- The precise t=5 cutoff makes the energy filter contradictory. -/
theorem admissible_count_ne_five_of_size (r : Profile) (hr : r.Admissible)
    (hm : r.m ≤ 236) : r.t ≠ 5 := by
  intro ht5
  have hlin := admissible_resource_peak_linear r hr
  obtain ⟨hd,hs,hfilters⟩ := hr
  obtain ⟨ht,_,hp0,hp1,hf0,_,he0,he1,ha0,_,hU0,hU1,_,_,hv0,_,_,_,_,_,_⟩ := hd
  obtain ⟨_,_,_,_,hT0,_,_,_⟩ := hs
  have hB : r.B ≤ r.isolated+r.t := by unfold B; split_ifs <;> omega
  have hchoose : 0 ≤ (r.isolated.toNat.choose 2 : ℤ) := by positivity
  have hav : 0 ≤ r.isolated*(r.exterior-2) := mul_nonneg ha0 (by omega)
  have hTupper : r.T ≤ r.m+47-r.peak-8*r.exterior-r.eps := by
    unfold T M
    rw [ht5]
    rw [ht5] at hB
    nlinarith only [hB,hchoose,hav]
  have hTm : 2*r.T ≤ 2*r.m-144-5*r.peak := by
    rw [ht5] at hlin
    nlinarith only [hlin,hf0]
  have hm75 : 75 ≤ r.m := by omega
  have hv35 : r.exterior ≤ 35 := by omega
  have hL : r.L ≤ 2*r.m-9 := by unfold L n; omega
  have henergy : r.m^2-21 ≤ r.energy := by
    unfold energy
    have hp := mul_nonneg (show 0 ≤ r.m by omega) hp0
    nlinarith only [he1,hp,ht5]
  have hprod : r.peak*(r.L-r.peak) ≤ r.peak*(2*r.m-9-r.peak) := by
    have h1 := mul_nonneg (show 0 ≤ r.peak by omega) (show 0 ≤ 2*r.m-9-r.L by omega)
    nlinarith only [h1]
  have hE2 : r.E2 ≤ 745 := by
    unfold E2
    rw [ht5]
    have hp := mul_nonneg (show 0 ≤ r.exterior-10 by omega) (show 0 ≤ 35-r.exterior by omega)
    nlinarith only [hp,hv0,hv35,ht5]
  have hc : r.correction ≤ 1 := by unfold correction; split_ifs <;> omega
  have hTe : 4*r.T*(r.T+r.correction) ≤
      (2*r.m-144-5*r.peak)*(2*r.m-142-5*r.peak) := by
    have h1 := mul_nonneg hT0 (show 0 ≤ 1-r.correction by omega)
    have h2 := mul_nonneg (show 0 ≤ 2*r.m-144-5*r.peak-2*r.T by omega)
      (show 0 ≤ 2*r.m-142-5*r.peak+2*r.T by omega)
    nlinarith only [h1,h2]
  have hylo : 64 ≤ r.m-3*r.peak := by omega
  have hyhi : r.m-3*r.peak ≤ 233 := by omega
  have hconcave := mul_nonneg (show 0 ≤ r.m-3*r.peak-64 by omega)
    (show 0 ≤ 233-(r.m-3*r.peak) by omega)
  have hUc := mul_nonneg (show 0 ≤ r.peak by omega) (show 0 ≤ 16-r.peak by omega)
  have he := hfilters.2.2.1
  have hmod : 0 ≤ r.exterior%2 := Int.emod_nonneg _ (by norm_num)
  unfold need at he
  nlinarith only [he,hmod,hE2,hTe,henergy,hprod,hconcave,hUc,hyhi,hU0]

/-- The precise cutoff and necessary filters leave only t=2,3,4. -/
theorem precise_admissible_count_size (r : Profile) (hr : r.Admissible)
    (hcut : r.m < CoupledPeakCutoff.cutoff r.t) :
    r.t ≤ 4 ∧ r.m ≤ 223 ∧ r.n ≤ 447 := by
  have hcount := admissible_count_le_five r hr
  have hnot5 : r.t ≠ 5 := by
    intro h5
    have hm : r.m ≤ 236 := by
      rw [h5] at hcut
      norm_num [CoupledPeakCutoff.cutoff] at hcut
      omega
    exact admissible_count_ne_five_of_size r hr hm h5
  have ht4 : r.t ≤ 4 := by omega
  have ht2 := hr.1.1
  have hm223 : r.m ≤ 223 := by
    have hcases : r.t=2 ∨ r.t=3 ∨ r.t=4 := by omega
    rcases hcases with h | h | h <;> rw [h] at hcut <;>
      norm_num [CoupledPeakCutoff.cutoff] at hcut <;> omega
  have hp1 := hr.1.2.2.2.1
  refine ⟨ht4,hm223,?_⟩
  unfold n
  omega

#print axioms admissible_resource_peak_linear
#print axioms admissible_count_ne_five_of_size
end LRX.FinitePeak.Profile

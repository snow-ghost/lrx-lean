module

public import LRX.PeakProfileFive

@[expose] public section

namespace LRX.FinitePeak.Profile

/-- The actual support bound is expressed using the unchanged hole count. -/
def CoreBound (r : Profile) : Prop :=
  2*r.m+2*r.parity-r.exterior-8*r.peak-1 ≤ r.holes

theorem admissible_count_ne_four (r : Profile) (hr : r.Admissible)
    (hcore : r.CoreBound) : r.t ≠ 4 := by
  intro ht4
  obtain ⟨hd,hs,_⟩ := hr
  obtain ⟨_,_,hp0,_,hf0,_,he0,_,ha,haf,_,hU,_,_,hv,_,_⟩ := hd
  obtain ⟨_,_,hfirst,htail,_,hwidth,_,_⟩ := hs
  have hB : r.B ≤ r.isolated+r.t := by unfold B; split_ifs <;> omega
  have hBf : r.B ≤ r.fixed+r.t := by omega
  have he : 2*r.eps ≤ 3*r.fixed+11-r.peak := by
    unfold A at hfirst
    omega
  have hchoose : 0 ≤ (r.isolated.toNat.choose 2 : ℤ) := by positivity
  have hav : 0 ≤ r.isolated*(r.exterior-2) := mul_nonneg ha (by omega)
  have hT : r.T ≤ r.m+29-r.peak-6*r.exterior-r.eps := by
    unfold T M
    rw [ht4]
    rw [ht4] at hB
    nlinarith only [hB,hchoose,hav]
  unfold CoreBound at hcore
  have hlinear : 215+19*r.fixed ≤ 17*r.peak := by
    rw [ht4] at htail
    nlinarith only [hcore,hwidth,hT,htail,he,ha,hp0]
  have hfzero : r.fixed=0 := by omega
  have hUb : r.peak ≤ 11 := by omega
  omega

/-- Eliminating both m and x gives a purely exterior necessary inequality. -/
theorem admissible_core_exterior_filter (r : Profile) (hr : r.Admissible)
    (hcore : r.CoreBound) :
    (4*r.t-5+2*r.isolated)*r.exterior ≤
      4*r.B+6*r.peak-5-2*r.parity+4*r.t*(r.t-1)-
        2*(r.isolated.toNat.choose 2 : ℤ)+r.fixed-r.isolated-2*r.eps := by
  have hwidth := hr.2.1.2.2.2.2.2.1
  unfold CoreBound at hcore
  unfold T M at hwidth
  nlinarith only [hcore,hwidth]

#print axioms admissible_core_exterior_filter
#print axioms admissible_count_ne_four
end LRX.FinitePeak.Profile

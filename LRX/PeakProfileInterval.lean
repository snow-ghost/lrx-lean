module

public import LRX.FinitePeakProfile
public import LRX.ScalarIntervalCertificate

@[expose] public section

/-! M4: interval certificates reject a scalar profile while retaining its actual x. -/
namespace LRX.FinitePeak.Profile

def intervalData (r : Profile) : ScalarIntervalCertificate.Data :=
  ScalarIntervalCertificate.fromScalars r.L r.cap r.exterior r.isolated r.fixed
    r.parity r.eps r.peak r.T r.energy r.E2

theorem admissible_interval_feasible (r : Profile) (hr : r.Admissible) :
    r.intervalData.feasible r.holes := by
  obtain ⟨hd,hs,hf⟩ := hr
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hx0,hxL⟩ := hd
  obtain ⟨_,_,_,_,_,hxT,_,hxh⟩ := hs
  obtain ⟨hJ,hlinear,_,harea,henergy,hdensity⟩ := hf
  apply ScalarIntervalCertificate.feasible_of_scalar_filters
    r.L r.cap r.exterior r.isolated r.fixed r.parity r.eps r.peak r.T
    r.energy r.E2 r.holes hx0 hxL hxT hxh
  · dsimp only [need, B0] at hlinear
    linarith only [hlinear]
  · change 2*r.energy-4*r.peak*(r.L-r.peak) ≤ r.J+r.E2
    dsimp only [need] at hJ
    linarith only [hJ]
  · exact harea
  · exact henergy
  · exact hdensity

theorem verified_interval_not_admissible (r : Profile) (lo hi : ℤ)
    (hv : ScalarIntervalCertificate.verify r.intervalData lo hi = true) :
    ¬r.Admissible := by
  intro hr
  exact ScalarIntervalCertificate.verify_sound _ lo hi hv _
    (admissible_interval_feasible r hr)

#print axioms admissible_interval_feasible
#print axioms verified_interval_not_admissible
end LRX.FinitePeak.Profile

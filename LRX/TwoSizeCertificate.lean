import LRX.TwoOuterTable
import LRX.PeakProfileInterval

namespace LRX.FinitePeak

def twoProfileOfOuter (o : OuterRow) (m x : ℤ) : Profile :=
  ⟨2,m,o.1,o.2.1,o.2.2.1,o.2.2.2.1,o.2.2.2.2.1,o.2.2.2.2.2,x⟩

def TwoSizeNecessary (r : Profile) : Prop :=
  5+r.isolated ≤ r.m ∧ r.energy%2=0 ∧ 2*r.peak ≤ r.L ∧ 0 ≤ r.T ∧ 0 ≤ r.cap ∧
  r.need ≤ r.E2-r.exterior%2+4*r.T*(r.T+r.correction)

instance (r : Profile) : Decidable (TwoSizeNecessary r) := by
  unfold TwoSizeNecessary
  infer_instance

def KeptTwoSize (o : OuterRow) (m : ℤ) : Prop := m ≤ 36 ∧ o.2.2.2.2.2 ≤ 7

instance (o : OuterRow) (m : ℤ) : Decidable (KeptTwoSize o m) := by
  unfold KeptTwoSize
  infer_instance

def checkTwoSize (o : OuterRow) (m : ℤ) (cert : ℤ × ℤ) : Bool :=
  let r := twoProfileOfOuter o m 0
  decide (¬TwoSizeNecessary r ∨ KeptTwoSize o m ∨
    ScalarIntervalCertificate.verify r.intervalData cert.1 cert.2=true)

theorem admissible_two_size_necessary (r : Profile) (hr : r.Admissible) (ht : r.t=2) :
    TwoSizeNecessary r := by
  obtain ⟨hd,hs,hf⟩ := hr
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hm,_,_,_,_,hpar,hwidth,_⟩ := hd
  obtain ⟨_,_,_,_,hT,_,hcap,_⟩ := hs
  exact ⟨by rw [ht] at hm; omega,hpar,hwidth,hT,hcap,hf.2.2.1⟩

theorem check_two_size_sound (o : OuterRow) (m x : ℤ) (cert : ℤ × ℤ)
    (hc : checkTwoSize o m cert=true) (hr : (twoProfileOfOuter o m x).Admissible) :
    KeptTwoSize o m := by
  have hs := admissible_two_size_necessary _ hr rfl
  have h := of_decide_eq_true hc
  change ¬TwoSizeNecessary (twoProfileOfOuter o m 0) ∨ KeptTwoSize o m ∨
    ScalarIntervalCertificate.verify (twoProfileOfOuter o m 0).intervalData cert.1 cert.2=true at h
  rcases h with h | h | h
  · exact False.elim (h hs)
  · exact h
  · exact False.elim (Profile.verified_interval_not_admissible (twoProfileOfOuter o m x)
      cert.1 cert.2 h hr)

#print axioms check_two_size_sound
end LRX.FinitePeak

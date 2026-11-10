import LRX.ActualPeakProfile

/-! Connect every computable envelope filter to the original unpaid map.
The resulting necessary predicate is ready for a trusted finite classifier. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords FinitePeak
variable {n k : ℕ} [NeZero n]

theorem actual_peak_profile_need (p : State n) (root : Fin n) :
    (actualPeakProfile p root).need=2*(∑ i, |displacement p.symm i|)-
      4*(sourceHalfPeak p : ℤ)*(((componentSet p root).card : ℤ)-(sourceHalfPeak p : ℤ)) := by
  rw [FinitePeak.Profile.need,actual_peak_profile_energy,actual_peak_profile_L]
  rfl

theorem actual_peak_profile_E2 (p : State n) (root : Fin n) :
    (actualPeakProfile p root).E2=
      exteriorSquareBound
        (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root)) (componentSet p root).card).card
        (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root)) (componentSet p root).card, C.card) := rfl

theorem actual_peak_profile_J (p : State n) (root : Fin n) :
    (actualPeakProfile p root).J=internalSquareBound (((n/2 : ℕ) : ℤ)+(n%2 : ℕ)-2)
      ((componentSet p root).card-(prefixSourceCore (localTarget p 0 (componentLeft p root))).card) := rfl

theorem actual_peak_profile_exterior_mod (p : State n) (root : Fin n) :
    (actualPeakProfile p root).exterior%2=
      ((∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card, C.card)%2 : ℕ) := by
  dsimp only [actualPeakProfile]
  omega

set_option maxHeartbeats 800000 in
/-- Every envelope filter of the finite profile is a theorem about the actual map. -/
theorem actual_peak_profile_filters (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    (actualPeakProfile p root).Filters := by
  have hproper := component_card_lt_of_multiple_roots p (by omega) root
  have hJ := original_j_density_filter p hmaj root hlarge hproper
  have hh := original_unpaid_envelope_filters hn p hmaj hmax hc hk root hlarge hpos
  have he := original_unpaid_energy_density_filter hn p hmaj hmax hc hk root hlarge hpos
  have ha := original_unpaid_j_area_filter hn p hmaj hmax hc hk root hlarge hpos
  obtain ⟨hlinear,harea,henergy⟩ := hh
  dsimp only at hJ hlinear harea henergy he ha
  unfold FinitePeak.Profile.Filters
  rw [actual_peak_profile_need,actual_peak_profile_E2,actual_peak_profile_J,
    actual_peak_profile_exterior_mod]
  simp only [FinitePeak.Profile.B0,actual_peak_profile_T]
  simp only [FinitePeak.Profile.A,FinitePeak.Profile.correction,actualPeakProfile,Nat.cast_lt]
  exact ⟨by linarith only [hJ],by linarith only [hlinear],he,harea,henergy,ha⟩

/-- The full computable necessary condition for any original unpaid M4 peak. -/
theorem actual_unpaid_peak_profile_admissible (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc) :
    (actualPeakProfile p root).Admissible := by
  obtain ⟨hd,hr⟩ := actual_peak_profile_domain_reserves hn p hmaj hmax hc hk root hlarge ht hpos
  exact ⟨hd,hr,actual_peak_profile_filters hn p hmaj hmax hc hk root hlarge hpos⟩

#print axioms actual_peak_profile_filters
#print axioms actual_unpaid_peak_profile_admissible
end LRX.FiniteCuts

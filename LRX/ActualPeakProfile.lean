module

public import LRX.FinitePeakProfile
public import LRX.OriginalRefinedEnvelopeFilters
public import LRX.ActualPeakCutoff
public import LRX.PrefixCoreBalancedEnergy

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords FinitePeak
variable {n k : ℕ} [NeZero n]

noncomputable def actualPeakProfile (p : State n) (root : Fin n) : FinitePeak.Profile :=
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  { t := (nontrivialSuffixComponents q L).card
    m := ((n/2 : ℕ) : ℤ)
    parity := ((n%2 : ℕ) : ℤ)
    fixed := ((n-p.support.card : ℕ) : ℤ)
    eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    isolated := (singletonSuffixComponents q L).card
    peak := sourceHalfPeak p
    exterior := (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ)
    holes := ((L-(prefixSourceCore q).card : ℕ) : ℤ) }

theorem actual_peak_profile_n (p : State n) (root : Fin n) :
    (actualPeakProfile p root).n=(n : ℤ) := by
  dsimp only [actualPeakProfile,FinitePeak.Profile.n]
  omega

theorem actual_peak_profile_L (p : State n) (root : Fin n) :
    (actualPeakProfile p root).L=((componentSet p root).card : ℤ) := by
  have hLn : (componentSet p root).card ≤ n := by simpa using Finset.card_le_univ (componentSet p root)
  have htail := suffix_component_parameter_sum (localTarget p 0 (componentLeft p root))
    (componentSet p root).card hLn (component_recenter_cut p root).1
  unfold FinitePeak.Profile.L
  rw [actual_peak_profile_n]
  dsimp only [actualPeakProfile]
  omega

theorem actual_peak_profile_energy (p : State n) (root : Fin n) :
    (actualPeakProfile p root).energy=∑ i, |displacement p.symm i| := by
  have hn : (n : ℤ)=2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ) := by omega
  dsimp only [actualPeakProfile,FinitePeak.Profile.energy]
  nlinarith only [hn]

theorem actual_peak_profile_T (p : State n) (root : Fin n) :
    (actualPeakProfile p root).T=scalarFillingBudget p root := by
  simp only [actualPeakProfile,FinitePeak.Profile.T,FinitePeak.Profile.B,FinitePeak.Profile.M,
    scalarFillingBudget,Int.toNat_natCast,Nat.cast_eq_zero]

theorem source_half_peak_positive (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) : 0 < sourceHalfPeak p := by
  classical
  obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0 < (componentRoots p).card by omega)
  have hmove := component_root_moved p r hr
  have hs := component_universal_source p r hmove
    (fun i hi hp => component_root_reaches hn p hm r hr i hi hp)
  have htarget : (sourceTarget p).symm r ≠ r := by
    simpa only [sourceTarget,PrunedLift.permutation_symm_apply,ite_eq_left hs] using hmove
  exact moved_global_peak_positive (sourceTarget p).symm r htarget

set_option maxHeartbeats 1200000 in
/-- All finite domains and reserves are consequences of the original unpaid map. -/
theorem actual_peak_profile_domain_reserves (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc) :
    (actualPeakProfile p root).Domain ∧ (actualPeakProfile p root).Reserves := by
  classical
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let t := (nontrivialSuffixComponents q L).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
  let a := (singletonSuffixComponents q L).card
  let f := n-p.support.card
  let m : ℤ := (n/2 : ℕ)
  let parity : ℤ := (n%2 : ℕ)
  let eps : ℤ := m*((n : ℤ)-m)-(∑ i, |displacement p.symm i|)
  let U : ℤ := sourceHalfPeak p
  let B : ℤ := bridgeBudget (componentBridges p hc)
  let Bcap : ℤ := if (a : ℤ)=0 then (t : ℤ) else (a : ℤ)+(t : ℤ)-1
  let x := L-(prefixSourceCore q).card
  have hsize : 2 ≤ L := by dsimp only [L]; omega
  have hproper : L<n := component_card_lt_of_multiple_roots p (by omega) root
  have hqmajor : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hs : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  have hm : (∑ i, |displacement q.symm i|)=(∑ i, |displacement p.symm i|) :=
    component_cut_displacement_mass p root
  have htail := suffix_component_parameter_sum q L hproper.le (component_recenter_cut p root).1
  change v+a=n-L at htail
  have hv := nontrivial_suffix_size_sum q L
  change 2*t ≤ v at hv
  have hLlarge : (n+1)/2<L := hlarge
  have hvmax : v+a+1 ≤ n/2 := by omega
  have hmLower : 2*(t : ℤ)+(a : ℤ)+1 ≤ m := by
    have hh : 2*t+a+1 ≤ n/2 := by omega
    dsimp only [m]
    exact_mod_cast hh
  have hvUpper : (v : ℤ) ≤ m-(a : ℤ)-1 := by
    have hh : (v : ℤ)+(a : ℤ)+1 ≤ m := by
      dsimp only [m]
      exact_mod_cast hvmax
    omega
  have hcount := component_cut_external_count p root hsize
  change t+1=(componentRoots p).card at hcount
  have htk : t=k := by omega
  have hfixed := component_cut_filling_fixed_partition p (by omega) root hsize
  change _+_+a=f at hfixed
  have haf : a ≤ f := by omega
  have hU : 1 ≤ U := by
    have hh := source_half_peak_positive hn p (by omega)
    dsimp only [U]
    omega
  have hUwidth := large_component_source_peak_capacity p root hlarge
  have hact := canonical_fixed_activity_square p hmaj
  have hcredit := canonical_activity_credit_nonneg p hmaj
  change (f : ℤ)^2 ≤ 4*eps+parity at hact
  change 0 ≤ 2*eps+parity-(f : ℤ) at hcredit
  have heps : 0 ≤ eps := by
    have hh := majorized_canonical_energy p hmaj
    change _ ≤ m*((n : ℤ)-m) at hh
    dsimp only [eps]
    omega
  have hshort := component_short_arrow_energy_deficit q hqmajor L ht
  dsimp only at hshort
  rw [hs,hm] at hshort
  change 2*(f : ℤ)+(t : ℤ)^2-2*((v : ℤ)-(t : ℤ)) ≤ eps at hshort
  have hbridges := maximal_bridge_bounds_at_component_cut hn p hmax hc hk root hsize
  change ((a : ℤ)=0 → B ≤ (k : ℤ)) ∧ (1 ≤ (a : ℤ) → B ≤ (a : ℤ)+(k : ℤ)-1) at hbridges
  have hB0 : (a : ℤ)=0 → B ≤ (t : ℤ) := by rw [htk]; exact hbridges.1
  have hB1 : 1 ≤ (a : ℤ) → B ≤ (a : ℤ)+(t : ℤ)-1 := by rw [htk]; exact hbridges.2
  have hBcap : B ≤ Bcap := by
    dsimp only [Bcap]
    split_ifs with ha
    · exact hB0 ha
    · exact hB1 (by omega)
  have hp := peak_activity_bound hn p hmaj hc hk
  change peakExcess p hc ≤ 2*B+(k : ℤ)-U-(2*eps+parity-(f : ℤ)) at hp
  have hpeak : 1 ≤ 2*B+(t : ℤ)-U-(2*eps+parity-(f : ℤ)) := by omega
  have hr := normalized_peak_reserve_bound hn p hmaj hc hk root hlarge
  dsimp only at hr
  rw [component_cut_source_half_peak,component_cut_displacement_mass] at hr
  change peakExcess p hc ≤ 2*B+m-U-2-2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))-
    (a : ℤ)*(v : ℤ)-eps at hr
  have hreserve : 1 ≤ 2*B+m-U-2-2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))-
      (a : ℤ)*(v : ℤ)-eps := by omega
  have hp0 : 0 ≤ parity := by dsimp only [parity]; positivity
  have hp1 : parity ≤ 1 := by dsimp only [parity]; omega
  have pre := CoupledPeakCutoff.unpaid_prebounds m parity t f a v B U eps
    (by exact_mod_cast ht) hp0 hp1 (by positivity) (by positivity)
    (by exact_mod_cast haf) (by exact_mod_cast hv) hU hB0 hB1 hact hcredit hpeak hreserve hshort
  have hBweak : B ≤ (a : ℤ)+(t : ℤ) := by
    by_cases ha : (a : ℤ)=0
    · have hh := hB0 ha; omega
    · have hh := hB1 (by omega); omega
  have hpre : 2*eps+parity ≤ 3*(f : ℤ)+3*(t : ℤ)-2 := by omega
  have hfquad : ((f : ℤ)-3)^2 ≤ 6*(t : ℤ)+5-parity := by nlinarith only [hact,hpre]
  have hfbound : (f : ℤ) ≤ (t : ℤ)+5 := by
    by_contra hh
    have hprod := mul_nonneg (show 0 ≤ (f : ℤ)-(t : ℤ)-6 by omega)
      (show 0 ≤ (f : ℤ)+(t : ℤ) by positivity)
    nlinarith only [hfquad,hprod,hp0,sq_nonneg (t : ℤ)]
  have hcutoff := original_unpaid_peak_cutoff hn p hmaj hmax hc hk root hlarge ht hpos
  have hR := (component_area_size_bounds p hmaj root hlarge hproper).1
  change 4 ≤ (prefixSourceCore q).card at hR
  have hpart := component_cut_internal_size_partition p (by omega) root hsize
  change _+(prefixSourceCore q).card=L at hpart
  have hx : (x : ℤ) ≤ (L : ℤ)-4 := by dsimp only [x]; omega
  obtain ⟨z,hz⟩ := canonical_energy_twice p
  have hdom : (actualPeakProfile p root).Domain := by
    unfold FinitePeak.Profile.Domain
    rw [actual_peak_profile_L,actual_peak_profile_energy]
    dsimp only [actualPeakProfile]
    exact ⟨by exact_mod_cast ht,by exact_mod_cast hcutoff.1,hp0,hp1,
      by positivity,hfbound,heps,pre.1,by positivity,by exact_mod_cast haf,hU,pre.2.1,
      hmLower,by exact_mod_cast hcutoff.2.1,by exact_mod_cast hv,
      hvUpper,pre.2.2.1,by omega,by exact_mod_cast hUwidth,
      by positivity,hx⟩
  have hscalar := original_unpaid_filling_scalar_filters hn p hmaj hmax hc hk root hlarge hpos
  have hJ := original_internal_square_envelope p hmaj root hlarge hproper
  refine ⟨hdom,?_⟩
  unfold FinitePeak.Profile.Reserves
  rw [actual_peak_profile_T]
  dsimp only [actualPeakProfile,FinitePeak.Profile.A,FinitePeak.Profile.B,FinitePeak.Profile.cap]
  refine ⟨hact,hcredit,?_,hshort,hscalar.2.1,hscalar.2.2.1,hJ.1,hJ.2.1⟩
  change 1 ≤ 2*Bcap+(t : ℤ)-U-(2*eps+parity-(f : ℤ))
  omega

#print axioms actual_peak_profile_L
#print axioms actual_peak_profile_energy
#print axioms actual_peak_profile_T
#print axioms actual_peak_profile_domain_reserves
end LRX.FiniteCuts

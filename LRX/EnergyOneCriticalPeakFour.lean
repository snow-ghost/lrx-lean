module

public import LRX.ActualEnergyOneDefectBudget
public import LRX.BitonicNonshortDefect

@[expose] public section

namespace LRX.FiniteCuts
open ZeroGap RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_energy_one_two_fixed_peak_bound (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=1) (hp : n%2=0) (hf : n-p.support.card=2)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=6) :
    sourceHalfPeak p ≤ 4 ∧ (sourceHalfPeak p=4 → cycleDefect p=2) := by
  have hb := actual_energy_one_defect_peak_budget hn p hmaj hmax hc hk root hlarge ht hpos he hp 2 (by decide) hf (by simpa using hv)
  have hd := actual_energy_one_nonempty_global_defect hn p hmaj hmax hc hk root hlarge ht hpos he hp 2 (by decide) hf (by simpa using hv)
  constructor
  · omega
  · intro hU
    rw [hU] at hb
    omega

theorem energy_one_two_fixed_peak_four_rigidity (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=1) (hp : n%2=0) (hf : n-p.support.card=2)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=6)
    (hU : sourceHalfPeak p=4) :
    (componentRoots p).card=3 ∧ bridgeBudget (componentBridges p hc)=2 ∧
      peakExcess p hc=1 ∧ cycleDefect p=2 ∧
      (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
        (p.support.card : ℤ)+fillingHalfPeakSum p = -2 ∧
      fillingHalfPeakSum p=((fillingCycles p).card : ℤ) ∧
      p.cycleFactorsFinset.card=(fillingCycles p).card+4 := by
  classical
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hsize : 2 ≤ (componentSet p root).card := by omega
  have ha : (singletonSuffixComponents q L).card=0 :=
    (actual_energy_one_nonempty_shape hn p hmaj hmax hc hk root hlarge ht hpos he hp
      2 (by decide) hf (by simpa using hv)).1
  have hw := nontrivial_suffix_size_sum q L
  have hcount := component_cut_external_count p root hsize
  change 2*(nontrivialSuffixComponents q L).card ≤
    (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ) at hw
  change (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ)=6 at hv
  change 2 ≤ (nontrivialSuffixComponents q L).card at ht
  change (nontrivialSuffixComponents q L).card+1=(componentRoots p).card at hcount
  have ht2 := (original_unpaid_two_size_cutoff hn p hmaj hmax hc hk root hlarge ht hpos).1
  change (nontrivialSuffixComponents q L).card=2 at ht2
  have hroots : (componentRoots p).card=3 := by omega
  have hk2 : k=2 := by omega
  have hB := (maximal_bridge_bounds_at_component_cut hn p hmax hc hk root hsize).1
    (by change ((singletonSuffixComponents q L).card : ℤ)=0; rw [ha]; rfl)
  have hz := (actual_energy_one_two_fixed_peak_bound hn p hmaj hmax hc hk root
    hlarge ht hpos he hp hf hv).2 hU
  let C := (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
    (p.support.card : ℤ)+fillingHalfPeakSum p
  have hN := choose_two_half_identity n
  have hsizeN : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by omega
  have hprice : peakExcess p hc=2*(bridgeBudget (componentBridges p hc) : ℤ)-
      (sourceHalfPeak p : ℤ)-1-C := by
    unfold peakExcess
    dsimp only [C]
    unfold canonicalEnergyDeficit at he
    have hsupport : (p.support.card : ℤ)=(n : ℤ)-2 := by omega
    nlinarith only [he,hN,hsizeN,hsupport]
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  obtain ⟨events,hprod,hlen,_,_,hsep,_,htravel⟩ := sorting_events hd (majorized_short hd hmaj)
  have hstrong := source_packet_strong_event_cover hn p (by omega) events hprod hsep htravel
  have hF : (fun i : Fin n => (i : ℤ)+displacement p.symm i)=
      (fun i => (p.symm i : ℤ)) := by funext i; simp [displacement]
  have hI : inversionNumber p.symm=inversionNumber p := inversion_number_inverse p
  rw [hF,canonical_inversion_count,hI] at hlen
  have hS := filling_half_peak_sum_ge_count p
  have hZ : C=cycleDefect p-(p.cycleFactorsFinset.card : ℤ)+fillingHalfPeakSum p := by
    simp only [C,cycleDefect,displacement_mass_inverse]
    ring
  change _ ∧ _ ∧ _ ∧ _ ∧ C= -2 ∧ _ ∧ _
  omega

theorem actual_energy_one_two_fixed_peak_four_local_cycle_peak_one (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=1) (hp : n%2=0) (hf : n-p.support.card=2)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=6)
    (hU : sourceHalfPeak p=4)
    (A : FillingWindow n)
    (hA : A ∈ positiveSourceFamily (localTarget p 0 (componentLeft p root))
      (componentSet p root).card)
    (c : State A.size) (hcA : c ∈ A.filling.cycleFactorsFinset) : leftPeak c A.size=1 := by
  obtain ⟨_,_,_,_,_,hS,_⟩ := energy_one_two_fixed_peak_four_rigidity hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv hU
  have hpeak := filling_cycles_peak_one_of_equality p hS
  have hqpeak := filling_cycle_peak_one_recenter p root hpeak
  have hspec := positive_source_family_spec (localTarget p 0 (componentLeft p root))
    (componentSet p root).card
  exact matched_filling_window_cycle_peak_one _ A (hspec.1 A hA)
    (positive_family_avoids_source _ _ A hA) hqpeak c hcA

theorem actual_energy_one_two_fixed_peak_four_nonempty_filling_defect_four (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=1) (hp : n%2=0) (hf : n-p.support.card=2)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=6)
    (hU : sourceHalfPeak p=4)
    (A : FillingWindow n)
    (hA : A ∈ positiveSourceFamily (localTarget p 0 (componentLeft p root))
      (componentSet p root).card) (hs : 0 < A.size) :
    4 ≤ cycleDefect A.filling := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hspec := positive_source_family_spec q L
  have hm := hspec.1 A hA
  have hbound := hspec.2.2.1 A hA
  have hmin := (actual_energy_one_nonempty_shape hn p hmaj hmax hc hk root hlarge ht hpos
    he hp 2 (by decide) hf (by simpa using hv)).2
  have hphysical (i : Fin n) (hi : Contains A.window i) : 3 ≤ |displacement q.symm i| := by
    apply hmin i
    have hhi := hi.2
    change i.val < L
    omega
  have hlocal (i : Fin A.size) : 3 ≤ |displacement A.filling i| := by
    rw [← matching_window_displacement A.window q.symm A.filling hm i]
    exact hphysical _ (contains_embed A.window i)
  letI : NeZero A.size := ⟨by omega⟩
  have hfull : A.filling.support=Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    apply Equiv.Perm.mem_support.mpr
    intro hi
    have hh := hlocal i
    simp only [displacement,hi,sub_self,abs_zero] at hh
    omega
  exact full_support_peak_one_nonshort_defect_ge_four A.filling hfull hlocal
    (fun c hcA => le_of_eq (actual_energy_one_two_fixed_peak_four_local_cycle_peak_one hn p hmaj hmax hc hk root
      hlarge ht hpos he hp hf hv hU A hA c hcA))

theorem actual_energy_one_two_fixed_peak_four_filling_size_zero (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=1) (hp : n%2=0) (hf : n-p.support.card=2)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=6)
    (hU : sourceHalfPeak p=4)
    (A : FillingWindow n)
    (hA : A ∈ positiveSourceFamily (localTarget p 0 (componentLeft p root))
      (componentSet p root).card) : A.size=0 := by
  by_contra hsize
  have hfour := actual_energy_one_two_fixed_peak_four_nonempty_filling_defect_four hn p hmaj hmax hc hk root
    hlarge ht hpos he hp hf hv hU A hA (by omega)
  let q := localTarget p 0 (componentLeft p root)
  have hm := (positive_source_family_spec q (componentSet p root).card).1 A hA
  have hle := matching_window_defect_le A q.symm hm
  rw [cycle_defect_inverse] at hle
  have hq : cycleDefect q=cycleDefect p := component_cut_cycle_defect p root
  rw [hq] at hle
  have hz := (actual_energy_one_two_fixed_peak_bound hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv).2 hU
  omega

theorem actual_energy_one_two_fixed_peak_four_no_prefix_holes (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=1) (hp : n%2=0) (hf : n-p.support.card=2)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=6)
    (hU : sourceHalfPeak p=4)
 :
    (componentSet p root).card-(prefixSourceCore (localTarget p 0 (componentLeft p root))).card=0 := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hzero : ∀ A ∈ positiveSourceFamily q L, A.size=0 :=
    fun A hA => actual_energy_one_two_fixed_peak_four_filling_size_zero hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv hU A hA
  have hsum : ((positiveSourceFamily q L).map (fun A => A.size)).sum=0 := by
    have hh : (positiveSourceFamily q L).map (fun A => A.size)=
        (positiveSourceFamily q L).map (fun _ => (0 : ℕ)) :=
      List.map_congr_left hzero
    rw [hh]
    simp
  have hpart := component_cut_internal_size_partition p (by omega) root (by omega)
  change ((positiveSourceFamily q L).map (fun A => A.size)).sum+(prefixSourceCore q).card=L at hpart
  change L-(prefixSourceCore q).card=0
  omega

#print axioms actual_energy_one_two_fixed_peak_bound
#print axioms energy_one_two_fixed_peak_four_rigidity
#print axioms actual_energy_one_two_fixed_peak_four_local_cycle_peak_one
#print axioms actual_energy_one_two_fixed_peak_four_nonempty_filling_defect_four
#print axioms actual_energy_one_two_fixed_peak_four_filling_size_zero
#print axioms actual_energy_one_two_fixed_peak_four_no_prefix_holes
end LRX.FiniteCuts

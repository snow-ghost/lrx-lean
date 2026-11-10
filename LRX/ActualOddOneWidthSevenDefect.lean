import LRX.MatchingWindowDefect
import LRX.OddOneWidthSevenCertificate
import LRX.ActualNonunitComponentDefect
import LRX.OriginalShallowExteriorDeficit

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords FiniteWindow
variable {n k : ℕ} [NeZero n]

theorem actual_odd_one_width_seven_no_isolated (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=7) :
    (singletonSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card=0 := by
  obtain ⟨A,B,_,_,_,_,hmem⟩ :=
    actual_unpaid_filtered_exterior_pair hn p hmaj hmax hc hk root hlarge ht hpos
  rw [hp,he,hf,hv] at hmem
  norm_num only [Nat.cast_one] at hmem
  have hinfo := (filtered_catalogue_mem_iff _ _ _ _ _ _ _).mp hmem
  have ha := hinfo.2.2.1.2
  by_contra hzero
  have hone : (singletonSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card=1 := by omega
  rw [hone,odd_one_seven_isolated_empty] at hmem
  simp only [List.not_mem_nil] at hmem

theorem actual_odd_one_width_seven_global_defect (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=7) :
    2 ≤ cycleDefect p := by
  let q := localTarget p 0 (componentLeft p root)
  have hzero : (componentSet q 0).card=(componentSet p root).card := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have hh' : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← hh'] at hh
  have hmin := actual_odd_one_width_seven_large_min_arrow hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv
  obtain ⟨A,_,_,hm,hdef⟩ := exists_nonunit_component_defect q 0 (by omega)
    (fun i hi => by
      have hi' := (zero_component_prefix q i).mp hi
      rw [hzero] at hi'
      have h := hmin i hi'
      change 3 ≤ |displacement q.symm i| at h
      omega)
  have hle := matching_window_defect_le A q.symm hm
  rw [cycle_defect_inverse] at hle
  have hq : cycleDefect q=cycleDefect p := component_cut_cycle_defect p root
  rw [hq] at hle
  change 2 ≤ cycleDefect A.filling at hdef
  omega

theorem actual_odd_one_width_seven_defect_peak_budget (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=7) :
    cycleDefect p+2*(sourceHalfPeak p : ℤ) ≤ 10 := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hsize : 2 ≤ (componentSet p root).card := by omega
  have ha : (singletonSuffixComponents q L).card=0 :=
    actual_odd_one_width_seven_no_isolated hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv
  have hw := nontrivial_suffix_size_sum q L
  have hcount := component_cut_external_count p root hsize
  change 2*(nontrivialSuffixComponents q L).card ≤
    (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ) at hw
  change (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ)=7 at hv
  change 2 ≤ (nontrivialSuffixComponents q L).card at ht
  change (nontrivialSuffixComponents q L).card+1=(componentRoots p).card at hcount
  have ht2 := (original_unpaid_two_size_cutoff hn p hmaj hmax hc hk root hlarge ht hpos).1
  change (nontrivialSuffixComponents q L).card=2 at ht2
  have hk2 : k=2 := by omega
  have hB := (maximal_bridge_bounds_at_component_cut hn p hmax hc hk root hsize).1
    (by change ((singletonSuffixComponents q L).card : ℤ)=0; rw [ha]; rfl)
  have hdef := actual_odd_one_width_seven_global_defect hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv
  let C := (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
    (p.support.card : ℤ)+fillingHalfPeakSum p
  have hs := aggregate_source_filling_strong_defect hn p hmaj (by omega)
  dsimp only at hs
  rw [hc,hk2] at hs
  norm_num only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] at hs
  have hs' : cycleDefect p-6 ≤ 2*C := by
    simpa only [cycleDefect,displacement_mass_inverse,C,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hs
  have hC : -2 ≤ C := by omega
  have hN := choose_two_half_identity n
  have hsizeN : (n : ℤ)=2*((n/2 : ℕ) : ℤ)+1 := by omega
  have hprice : peakExcess p hc=2*(bridgeBudget (componentBridges p hc) : ℤ)-
      (sourceHalfPeak p : ℤ)-1-C := by
    unfold peakExcess
    dsimp only [C]
    unfold canonicalEnergyDeficit at he
    have hsupport : (p.support.card : ℤ)=(n : ℤ)-1 := by omega
    nlinarith only [he,hN,hsizeN,hsupport]
  omega

theorem actual_odd_one_width_seven_peak_le_four (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=7) :
    sourceHalfPeak p ≤ 4 ∧ (sourceHalfPeak p=4 → cycleDefect p=2) := by
  have hb := actual_odd_one_width_seven_defect_peak_budget hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv
  have hd := actual_odd_one_width_seven_global_defect hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv
  constructor
  · omega
  · intro hU
    rw [hU] at hb
    omega

#print axioms actual_odd_one_width_seven_no_isolated

#print axioms actual_odd_one_width_seven_defect_peak_budget
#print axioms actual_odd_one_width_seven_peak_le_four

#print axioms actual_odd_one_width_seven_global_defect
end LRX.FiniteCuts

module

public import LRX.MatchingWindowDefect
public import LRX.ActualLargeComponentNoTwo
public import LRX.OriginalShallowExteriorDeficit

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords FiniteWindow
variable {n k : ℕ} [NeZero n]

theorem actual_zero_width_four_global_defect (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4) :
    2 ≤ cycleDefect p := by
  let q := localTarget p 0 (componentLeft p root)
  have hzero : (componentSet q 0).card=(componentSet p root).card := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have hh' : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← hh'] at hh
  have hmin := actual_zero_width_four_large_min_arrow hn p hmaj hmax hc hk root hlarge ht hpos he hp hv
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

theorem actual_zero_width_four_defect_peak_budget (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4) :
    cycleDefect p+2*(sourceHalfPeak p : ℤ) ≤ 10 := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hsize : 2 ≤ (componentSet p root).card := by omega
  have hf := zero_energy_even_full_support p hmaj he hp
  have hfixed := component_cut_filling_fixed_partition p (by omega) root hsize
  have ha : (singletonSuffixComponents q L).card=0 := by
    change _+_+(singletonSuffixComponents q L).card=n-p.support.card at hfixed
    omega
  have hw := nontrivial_suffix_size_sum q L
  have hcount := component_cut_external_count p root hsize
  change 2*(nontrivialSuffixComponents q L).card ≤
    (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ) at hw
  change (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ)=4 at hv
  change 2 ≤ (nontrivialSuffixComponents q L).card at ht
  change (nontrivialSuffixComponents q L).card+1=(componentRoots p).card at hcount
  have hk2 : k=2 := by omega
  have hB := (maximal_bridge_bounds_at_component_cut hn p hmax hc hk root hsize).1
    (by change ((singletonSuffixComponents q L).card : ℤ)=0; rw [ha]; rfl)
  have hdef := actual_zero_width_four_global_defect hn p hmaj hmax hc hk root hlarge ht hpos he hp hv
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
  have hsizeN : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by omega
  have hprice : peakExcess p hc=2*(bridgeBudget (componentBridges p hc) : ℤ)-
      (sourceHalfPeak p : ℤ)-1-C := by
    unfold peakExcess
    dsimp only [C]
    unfold canonicalEnergyDeficit at he
    rw [hf]
    nlinarith only [he,hN,hsizeN]
  omega

theorem actual_zero_width_four_peak_le_four (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4) :
    sourceHalfPeak p ≤ 4 ∧ (sourceHalfPeak p=4 → cycleDefect p=2) := by
  have hb := actual_zero_width_four_defect_peak_budget hn p hmaj hmax hc hk root hlarge ht hpos he hp hv
  have hd := actual_zero_width_four_global_defect hn p hmaj hmax hc hk root hlarge ht hpos he hp hv
  constructor
  · omega
  · intro hU
    rw [hU] at hb
    omega

theorem zero_width_four_high_peak_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (hU : 5 ≤ sourceHalfPeak p) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      w.length ≤ n.choose 2 := by
  rcases original_cut_sharp_or_two_arc hn p hmaj hc hk root hlarge ht start finish with h | h
  · exact h
  · apply joined_peak_word_of_nonpositive_excess (by omega) p hc hk start finish h.1 h.2
    by_contra hpos
    have hbound := actual_zero_width_four_peak_le_four (by omega) p hmaj hmax hc hk root
      hlarge ht (by omega) he hp hv
    have hfour := hbound.1
    omega

#print axioms zero_width_four_high_peak_sharp_word

#print axioms actual_zero_width_four_defect_peak_budget
#print axioms actual_zero_width_four_peak_le_four

#print axioms actual_zero_width_four_global_defect
end LRX.FiniteCuts

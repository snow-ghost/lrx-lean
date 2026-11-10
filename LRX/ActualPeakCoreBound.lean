module

public import LRX.ActualPeakProfileFilters
public import LRX.ActualPeakSupportBound
public import LRX.PeakProfileFour

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n k : ℕ} [NeZero n]

/-- The support estimate uses the same source core and holes as the profile. -/
theorem actual_unpaid_peak_core_bound (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc) :
    (actualPeakProfile p root).CoreBound := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let R := (prefixSourceCore q).card
  let a := (singletonSuffixComponents q L).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
  have hzero : (componentSet q 0).card=L := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have he : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← he] at hh
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hproper : L<n := component_card_lt_of_multiple_roots p (by omega) root
  have hdom := (actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos).1
  have heps := hdom.2.2.2.2.2.2.2.1
  have hbound := actual_peak_support_bound q hqm (by omega) (by omega) (by simpa only [hzero] using ht)
  have heps' : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement q.symm i|) ≤
      3*((nontrivialSuffixComponents q (componentSet q 0).card).card : ℤ)+6 := by
    rw [hzero]
    dsimp only [q]
    rw [component_cut_displacement_mass]
    exact heps
  have hsupport := hbound heps'
  rw [hzero] at hsupport
  have hpeak : sourceHalfPeak q=sourceHalfPeak p := component_cut_source_half_peak p root
  rw [hpeak] at hsupport
  change (R : ℤ)+(a : ℤ) ≤ 8*(sourceHalfPeak p : ℤ)+1-(n%2 : ℕ) at hsupport
  have htail := suffix_component_parameter_sum q L (by omega) (component_recenter_cut p root).1
  change v+a=n-L at htail
  have hsize := component_cut_internal_size_partition p (by omega) root (by omega)
  change ((positiveSourceFamily q L).map (fun A => A.size)).sum+R=L at hsize
  change 2*((n/2 : ℕ) : ℤ)+2*((n%2 : ℕ) : ℤ)-(v : ℤ)-8*(sourceHalfPeak p : ℤ)-1 ≤
    ((L-R : ℕ) : ℤ)
  omega

#print axioms actual_unpaid_peak_core_bound
end LRX.FiniteCuts

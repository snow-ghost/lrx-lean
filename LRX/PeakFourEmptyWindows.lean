module

public import LRX.BitonicNonshortDefect
public import LRX.ActualNonshortFillings

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_peak_four_filling_size_zero (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (hU : sourceHalfPeak p=4)
    (A : FillingWindow n)
    (hA : A ∈ positiveSourceFamily (localTarget p 0 (componentLeft p root))
      (componentSet p root).card) : A.size=0 := by
  by_contra hsize
  have hfour := actual_peak_four_nonempty_filling_defect_four hn p hmaj hmax hc hk root
    hlarge ht hpos he hp hv hU A hA (by omega)
  let q := localTarget p 0 (componentLeft p root)
  have hm := (positive_source_family_spec q (componentSet p root).card).1 A hA
  have hle := matching_window_defect_le A q.symm hm
  rw [cycle_defect_inverse] at hle
  have hq : cycleDefect q=cycleDefect p := component_cut_cycle_defect p root
  rw [hq] at hle
  have hz := (actual_zero_width_four_peak_le_four hn p hmaj hmax hc hk root hlarge ht hpos he hp hv).2 hU
  omega

theorem actual_peak_four_no_prefix_holes (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (hU : sourceHalfPeak p=4)
 :
    (componentSet p root).card-(prefixSourceCore (localTarget p 0 (componentLeft p root))).card=0 := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hzero : ∀ A ∈ positiveSourceFamily q L, A.size=0 :=
    fun A hA => actual_peak_four_filling_size_zero hn p hmaj hmax hc hk root hlarge ht hpos he hp hv hU A hA
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

#print axioms actual_peak_four_filling_size_zero
#print axioms actual_peak_four_no_prefix_holes
end LRX.FiniteCuts

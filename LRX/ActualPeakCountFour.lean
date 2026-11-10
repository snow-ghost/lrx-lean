import LRX.PeakProfileFive
import LRX.UnpaidPrecisePeakCutoff
import LRX.ActualPeakProfileFilters
import LRX.MaximalCutManyRouting
import LRX.PeakProfileLargeCount

namespace LRX.FiniteCuts
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- Both the count and the size now use the precise per-count cutoff. -/
theorem original_unpaid_count_four_size_cutoff (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc) :
    (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card ≤ 4 ∧ n/2 ≤ 223 ∧ n ≤ 447 := by
  let r := actualPeakProfile p root
  have hr : r.Admissible := actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos
  have hprecise := original_unpaid_precise_peak_cutoff hn p hmaj hmax hc hk root hlarge ht hpos
  change r.m < CoupledPeakCutoff.cutoff r.t at hprecise
  obtain ⟨ht4,hm223,_⟩ := FinitePeak.Profile.precise_admissible_count_size r hr hprecise
  change ((nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
    (componentSet p root).card).card : ℤ) ≤ 4 at ht4
  change ((n/2 : ℕ) : ℤ) ≤ 223 at hm223
  omega

#print axioms original_unpaid_count_four_size_cutoff
end LRX.FiniteCuts

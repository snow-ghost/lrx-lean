import LRX.ActualPeakCountFour
import LRX.ActualPeakCoreBound

namespace LRX.FiniteCuts
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- The actual core estimate removes the last count t=4. -/
theorem original_unpaid_count_three_size_cutoff (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc) :
    (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card ≤ 3 ∧ n/2 ≤ 223 ∧ n ≤ 447 := by
  obtain ⟨ht4,hm,hn447⟩ := original_unpaid_count_four_size_cutoff hn p hmaj hmax hc hk root hlarge ht hpos
  have hne := FinitePeak.Profile.admissible_count_ne_four _
    (actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos)
    (actual_unpaid_peak_core_bound hn p hmaj hmax hc hk root hlarge ht hpos)
  change ((nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card : ℤ) ≠ 4 at hne
  omega

#print axioms original_unpaid_count_three_size_cutoff
end LRX.FiniteCuts

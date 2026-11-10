module

public import LRX.OriginalPrecisePeakCutoff
public import LRX.PeakActivityBound

@[expose] public section

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem original_unpaid_precise_peak_cutoff (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (hpos : 1 ≤ peakExcess p hc) :
    ((n/2 : ℕ) : ℤ) < CoupledPeakCutoff.cutoff
      ((nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card : ℤ) := by
  apply original_precise_peak_cutoff_of_first_C8 hn p hmaj hmax hc hk root hlarge ht hpos
  dsimp only
  rw [component_cut_source_half_peak,component_cut_displacement_mass]
  have hs : (localTarget p 0 (componentLeft p root)).support.card=p.support.card := by
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  rw [hs]
  have hsize : 2 ≤ (componentSet p root).card := by omega
  have hcount := component_cut_external_count p root hsize
  have htcount : (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card=k := by omega
  rw [htcount]
  exact peak_activity_bound hn p hmaj hc hk


#print axioms original_unpaid_precise_peak_cutoff
end LRX.FiniteCuts

module

public import LRX.ThreeOuterEnergyExclusion
public import LRX.ExternalExactEnergyFilter
public import LRX.ActualPeakCountThree

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- Only two exterior nontrivial components can remain unpaid in M4. -/
theorem original_unpaid_many_two_cutoff (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc) :
    (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card=2 ∧ n/2 ≤ 199 ∧ n ≤ 399 := by
  have hb := original_unpaid_count_three_size_cutoff hn p hmaj hmax hc hk root hlarge ht hpos
  have hne : (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card ≠ 3 := by
    intro hthree
    let r := actualPeakProfile p root
    have hrt : r.t=3 := by change ((_ : ℕ) : ℤ)=3; exact_mod_cast hthree
    have hr := actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos
    have hcore := actual_unpaid_peak_core_bound hn p hmaj hmax hc hk root hlarge ht hpos
    have hout := FinitePeak.admissible_three_outer r hr hcore hrt
    have he := actual_peak_external_energy_filter p hmaj root
    change r.exterior^2 ≤ 4*r.eps+r.parity+2*(r.E2-r.exterior%2) at he
    unfold FinitePeak.Profile.E2 at he
    rw [hrt] at he
    apply FinitePeak.three_outer_energy_impossible _ _ _ _ _ _ hout
    nlinarith only [he]
  have ht2 : (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card=2 := by omega
  have hcut := original_unpaid_precise_peak_cutoff hn p hmaj hmax hc hk root hlarge ht hpos
  rw [ht2] at hcut
  norm_num [CoupledPeakCutoff.cutoff] at hcut
  exact ⟨ht2,by omega,by omega⟩

#print axioms original_unpaid_many_two_cutoff
end LRX.FiniteCuts

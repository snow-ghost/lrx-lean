import LRX.EnergyOneOuterCases
import LRX.ActualTwoSizeCutoff
import LRX.SignedSelectionDeficit

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_energy_one_mem_cases (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=1) :
    let r := actualPeakProfile p root
    (r.parity,r.fixed,r.eps,r.isolated,r.peak,r.exterior) ∈ FinitePeak.energyOneOuterRows := by
  let r := actualPeakProfile p root
  have hb := original_unpaid_two_size_cutoff hn p hmaj hmax hc hk root hlarge ht hpos
  have hr := actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos
  have hcore := actual_unpaid_peak_core_bound hn p hmaj hmax hc hk root hlarge ht hpos
  have hext := actual_peak_external_energy_filter p hmaj root
  have ht2 : r.t=2 := by change ((_ : ℕ) : ℤ)=2; exact_mod_cast hb.1
  have hm : r.m ≤ 36 := by change ((n/2 : ℕ) : ℤ) ≤ 36; exact_mod_cast hb.2.1
  have hv : r.exterior ≤ 7 := by change ((_ : ℕ) : ℤ) ≤ 7; exact_mod_cast hb.2.2.2
  have hdom := hr.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hholes⟩ := hdom
  have hx : r.holes ≤ 69 := by
    rw [actual_peak_profile_L] at hholes
    have hLn : (componentSet p root).card ≤ n := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (componentSet p root)
    have hn73 := hb.2.2.1
    change r.holes ≤ ((_ : ℕ) : ℤ)-4 at hholes
    omega
  exact FinitePeak.energy_one_profile_mem_cases r hr hcore ht2 hext
    (Int.natCast_nonneg _) hm (Int.natCast_nonneg _) hx he hv

#print axioms actual_energy_one_mem_cases
end LRX.FiniteCuts

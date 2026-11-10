module

public import LRX.PeakFourScalarSizes
public import LRX.PeakFourEmptyWindows

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_peak_four_sizes (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (hU : sourceHalfPeak p=4)
 : n=16 ∨ n=20 := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let r := actualPeakProfile p root
  have hsize : 2 ≤ L := by dsimp only [L]; omega
  have hrig := peak_four_source_rigidity hn p hmaj hmax hc hk root hlarge ht hpos he hp hv hU
  have hcount := component_cut_external_count p root hsize
  have ht2 : (nontrivialSuffixComponents q L).card=2 := by
    change (nontrivialSuffixComponents q L).card+1=(componentRoots p).card at hcount
    have hh := hrig.1
    omega
  have hf := zero_energy_even_full_support p hmaj he hp
  have hfixed := component_cut_filling_fixed_partition p (by omega) root hsize
  have ha : (singletonSuffixComponents q L).card=0 := by
    change _+_+(singletonSuffixComponents q L).card=n-p.support.card at hfixed
    omega
  have hx := actual_peak_four_no_prefix_holes hn p hmaj hmax hc hk root hlarge ht hpos he hp hv hU
  have hr := actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos
  have ht' : r.t=2 := by change ((_ : ℕ) : ℤ)=2; exact_mod_cast ht2
  have hp' : r.parity=0 := by change ((n%2 : ℕ) : ℤ)=0; rw [hp]; rfl
  have hf' : r.fixed=0 := by change ((n-p.support.card : ℕ) : ℤ)=0; rw [hf]; simp
  have he' : r.eps=0 := he
  have ha' : r.isolated=0 := by change (((singletonSuffixComponents q L).card : ℕ) : ℤ)=0; rw [ha]; rfl
  have hU' : r.peak=4 := by change ((sourceHalfPeak p : ℕ) : ℤ)=4; rw [hU]; rfl
  have hv' : r.exterior=4 := by change ((_ : ℕ) : ℤ)=4; exact_mod_cast hv
  have hx' : r.holes=0 := by change ((_ : ℕ) : ℤ)=0; rw [hx]; rfl
  have hh := FinitePeak.peak_four_zero_holes_sizes r hr ht' hp' hf' he' ha' hU' hv' hx'
  change ((n/2 : ℕ) : ℤ)=8 ∨ ((n/2 : ℕ) : ℤ)=10 at hh
  omega

#print axioms actual_peak_four_sizes
end LRX.FiniteCuts

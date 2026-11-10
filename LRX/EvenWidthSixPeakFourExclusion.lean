module

public import LRX.EvenWidthSixPeakFour
public import LRX.FinitePeakProfile

@[expose] public section

namespace LRX.FinitePeak

theorem even_six_peak_four_zero_holes_impossible (r : Profile) (hr : r.Admissible)
    (ht : r.t=2) (hp : r.parity=0) (hf : r.fixed=0) (he : r.eps=0)
    (ha : r.isolated=0) (hU : r.peak=4) (hv : r.exterior=6) (hx : r.holes=0) : False := by
  obtain ⟨_,hres,hfilters⟩ := hr
  obtain ⟨_,_,_,_,hT,_,_,_⟩ := hres
  have henergy := hfilters.1
  norm_num [Profile.T,Profile.B,Profile.M,ht,hp,hf,he,ha,hU,hv] at hT
  have hm : 2 ≤ r.m := by omega
  norm_num [Profile.need,Profile.energy,Profile.L,Profile.n,Profile.E2,
    Profile.J,Profile.cap,ht,hp,hf,he,ha,hU,hv,hx] at henergy
  rw [if_pos hm] at henergy
  nlinarith [sq_nonneg (r.m-8)]

#print axioms even_six_peak_four_zero_holes_impossible
end LRX.FinitePeak

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_even_six_peak_four_impossible (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=6)
    (hU : sourceHalfPeak p=4)
 : False := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let r := actualPeakProfile p root
  have hsize : 2 ≤ L := by dsimp only [L]; omega
  have hrig := even_width_six_peak_four_rigidity hn p hmaj hmax hc hk root hlarge ht hpos he hp hv hU
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
  have hx := actual_even_six_peak_four_no_prefix_holes hn p hmaj hmax hc hk root hlarge ht hpos he hp hv hU
  have hr := actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos
  have ht' : r.t=2 := by change ((_ : ℕ) : ℤ)=2; exact_mod_cast ht2
  have hp' : r.parity=0 := by change ((n%2 : ℕ) : ℤ)=0; rw [hp]; rfl
  have hf' : r.fixed=0 := by change ((n-p.support.card : ℕ) : ℤ)=0; rw [hf]; simp
  have he' : r.eps=0 := he
  have ha' : r.isolated=0 := by change (((singletonSuffixComponents q L).card : ℕ) : ℤ)=0; rw [ha]; rfl
  have hU' : r.peak=4 := by change ((sourceHalfPeak p : ℕ) : ℤ)=4; rw [hU]; rfl
  have hv' : r.exterior=6 := by change ((_ : ℕ) : ℤ)=6; exact_mod_cast hv
  have hx' : r.holes=0 := by change ((_ : ℕ) : ℤ)=0; rw [hx]; rfl
  exact FinitePeak.even_six_peak_four_zero_holes_impossible r hr ht' hp' hf' he' ha' hU' hv' hx'

#print axioms actual_even_six_peak_four_impossible
end LRX.FiniteCuts

import LRX.OddWidthFivePeakFour
import LRX.FinitePeakProfile

namespace LRX.FinitePeak

theorem odd_five_peak_four_zero_holes_impossible (r : Profile) (hr : r.Admissible)
    (ht : r.t=2) (hp : r.parity=1) (hf : r.fixed=1) (he : r.eps=0)
    (ha : r.isolated=0) (hU : r.peak=4) (hv : r.exterior=5) (hx : r.holes=0) : False := by
  obtain ⟨_,hres,hfilters⟩ := hr
  obtain ⟨_,_,_,_,hT,_,_,_⟩ := hres
  have henergy := hfilters.1
  norm_num [Profile.T,Profile.B,Profile.M,ht,hp,hf,he,ha,hU,hv] at hT
  have hm : 1 ≤ r.m := by omega
  norm_num [Profile.need,Profile.energy,Profile.L,Profile.n,Profile.E2,
    Profile.J,Profile.cap,ht,hp,hf,he,ha,hU,hv,hx] at henergy
  rw [if_pos (show 2 ≤ r.m+1 by omega)] at henergy
  nlinarith [sq_nonneg (2*r.m-15)]

#print axioms odd_five_peak_four_zero_holes_impossible
end LRX.FinitePeak

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_odd_five_peak_four_impossible (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=5)
    (hU : sourceHalfPeak p=4)
 : False := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let r := actualPeakProfile p root
  have hsize : 2 ≤ L := by dsimp only [L]; omega
  have hrig := odd_width_five_peak_four_rigidity hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv hU
  have hcount := component_cut_external_count p root hsize
  have ht2 : (nontrivialSuffixComponents q L).card=2 := by
    change (nontrivialSuffixComponents q L).card+1=(componentRoots p).card at hcount
    have hh := hrig.1
    omega
  have ha : (singletonSuffixComponents q L).card=0 :=
    (actual_unpaid_odd_width_five_pair hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv).1
  have hx := actual_odd_five_peak_four_no_prefix_holes hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv hU
  have hr := actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos
  have ht' : r.t=2 := by change ((_ : ℕ) : ℤ)=2; exact_mod_cast ht2
  have hp' : r.parity=1 := by change ((n%2 : ℕ) : ℤ)=1; rw [hp]; rfl
  have hf' : r.fixed=1 := by change ((n-p.support.card : ℕ) : ℤ)=1; rw [hf]; simp
  have he' : r.eps=0 := he
  have ha' : r.isolated=0 := by change (((singletonSuffixComponents q L).card : ℕ) : ℤ)=0; rw [ha]; rfl
  have hU' : r.peak=4 := by change ((sourceHalfPeak p : ℕ) : ℤ)=4; rw [hU]; rfl
  have hv' : r.exterior=5 := by change ((_ : ℕ) : ℤ)=5; exact_mod_cast hv
  have hx' : r.holes=0 := by change ((_ : ℕ) : ℤ)=0; rw [hx]; rfl
  exact FinitePeak.odd_five_peak_four_zero_holes_impossible r hr ht' hp' hf' he' ha' hU' hv' hx'

#print axioms actual_odd_five_peak_four_impossible
end LRX.FiniteCuts

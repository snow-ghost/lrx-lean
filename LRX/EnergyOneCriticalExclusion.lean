import LRX.EnergyOneCriticalPeakFour
import LRX.FinitePeakProfile

namespace LRX.FinitePeak

theorem energy_one_critical_zero_holes_impossible (r : Profile) (hr : r.Admissible)
    (ht : r.t=2) (hp : r.parity=0) (hf : r.fixed=2) (he : r.eps=1)
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

#print axioms energy_one_critical_zero_holes_impossible
end LRX.FinitePeak

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_energy_one_critical_impossible (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=1) (hp : n%2=0) (hf : n-p.support.card=2)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=6)
    (hU : sourceHalfPeak p=4)
 : False := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let r := actualPeakProfile p root
  have hsize : 2 ≤ L := by dsimp only [L]; omega
  have hrig := energy_one_two_fixed_peak_four_rigidity hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv hU
  have hcount := component_cut_external_count p root hsize
  have ht2 : (nontrivialSuffixComponents q L).card=2 := by
    change (nontrivialSuffixComponents q L).card+1=(componentRoots p).card at hcount
    have hh := hrig.1
    omega
  have ha : (singletonSuffixComponents q L).card=0 :=
    (actual_energy_one_nonempty_shape hn p hmaj hmax hc hk root hlarge ht hpos he hp
      2 (by decide) hf (by simpa using hv)).1
  have hx := actual_energy_one_two_fixed_peak_four_no_prefix_holes hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv hU
  have hr := actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos
  have ht' : r.t=2 := by change ((_ : ℕ) : ℤ)=2; exact_mod_cast ht2
  have hp' : r.parity=0 := by change ((n%2 : ℕ) : ℤ)=0; rw [hp]; rfl
  have hf' : r.fixed=2 := by change ((n-p.support.card : ℕ) : ℤ)=2; rw [hf]; simp
  have he' : r.eps=1 := he
  have ha' : r.isolated=0 := by change (((singletonSuffixComponents q L).card : ℕ) : ℤ)=0; rw [ha]; rfl
  have hU' : r.peak=4 := by change ((sourceHalfPeak p : ℕ) : ℤ)=4; rw [hU]; rfl
  have hv' : r.exterior=6 := by change ((_ : ℕ) : ℤ)=6; exact_mod_cast hv
  have hx' : r.holes=0 := by change ((_ : ℕ) : ℤ)=0; rw [hx]; rfl
  exact FinitePeak.energy_one_critical_zero_holes_impossible r hr ht' hp' hf' he' ha' hU' hv' hx'

#print axioms actual_energy_one_critical_impossible
end LRX.FiniteCuts

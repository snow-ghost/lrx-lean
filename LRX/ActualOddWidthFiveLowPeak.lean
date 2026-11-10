module

public import LRX.OddWidthFiveLowExclusion
public import LRX.ActualOddWidthFiveFillings

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_odd_width_five_low_peak_impossible (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=5)
    (hU : sourceHalfPeak p ≤ 3)
 : False := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let x := L-(prefixSourceCore q).card
  have hbase := original_unpaid_two_size_cutoff hn p hmaj hmax hc hk root hlarge ht hpos
  have ht2 : (nontrivialSuffixComponents q L).card=2 := hbase.1
  have ha : (singletonSuffixComponents q L).card=0 :=
    (actual_unpaid_odd_width_five_pair hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv).1
  have hr := actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos
  have hdom := hr.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hholes⟩ := hdom
  change (x : ℤ) ≤ (actualPeakProfile p root).L-4 at hholes
  rw [actual_peak_profile_L] at hholes
  have hLn : L ≤ n := by simpa only [L,Fintype.card_fin] using Finset.card_le_univ (componentSet p root)
  have htail := suffix_component_parameter_sum q L hLn (component_recenter_cut p root).1
  change (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ)+(singletonSuffixComponents q L).card=n-L at htail
  change (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ)=5 at hv
  rw [hv,ha] at htail
  have hxSmall : x < 65 := by
    change (x : ℤ) ≤ (L : ℤ)-4 at hholes
    have hn73 := hbase.2.2.1
    omega
  dsimp only [q,L] at ht2 ha hv
  have heq : FinitePeak.oddFiveLowProfile (n/2) (sourceHalfPeak p) x=actualPeakProfile p root := by
    have he' : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-
        (∑ i, |displacement p.symm i|)=0 := he
    simp only [FinitePeak.oddFiveLowProfile,actualPeakProfile,ht2,hp,hf,ha,hv,he',
      Nat.sub_self,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,x,L,q]
  have hstrict : (actualPeakProfile p root).holes=0 ∨
      (actualPeakProfile p root).holes ≤ 2*(actualPeakProfile p root).T-5 := by
    by_cases hx : x=0
    · left
      change (x : ℤ)=0
      rw [hx]; rfl
    · right
      rw [actual_peak_profile_T]
      exact actual_odd_width_five_stronger_width_reserve hn p hmaj hmax hc hk root
        hlarge ht hpos he hp hf hv (by change 0 < x; omega)
  have hcheck := FinitePeak.odd_five_low_peak_check
    ⟨n/2,by have hh := hbase.2.1; omega⟩ ⟨sourceHalfPeak p,by omega⟩ ⟨x,hxSmall⟩
  change ¬((FinitePeak.oddFiveLowProfile (n/2) (sourceHalfPeak p) x).Admissible ∧
    ((FinitePeak.oddFiveLowProfile (n/2) (sourceHalfPeak p) x).holes=0 ∨
     (FinitePeak.oddFiveLowProfile (n/2) (sourceHalfPeak p) x).holes ≤
       2*(FinitePeak.oddFiveLowProfile (n/2) (sourceHalfPeak p) x).T-5)) at hcheck
  rw [heq] at hcheck
  exact hcheck ⟨hr,hstrict⟩

#print axioms actual_odd_width_five_low_peak_impossible
end LRX.FiniteCuts

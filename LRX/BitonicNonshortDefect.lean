import LRX.BitonicComponentLoad
import LRX.ActualPeakFourLocalCyclePeaks

namespace LRX.FiniteCuts
open ZeroGap FiniteWindow RotationWords
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- D3: unit cycle peaks and no arrows of length one or two force defect
at least four. The interval component and cycle budget are derived. -/
theorem full_support_peak_one_nonshort_defect_ge_four (p : State n)
    (hfull : p.support=Finset.univ) (hmin : ∀ i, 3 ≤ |displacement p i|)
    (hpeak : ∀ c ∈ p.cycleFactorsFinset, leftPeak c n ≤ 1) : 4 ≤ cycleDefect p := by
  classical
  obtain ⟨events,hprod,hlen,ha,hl,hs,_⟩ := linear_sorting_events p
  have hne : p.support.Nonempty := by rw [hfull]; exact ⟨0,Finset.mem_univ _⟩
  have hint : CarrierInterval p.support Finset.univ := by
    rw [hfull]
    exact ⟨Finset.Subset.refl _,fun _ _ _ _ _ hz _ _ => hz⟩
  obtain ⟨root,_,_,hinterval⟩ := exists_interval_event_component events p hprod ha hl hs hne hint
  have hthree := nonshort_interval_three_cycles events p hprod root hinterval (fun i _ => hmin i) hpeak
  have hbudget := component_cycle_defect_budget events p hprod root
  rw [displacement_mass_inverse] at hlen
  unfold cycleDefect
  omega

theorem actual_peak_four_nonempty_filling_defect_four (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (hU : sourceHalfPeak p=4)
    (A : FillingWindow n)
    (hA : A ∈ positiveSourceFamily (localTarget p 0 (componentLeft p root))
      (componentSet p root).card) (hs : 0 < A.size) :
    4 ≤ cycleDefect A.filling := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hspec := positive_source_family_spec q L
  have hm := hspec.1 A hA
  have hbound := hspec.2.2.1 A hA
  have hmin := actual_zero_width_four_large_min_arrow hn p hmaj hmax hc hk root hlarge ht hpos he hp hv
  have hphysical (i : Fin n) (hi : Contains A.window i) : 3 ≤ |displacement q.symm i| := by
    apply hmin i
    have hhi := hi.2
    change i.val < L
    omega
  have hlocal (i : Fin A.size) : 3 ≤ |displacement A.filling i| := by
    rw [← matching_window_displacement A.window q.symm A.filling hm i]
    exact hphysical _ (contains_embed A.window i)
  letI : NeZero A.size := ⟨by omega⟩
  have hfull : A.filling.support=Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    apply Equiv.Perm.mem_support.mpr
    intro hi
    have hh := hlocal i
    simp only [displacement,hi,sub_self,abs_zero] at hh
    omega
  exact full_support_peak_one_nonshort_defect_ge_four A.filling hfull hlocal
    (fun c hcA => le_of_eq (actual_peak_four_local_cycle_peak_one hn p hmaj hmax hc hk root
      hlarge ht hpos he hp hv hU A hA c hcA))

#print axioms full_support_peak_one_nonshort_defect_ge_four
#print axioms actual_peak_four_nonempty_filling_defect_four
end LRX.FiniteCuts

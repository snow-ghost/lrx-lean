module

public import LRX.ActualOddWidthFiveMinArrow
public import LRX.ActualNonshortFillings
public import LRX.StrictFillingFamilyWidth

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_odd_width_five_nonempty_filling (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=5)
    (A : FillingWindow n)
    (hA : A ∈ positiveSourceFamily (localTarget p 0 (componentLeft p root))
      (componentSet p root).card) (hs : 0 < A.size) :
    6 ≤ A.size ∧ 2 ≤ cycleDefect A.filling := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hspec := positive_source_family_spec q L
  have hm := hspec.1 A hA
  have hbound := hspec.2.2.1 A hA
  have hmin := actual_odd_zero_width_five_large_min_arrow hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv
  have hphysical (i : Fin n) (hi : Contains A.window i) : 3 ≤ |displacement q.symm i| := by
    apply hmin i
    have hhi := hi.2
    change i.val < L
    omega
  have hlocal (i : Fin A.size) : 3 ≤ |displacement A.filling i| := by
    rw [← matching_window_displacement A.window q.symm A.filling hm i]
    exact hphysical _ (contains_embed A.window i)
  refine ⟨finite_min_arrow_three_size A.filling hs hlocal,?_⟩
  exact matched_nonunit_window_defect q.symm A hs hm (fun i hi => by
    have hh := hphysical i hi
    omega)

theorem actual_odd_width_five_positive_filling_defect_sum (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=5)
    (hx : 0 < (componentSet p root).card-
      (prefixSourceCore (localTarget p 0 (componentLeft p root))).card) :
    2 ≤ ((positiveSourceFamily (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).map (fun A => cycleDefect A.filling)).sum := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let As := positiveSourceFamily q L
  have hnon (A : FillingWindow n) : 0 ≤ cycleDefect A.filling := by
    have h := finite_depth_rank A.filling
    unfold cycleDefect
    linarith only [h]
  by_contra hbad
  have hzero (A : FillingWindow n) (hA : A ∈ As) : A.size=0 := by
    by_contra hs
    have hdef := (actual_odd_width_five_nonempty_filling hn p hmaj hmax hc hk root
      hlarge ht hpos he hp hf hv A hA (by omega)).2
    have hle : cycleDefect A.filling ≤ (As.map (fun B => cycleDefect B.filling)).sum := by
      apply List.single_le_sum
      · intro z hz
        obtain ⟨B,_,rfl⟩ := List.mem_map.mp hz
        exact hnon B
      · exact List.mem_map.mpr ⟨A,hA,rfl⟩
    change ¬2 ≤ (As.map (fun B => cycleDefect B.filling)).sum at hbad
    omega
  have hmap : As.map (fun A => A.size)=As.map (fun _ => 0) :=
    List.map_congr_left hzero
  have hsum : (As.map (fun A => A.size)).sum=0 := by rw [hmap]; simp
  have hpart := component_cut_internal_size_partition p (by omega) root (by omega)
  change (As.map (fun A => A.size)).sum+(prefixSourceCore q).card=L at hpart
  change 0 < L-(prefixSourceCore q).card at hx
  omega

theorem actual_odd_width_five_stronger_width_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=5)
    (hx : 0 < (componentSet p root).card-
      (prefixSourceCore (localTarget p 0 (componentLeft p root))).card) :
    (((componentSet p root).card-
      (prefixSourceCore (localTarget p 0 (componentLeft p root))).card : ℕ) : ℤ) ≤
      2*scalarFillingBudget p root-5 := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let As := positiveSourceFamily q L
  let x := L-(prefixSourceCore q).card
  have hZ := actual_odd_width_five_positive_filling_defect_sum hn p hmaj hmax hc hk
    root hlarge ht hpos he hp hf hv hx
  change 2 ≤ (As.map (fun A => cycleDefect A.filling)).sum at hZ
  have hspec := positive_source_family_spec q L
  have hmin := actual_odd_zero_width_five_large_min_arrow hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv
  have hlocal : ∀ A ∈ As, ∀ i, 3 ≤ |displacement A.filling i| := by
    intro A hA i
    have hm := hspec.1 A hA
    have hb := hspec.2.2.1 A hA
    rw [← matching_window_displacement A.window q.symm A.filling hm i]
    apply hmin
    have hi := contains_embed A.window i
    have hh := hi.2
    change (embed A.window i).val < L
    omega
  have hfull : ∀ A ∈ As, A.filling.support.card=A.size := by
    intro A hA
    have hh : A.filling.support=Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro i
      apply Equiv.Perm.mem_support.mpr
      intro hi
      have hl := hlocal A hA i
      simp only [displacement,hi,sub_self,abs_zero] at hl
      omega
    rw [hh]
    simp
  have hbudget := original_unpaid_prefix_filling_budget hn p hmaj hmax hc hk root hlarge hpos
  have hwidth := (original_unpaid_filling_scalar_filters hn p hmaj hmax hc hk root hlarge hpos).1
  change (As.map (fun A => A.size)).sum=x at hwidth
  have hcast : (As.map (fun A => (A.size : ℤ))).sum=(x : ℤ) := by
    have hh := congrArg (fun z : ℕ => (z : ℤ)) hwidth
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using hh
  have hw := nonshort_family_strict_width As (scalarFillingBudget p root) hfull hlocal hbudget
    (by rw [hcast]; change 0 < (x : ℤ); exact_mod_cast hx) hZ
  rw [hcast] at hw
  exact hw

#print axioms actual_odd_width_five_nonempty_filling
#print axioms actual_odd_width_five_positive_filling_defect_sum
#print axioms actual_odd_width_five_stronger_width_reserve
end LRX.FiniteCuts

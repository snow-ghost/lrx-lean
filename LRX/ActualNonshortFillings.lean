import LRX.ActualLargeComponentNoTwo
import LRX.ActualNonunitComponentDefect

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords

/-- A nonempty finite permutation with all arrows of length at least three
needs at least six positions (consider the middle position). -/
theorem finite_min_arrow_three_size {b : ℕ} (σ : State b) (hb : 0 < b)
    (hmin : ∀ i, 3 ≤ |displacement σ i|) : 6 ≤ b := by
  by_contra h
  let i : Fin b := ⟨b/2,by omega⟩
  have hi := (σ i).isLt
  have hh := hmin i
  change 3 ≤ |((σ i).val : ℤ)-((b/2 : ℕ) : ℤ)| at hh
  have hm : b/2 ≤ 2 := by omega
  have hr : b ≤ b/2+3 := by omega
  have ha : |((σ i).val : ℤ)-((b/2 : ℕ) : ℤ)| ≤ 2 :=
    abs_le.mpr ⟨by omega,by omega⟩
  omega

variable {n k : ℕ} [NeZero n]

/-- Nonempty actual internal fillings satisfy the defect input required by
M4 rigidity; zero-width members of positiveSourceFamily are not counted. -/
theorem actual_zero_width_four_nonempty_filling (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (A : FillingWindow n)
    (hA : A ∈ positiveSourceFamily (localTarget p 0 (componentLeft p root))
      (componentSet p root).card) (hs : 0 < A.size) :
    6 ≤ A.size ∧ 2 ≤ cycleDefect A.filling := by
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
  refine ⟨finite_min_arrow_three_size A.filling hs hlocal,?_⟩
  exact matched_nonunit_window_defect q.symm A hs hm (fun i hi => by
    have hh := hphysical i hi
    omega)

theorem actual_zero_width_four_positive_filling_defect_sum (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
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
    have hdef := (actual_zero_width_four_nonempty_filling hn p hmaj hmax hc hk root
      hlarge ht hpos he hp hv A hA (by omega)).2
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

#print axioms finite_min_arrow_three_size
#print axioms actual_zero_width_four_nonempty_filling
#print axioms actual_zero_width_four_positive_filling_defect_sum
end LRX.FiniteCuts

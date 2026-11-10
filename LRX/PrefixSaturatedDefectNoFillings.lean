import LRX.TwoPrunedPartsDefect
import LRX.SourcePacketCyclePartition
import LRX.PrefixFillingSize

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

/-- A component of defect two whose actual source packet already has
that defect cannot contain a nonempty nonunit internal window. -/
theorem prefix_saturated_defect_internal_windows_empty (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (A : FillingWindow n) (hwhere : ∀ i, Contains A.window i ↔ i ∈ componentSet p 0)
    (hmatch : A.Matches p.symm) (hAZ : cycleDefect A.filling=2)
    (hpacket : cycleDefect (canonicalRootPacket p 0)=2)
    (hno : ∀ i ∈ componentSet p 0, 2 ≤ |displacement p.symm i|) :
    ∀ B ∈ positiveSourceFamily p (componentSet p 0).card, B.size=0 := by
  classical
  intro B hB
  by_contra hnonzero
  let S := prefixSourceCore p
  let T := windowPositions B.window
  let C := componentSet p 0
  have hS : ∀ i, p i ∈ S ↔ i ∈ S := prefix_source_core_invariant p
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hC : ∀ i, p i ∈ C ↔ i ∈ C := CycleFootprint.component_invariant hd 0
  have hspec := positive_source_family_spec p (componentSet p 0).card
  have hBm := hspec.1 B hB
  have hT : ∀ i, p i ∈ T ↔ i ∈ T := matched_window_positions_invariant p B hBm
  have hSC : S ⊆ C := by
    intro i hi
    exact (zero_component_prefix p i).mpr (Finset.mem_filter.mp hi).2
  have hTC : T ⊆ C := by
    intro i hi
    have hic : Contains B.window i := by simpa only [T,windowPositions,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    have hb := hspec.2.2.1 B hB
    apply (zero_component_prefix p i).mpr
    unfold Contains at hic
    omega
  have hdis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiT
    have his := (Finset.mem_filter.mp hiS).1
    have hic : Contains B.window i := by simpa only [T,windowPositions,Finset.mem_filter,Finset.mem_univ,true_and] using hiT
    exact positive_family_avoids_source p _ B hB i his hic
  have hAS : windowPositions A.window=C := by
    ext i
    simpa only [windowPositions,Finset.mem_filter,Finset.mem_univ,true_and,C] using hwhere i
  have hCZ := matched_window_pruned_defect p A hmatch
  have hprunedA : PrunedLift.permutation p (windowPositions A.window)
      (matched_window_positions_invariant p A hmatch)=PrunedLift.permutation p C hC := by
    apply Equiv.ext
    intro i
    simp only [PrunedLift.permutation_apply,hAS]
  rw [hprunedA] at hCZ
  change cycleDefect (PrunedLift.permutation p C hC)=cycleDefect A.filling at hCZ
  rw [hAZ] at hCZ
  have hpacketEq : PrunedLift.permutation p S hS=canonicalRootPacket p 0 := by
    apply Equiv.ext
    intro i
    simp only [S,canonicalRootPacket,PrunedLift.permutation_apply,prefix_root_core_eq p hm hc]
  have hSZ : cycleDefect (PrunedLift.permutation p S hS)=2 := by rw [hpacketEq,hpacket]
  have hTZ := matched_window_pruned_defect p B hBm
  have hsum := two_pruned_parts_defect_le_component p S T C hS hT hC hdis hSC hTC
  rw [hSZ,hCZ] at hsum
  change 2+cycleDefect (PrunedLift.permutation p (windowPositions B.window)
    (matched_window_positions_invariant p B hBm)) ≤ 2 at hsum
  rw [hTZ] at hsum
  have hBZ : 2 ≤ cycleDefect B.filling := matched_nonunit_window_defect p.symm B
    (by omega) hBm (by
      intro i hi
      apply hno i
      apply hTC
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  omega

theorem prefix_sources_cover_of_empty_internal_windows (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (hzero : ∀ B ∈ positiveSourceFamily p (componentSet p 0).card, B.size=0) :
    ∀ i ∈ componentSet p 0, i ∈ sourcePackets p := by
  classical
  intro i hi
  by_contra hs
  have hin := prefix_non_source_in_positive_family p hc
    (component_card_lt_of_multiple_roots p hm 0) i ((zero_component_prefix p i).mp hi) hs
  obtain ⟨B,hB,hiB⟩ := (mem_family_positions _ i).mp hin
  have hz := hzero B hB
  unfold Contains at hiB
  omega

/-- The actual remaining unit-energy data supply every premise of the
prefix exclusion, including the component window and the nonunit arrows. -/
theorem unit_energy_prefix_sources_cover (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (hc0 : 2 ≤ (componentSet p 0).card)
    (hf : n-p.support.card=2) (he : canonicalEnergyDeficit p=1)
    (hfixed : isolatedVertices p=p.supportᶜ) (hgeom : ExactDefectTwoComponentWindows p)
    (hPackets : ∀ root ∈ componentRoots p, cycleDefect (canonicalRootPacket p root)=2) :
    ∀ i ∈ componentSet p 0, i ∈ sourcePackets p := by
  classical
  have hleft : componentLeft p 0=0 := by
    apply Fin.ext
    have hh := component_left_bound p 0 0 Relation.ReflTransGen.refl
    change (componentLeft p 0).val ≤ 0 at hh
    change (componentLeft p 0).val=0
    omega
  have hroot := nontrivial_component_left_root p 0 hc0
  rw [hleft] at hroot
  have hpacket := hPackets 0 hroot
  have hno : ∀ i ∈ componentSet p 0, 2 ≤ |displacement p.symm i| := by
    intro i hi
    have him := component_support_of_all_fixed_isolated p hfixed 0 hc0 hi
    have hmove : p.symm i ≠ i := (mem_support_inverse p i).mp him
    have hnon : displacement p.symm i ≠ 0 := by
      intro hz
      apply hmove
      apply Fin.ext
      unfold displacement at hz
      omega
    have hunit := unit_energy_two_fixed_no_unit_arrow p hmaj hf he i
    have hapos := abs_pos.mpr hnon
    omega
  obtain ⟨a,b,A,B,_,hroots,_,_,hAw,hBw,_,hAm,hBm,_,hAZ,hBZ⟩ := hgeom
  have hcases : (0 : Fin n)=a ∨ 0=b := by rw [hroots] at hroot; simpa using hroot
  apply prefix_sources_cover_of_empty_internal_windows p (by omega) hc0
  rcases hcases with ha | hb
  · subst a
    exact prefix_saturated_defect_internal_windows_empty p (by omega) hc0 A hAw hAm hAZ hpacket hno
  · subst b
    exact prefix_saturated_defect_internal_windows_empty p (by omega) hc0 B hBw hBm hBZ hpacket hno

#print axioms prefix_saturated_defect_internal_windows_empty
#print axioms prefix_sources_cover_of_empty_internal_windows
#print axioms unit_energy_prefix_sources_cover
end LRX.FiniteCuts

import LRX.ActualShallowInternalDeficit
import LRX.OriginalShallowExteriorDeficit
import LRX.ReversalFamilyRank

namespace LRX.FiniteCuts
open FiniteWindow FiniteRankOrder
variable {n : ℕ} [NeZero n]

/-- Internal positive source gaps cover precisely the non-source vertices
inside the initial component. -/
theorem prefix_non_source_in_positive_family (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n)
    (i : Fin n) (hi : i.val < (componentSet p 0).card) (hnot : i ∉ sourcePackets p) :
    i ∈ familyPositions (positiveSourceFamily p (componentSet p 0).card) := by
  classical
  obtain ⟨hzero,hr,hw⟩ := prefix_component_source_ends p hc hproper
  obtain ⟨u,hu,hiu⟩ := FiniteGaps.outside_in_gap (sourcePackets p) hzero i hnot
  obtain ⟨hui,hinext⟩ := (FiniteGaps.mem_positions _ _ _).mp hiu
  have hur : u.val < (componentRight p 0).val := by omega
  have hn := FiniteGaps.next_le_member (sourcePackets p) u (componentRight p 0) hr hur
  have hpos := load_path_crossed_port_positive p (component_right_path p 0) u
    (by change 0 ≤ u.val; omega) hur
  have hselected : u ∈ positiveSourceGapStarts p (componentSet p 0).card :=
    (mem_positive_source_gap_starts _ _ _).mpr ⟨hu,by omega,by omega,hpos⟩
  let us : {u // u ∈ positiveSourceGapStarts p (componentSet p 0).card} := ⟨u,hselected⟩
  apply (mem_family_positions _ _).mpr
  refine ⟨positiveSourceFilling p (componentSet p 0).card us,?_,?_⟩
  · exact List.mem_map.mpr ⟨us,by simp,rfl⟩
  · exact (FiniteGaps.contains_window _ _ _).mpr ⟨hui,hinext⟩

theorem positive_family_avoids_source (p : State n) (L : ℕ)
    (A : FillingWindow n) (hA : A ∈ positiveSourceFamily p L)
    (i : Fin n) (hi : i ∈ sourcePackets p) : ¬Contains A.window i := by
  classical
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hA
  intro hh
  have hpos := (FiniteGaps.contains_window (sourcePackets p) u.val i).mp hh
  exact FiniteGaps.gap_avoids_marks (sourcePackets p) u.val i
    ((FiniteGaps.mem_positions _ _ _).mpr hpos) hi

/-- The exact shell family: all internal source gaps and one whole exterior
interval. It covers the complement of the real source packet. -/
theorem exists_shell_window_family (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    ∃ A : FillingWindow n, A.window.offset=(componentSet p 0).card ∧
      A.size=n-(componentSet p 0).card ∧
      (let As := positiveSourceFamily p (componentSet p 0).card++[A]
       (∀ B ∈ As, B.Matches p.symm) ∧ As.Pairwise FillingWindow.Apart ∧
       familyPositions As=(prefixSourceCore p)ᶜ) := by
  classical
  let L := (componentSet p 0).card
  let W : Window n (n-L) := ⟨L,by omega⟩
  have hW (i : Fin n) : Contains W i ↔ L ≤ i.val := by
    have hh := i.isLt
    change (L ≤ i.val ∧ i.val < L+(n-L)) ↔ _
    omega
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  obtain ⟨f,hf⟩ := exists_restriction_of_inverse_closed W p (by
    intro i hi
    have hh := hcut (p.symm i)
    simp only [Equiv.apply_symm_apply] at hh
    rw [hW] at hi ⊢
    omega)
  let A : FillingWindow n := ⟨n-L,W,f⟩
  let Ps := positiveSourceFamily p L
  have hspec := positive_source_family_spec p L
  have hmatch : ∀ B ∈ Ps++[A], B.Matches p.symm := by
    intro B hB
    rcases List.mem_append.mp hB with hB | hB
    · exact hspec.1 B hB
    · have he : B=A := List.mem_singleton.mp hB
      subst B
      exact hf
  have hap : (Ps++[A]).Pairwise FillingWindow.Apart := by
    apply List.pairwise_append.mpr
    refine ⟨hspec.2.1,by simp,?_⟩
    intro B hB C hC
    have he : C=A := List.mem_singleton.mp hC
    subst C
    intro i hiB hiA
    have hb := hspec.2.2.1 B hB
    have hi : L ≤ i.val := (hW i).mp hiA
    have hb' := hiB.2
    omega
  have hcover : familyPositions (Ps++[A])=(prefixSourceCore p)ᶜ := by
    ext i
    rw [mem_family_positions,Finset.mem_compl]
    constructor
    · rintro ⟨B,hB,hi⟩ hcore
      obtain ⟨his,hiL⟩ := Finset.mem_filter.mp hcore
      rcases List.mem_append.mp hB with hB | hB
      · exact positive_family_avoids_source p L B hB i his hi
      · have he : B=A := List.mem_singleton.mp hB
        subst B
        have hh := (hW i).mp hi
        omega
    · intro hi
      by_cases hiL : i.val < L
      · have hnot : i ∉ sourcePackets p := fun hh => hi (Finset.mem_filter.mpr ⟨hh,hiL⟩)
        obtain ⟨B,hB,hBi⟩ := (mem_family_positions _ _).mp
          (prefix_non_source_in_positive_family p hc hproper i hiL hnot)
        exact ⟨B,List.mem_append_left _ hB,hBi⟩
      · exact ⟨A,List.mem_append_right _ (by simp),(hW i).mpr (by omega)⟩
  exact ⟨A,rfl,rfl,hmatch,hap,hcover⟩

/-- The actual upper map for the shell construction. Every selected interval
is reversed and every original source-packet arrow is retained. -/
theorem exists_shell_upper_map (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    ∃ (A : FillingWindow n) (Q : State n),
      A.window.offset=(componentSet p 0).card ∧ A.size=n-(componentSet p 0).card ∧
      (let As := positiveSourceFamily p (componentSet p 0).card++[A]
       Below p.symm Q ∧
       (∀ i ∈ prefixSourceCore p, Q i=p.symm i) ∧
       (∀ B ∈ As, ∀ i, Q (embed B.window i)=embed B.window (Fin.revPerm i)) ∧
       As.Pairwise FillingWindow.Apart ∧ familyPositions As=(prefixSourceCore p)ᶜ) := by
  classical
  obtain ⟨A,hAo,hAs,hm,ha,hcover⟩ := exists_shell_window_family p hc hproper
  let As := positiveSourceFamily p (componentSet p 0).card++[A]
  let Q := reverseWindows As p.symm
  refine ⟨A,Q,hAo,hAs,below_reverse_windows As p.symm hm ha,?_,?_,ha,hcover⟩
  · intro i hi
    apply reverse_windows_outside
    intro B hB hBi
    have hh : i ∈ familyPositions As := (mem_family_positions _ _).mpr ⟨B,hB,hBi⟩
    rw [hcover] at hh
    exact (Finset.mem_compl.mp hh) hi
  · intro B hB i
    exact reverse_windows_on_member As p.symm hm ha B hB i

#print axioms prefix_non_source_in_positive_family
#print axioms positive_family_avoids_source
#print axioms exists_shell_window_family
#print axioms exists_shell_upper_map
end LRX.FiniteCuts

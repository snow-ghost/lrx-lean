import LRX.ShallowShellBoundaryData
import LRX.ShallowShellBoundaryJoin
import LRX.CircularRankTransfer
import LRX.FiniteCycleScan
import LRX.FiniteDisplacementSum
import LRX.FiniteExactAvailability
import LRX.FiniteRootRoute
import LRX.OrderedExactRoute
import LRX.PrunedLoad
import LRX.ZeroGapCycleRoots
import LRX.ExternalPairCycleJoin
import LRX.FiniteRootStar
import LRX.ReversalComplementCycles
import LRX.TranspositionPeak
import LRX.ExternalPairJoinPeak
import LRX.RootAndPairsCount
import LRX.ReversedComplementPairCount
import LRX.ReversedWindowInversionPrice
import LRX.ReversalCombinedPrice
import LRX.EnclosingTwoArcWord
import LRX.ShellInternalWindowData
import LRX.ShellExteriorWindowData
import LRX.ShellAllCursorAssembly

namespace LRX.FiniteCuts
open FiniteWindow FiniteRankOrder
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The actual zero-defect large component supplies a joined cyclic root
inside the already constructed upper target, with exact support and action. -/
theorem exists_shell_joined_rank_word (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (start finish : Fin n) :
    let L := (componentSet p 0).card
    let u := componentRight p 0
    let v : Fin n := ⟨L,component_card_lt_of_multiple_roots p hm 0⟩
    let z : Fin n := ⟨n-1,by have := NeZero.pos n; omega⟩
    ∃ (E : FillingWindow n) (Q C : State n) (w : List Letter),
      E.window.offset=L ∧ E.size=n-L ∧
      (∀ B ∈ positiveSourceFamily p L++[E], ∀ i,
        Q (embed B.window i)=embed B.window (Fin.revPerm i)) ∧
      (positiveSourceFamily p L++[E]).Pairwise FillingWindow.Apart ∧
      familyPositions (positiveSourceFamily p L++[E])=(prefixSourceCore p)ᶜ ∧
      Below p.symm Q ∧ Below p.symm (Q*Equiv.swap u v) ∧ C.IsCycle ∧
      C.support=insert z (insert v (prefixSourceCore p)) ∧
      leftPeak C n=leftPeak ((canonicalRootPacket p 0)⁻¹) n ∧
      (∀ i ∈ C.support, (Q*Equiv.swap u v) i=C i) ∧
      C ∈ (Q*Equiv.swap u v).cycleFactorsFinset ∧
      (∀ D ∈ (Q*Equiv.swap u v).cycleFactorsFinset, D ≠ C →
        (∃ a b : Fin n, a ≠ b ∧ D=Equiv.swap a b) ∧ leftPeak D n=1) ∧
      (prefixSourceCore p).card+2+
        2*((Q*Equiv.swap u v).cycleFactorsFinset.erase C).card=
          (Q*Equiv.swap u v).support.card ∧
      (∑ D ∈ (Q*Equiv.swap u v).cycleFactorsFinset.erase C, leftPeak D n)=
        ((Q*Equiv.swap u v).cycleFactorsFinset.erase C).card ∧
      ((Q*Equiv.swap u v).cycleFactorsFinset.erase C).card+1=
        ((positiveSourceFamily p L++[E]).map (fun B => B.size/2)).sum ∧
      (start ≠ finish →
        (∀ dir : Bool, ∃ r ∈ C.support, ∃ port : Fin n,
          (port=r ∨ port+1=r) ∧
          (RotationWords.arcCoordinate dir start port).val ≤
            (RotationWords.arcCoordinate dir start finish).val ∧
          0 < RotationWords.portLoad (displacement C) port) →
        ∃ w' : List Letter,
          eval w'=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
          (w'.length : ℤ) ≤ (inversionNumber p : ℤ)+
            (∑ i, |displacement (Q*Equiv.swap u v) i|)+(n/2 : ℕ)-
            (leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ)-
            (((positiveSourceFamily p L++[E]).map (fun B => B.size/2)).sum : ℕ)) ∧
      InternalShellGapWords p Q C hm start finish ∧
      ExteriorShellGapWords p Q C hm start finish ∧
      PrunedLift.RootStar (Q*Equiv.swap u v).symm (displacement (Q*Equiv.swap u v)) 0 ∧
      inversionNumber Q=inversionNumber ((canonicalRootPacket p 0)⁻¹)+
        ((positiveSourceFamily p L++[E]).map (fun B => B.size.choose 2)).sum ∧
      (∑ i, |displacement Q i|)=(∑ i, |displacement ((canonicalRootPacket p 0)⁻¹) i|)+
        ((positiveSourceFamily p L++[E]).map
          (fun B => ∑ i : Fin B.size, |displacement Fin.revPerm i|)).sum ∧
      (inversionNumber Q : ℤ)+(∑ i, |displacement Q i|)=
        2*(∑ i, |displacement ((canonicalRootPacket p 0)⁻¹) i|)-
          ((prefixSourceCore p).card : ℤ)+1+
          ((positiveSourceFamily p L++[E]).map
            (fun B => (B.size : ℤ)^2-((B.size+1)/2 : ℕ))).sum ∧
      inversionNumber (Q*Equiv.swap u v)=inversionNumber Q+1 ∧
      (∑ i, |displacement (Q*Equiv.swap u v) i|)=(∑ i, |displacement Q i|)+2 ∧
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
        (∑ i, |displacement (Q*Equiv.swap u v) i|)+(n/2 : ℕ)-
        (leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ)-
        (((positiveSourceFamily p L++[E]).map (fun B => B.size/2)).sum : ℕ) := by
  classical
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have hout := prefix_multiple_components_exterior_size p hc hm
  have hproper := component_card_lt_of_multiple_roots p hm 0
  let L := (componentSet p 0).card
  let u := componentRight p 0
  let v : Fin n := ⟨L,hproper⟩
  let z : Fin n := ⟨n-1,by have := NeZero.pos n; omega⟩
  let A : State n := (canonicalRootPacket p 0)⁻¹
  have hS : A.support=prefixSourceCore p := by
    rw [Equiv.Perm.support_inv]
    exact prefix_root_packet_support p hm hc
  obtain ⟨hzero,hright,hwidth⟩ := prefix_component_source_ends p hc hproper
  have hroot : (0 : Fin n) ∈ p.support := (mem_support_inverse p 0).mpr ((mem_source_packets p 0).mp hzero).1
  have hcycle : A.IsCycle := (canonical_root_packet_shallow_of_zero_defect p hmaj 0 hroot hz).1.inv
  have hu : u ∈ A.support := by rw [hS]; exact Finset.mem_filter.mpr ⟨hright,by dsimp only [u]; omega⟩
  have hv : v ∉ A.support := by
    rw [hS]
    intro hh
    have hval := (Finset.mem_filter.mp hh).2
    change L < L at hval
    omega
  have hzz : z ∉ A.support := by
    rw [hS]
    intro hh
    have hval := (Finset.mem_filter.mp hh).2
    change n-1 < (componentSet p 0).card at hval
    omega
  have hvz : v ≠ z := by
    intro hh
    have he := congrArg Fin.val hh
    change L=n-1 at he
    dsimp only [L] at he
    omega
  obtain ⟨E,Q,hEo,hEs,hrev,hapart,hcover,hbelow,hkeep,hQv,hQz,hbelowG,_,_,hI,hMass⟩ :=
    exists_shell_boundary_upper_data p hc hout
  have hQA : ∀ i ∈ A.support, Q i=A i := by
    intro i hi
    have hcore : i ∈ PrunedLift.core p (displacement p.symm) 0 := by
      rw [prefix_root_core_eq p hm hc]
      rwa [← hS]
    have hAi : A i=p.symm i := by
      change (PrunedLift.permutation p _ (PrunedLift.core_invariant p (displacement p.symm) 0)).symm i=p.symm i
      simp only [PrunedLift.permutation_symm_apply,if_pos hcore]
    exact (hkeep i (by rwa [← hS])).trans hAi.symm
  obtain ⟨hIQ,hMassQ⟩ := reversed_window_prices (positiveSourceFamily p L++[E]) A Q hapart
    (by
      intro B hB i
      apply Equiv.Perm.notMem_support.mp
      have hh : embed B.window i ∈ familyPositions (positiveSourceFamily p L++[E]) :=
        (mem_family_positions _ _).mpr ⟨B,hB,contains_embed B.window i⟩
      rwa [hcover,Finset.mem_compl,← hS] at hh)
    hrev
    (by
      intro i hi
      have hiS : i ∈ prefixSourceCore p := by
        rw [hcover,Finset.mem_compl,not_not] at hi
        exact hi
      exact hQA i (by rwa [hS]))
  have hshallowA : (∑ i, |displacement A i|)-(inversionNumber A : ℤ)=
      (A.support.card : ℤ)-1 := by
    have hh := (shallow_iff_direct (canonicalRootPacket p 0)).mp
      (canonical_root_packet_shallow_of_zero_defect p hmaj 0 hroot hz).2
    have hs : A.support=(canonicalRootPacket p 0).support := Equiv.Perm.support_inv _
    have hi : inversionNumber A=inversionNumber (canonicalRootPacket p 0) :=
      inversion_number_inverse _
    rw [hs,hi]
    simpa only [A,Equiv.Perm.inv_def,displacement_mass_inverse] using hh
  have hcombined := reversed_shallow_combined_price
    (positiveSourceFamily p L++[E]) A Q hshallowA hIQ hMassQ
  rw [hS] at hcombined
  let C := A*Equiv.swap v z*Equiv.swap u v
  obtain ⟨hC,hCs⟩ := ZeroGap.cycle_external_pair_join A hcycle u v z hu hv hzz hvz
  have hpeak : leftPeak C n=leftPeak A n := by
    apply external_pair_join_left_peak A hcycle u v z hu
    · intro i hi
      rw [hS] at hi
      have hval := (Finset.mem_filter.mp hi).2
      dsimp only [u]
      omega
    · dsimp only [u,v,L]
      omega
    · dsimp only [v,z,L]
      omega
  have hagree := ZeroGap.external_pair_join_agrees A Q u v z hu hv hzz hvz hQA hQv hQz
  have hfactor : C ∈ (Q*Equiv.swap u v).cycleFactorsFinset := by
    apply Equiv.Perm.mem_cycleFactorsFinset_iff.mpr
    refine ⟨hC,?_⟩
    intro i hi
    exact (hagree i (by rwa [← hCs])).symm
  have hother : ∀ D ∈ (Q*Equiv.swap u v).cycleFactorsFinset, D ≠ C →
      (∃ a b : Fin n, a ≠ b ∧ D=Equiv.swap a b) ∧ leftPeak D n=1 := by
    intro D hD hne
    have huC : u ∈ C.support := by
      rw [hCs]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
    have hvC : v ∈ C.support := by rw [hCs]; simp
    have houtside : ∀ x, x ∉ C.support →
        x ∈ familyPositions (positiveSourceFamily p L++[E]) := by
      intro x hx
      rw [hcover,Finset.mem_compl]
      intro hh
      apply hx
      rw [hCs,hS]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hh)
    obtain ⟨a,b,hab,hpair⟩ := nonroot_cycle_swap_of_reversed_cover
      (positiveSourceFamily p L++[E]) Q C u v hrev hfactor huC hvC houtside D hD hne
    exact ⟨⟨a,b,hab,hpair⟩,by rw [hpair]; exact transposition_left_peak a b hab⟩
  obtain ⟨hcount,hdiscount⟩ := root_and_pairs_count (Q*Equiv.swap u v) C hfactor
    (fun D hD hne => (hother D hD hne).1)
  have hCcard : C.support.card=(prefixSourceCore p).card+2 := by
    rw [hCs,Finset.card_insert_of_notMem (by simp [hzz,Ne.symm hvz]),
      Finset.card_insert_of_notMem hv,hS]
  rw [hCcard] at hcount
  have hcoreMoved : prefixSourceCore p ⊆ Q.support := by
    intro i hi
    have hiA : i ∈ A.support := by rwa [hS]
    rw [Equiv.Perm.mem_support,hQA i hiA]
    exact Equiv.Perm.mem_support.mp hiA
  have hsupport : (Q*Equiv.swap u v).support=Q.support := by
    apply support_mul_swap_of_endpoints_moved Q u v
    · exact hcoreMoved (by rwa [← hS])
    · apply Equiv.Perm.mem_support.mpr
      rw [hQv]
      exact Ne.symm hvz
    · apply Equiv.Perm.mem_cycleFactorsFinset_support_le hfactor
      rw [hCs]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
    · apply Equiv.Perm.mem_cycleFactorsFinset_support_le hfactor
      rw [hCs]
      simp
  have hpairsCount := reversed_complement_pairs_count
    (positiveSourceFamily p L++[E]) Q (Q*Equiv.swap u v) C (prefixSourceCore p)
    hrev hapart hcover hcoreMoved hsupport hfactor hCcard
    (fun D hD hne => (hother D hD hne).1)
  have h0 : (0 : Fin n) ∈ C.support := by
    rw [hCs,hS]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hzero,by change 0 < (componentSet p 0).card; omega⟩))
  have hzmem : z ∈ C.support := by rw [hCs]; exact Finset.mem_insert_self _ _
  have hgap := shell_internal_gap_words (by omega) p hm hc Q C
    (hCs.trans (by rw [hS]))
    (fun B hB => hrev B (List.mem_append_left _ hB)) hbelowG hfactor start finish
  have hgapExt := shell_exterior_gap_words (by omega) p hm hc Q C E hEo hEs
    (hrev E (List.mem_append_right _ (List.mem_singleton_self _)))
    (hCs.trans (by rw [hS])) hbelowG hfactor start finish
  have htwo : start ≠ finish →
      (∀ dir : Bool, ∃ r ∈ C.support, ∃ port : Fin n,
        (port=r ∨ port+1=r) ∧
        (RotationWords.arcCoordinate dir start port).val ≤
          (RotationWords.arcCoordinate dir start finish).val ∧
        0 < RotationWords.portLoad (displacement C) port) →
      ∃ w' : List Letter,
        eval w'=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
        (w'.length : ℤ) ≤ (inversionNumber p : ℤ)+
          (∑ i, |displacement (Q*Equiv.swap u v) i|)+(n/2 : ℕ)-
          (leftPeak A n : ℤ)-
          (((positiveSourceFamily p L++[E]).map (fun B => B.size/2)).sum : ℕ) := by
    intro hne hboth
    obtain ⟨w',hw',hl'⟩ := enclosing_positive_arcs_word (by omega) p (Q*Equiv.swap u v) C
      hbelowG hfactor h0 hzmem start finish hne hboth
    have hs : (∑ D ∈ (Q*Equiv.swap u v).cycleFactorsFinset.erase C, (leftPeak D n : ℤ))=
        (((Q*Equiv.swap u v).cycleFactorsFinset.erase C).card : ℤ) := by
      exact_mod_cast hdiscount
    have hj : (((Q*Equiv.swap u v).cycleFactorsFinset.erase C).card : ℤ)+1=
        (((positiveSourceFamily p L++[E]).map (fun B => B.size/2)).sum : ℕ) := by
      exact_mod_cast hpairsCount
    rw [hs,hpeak] at hl'
    exact ⟨w',hw',by linarith⟩
  have hsame : (Q*Equiv.swap u v).SameCycle 0 z :=
    (ZeroGap.cycle_root_same_cycle hfactor h0).symm.trans (ZeroGap.cycle_root_same_cycle hfactor hzmem)
  have hstar : PrunedLift.RootStar (Q*Equiv.swap u v).symm
      (displacement (Q*Equiv.swap u v)) 0 := by
    have hh := PrunedLift.enclosing_cycle_root_star (Q*Equiv.swap u v).symm 0 0 z
      (Equiv.Perm.SameCycle.refl _ _) (by simpa only [Equiv.Perm.inv_def,Equiv.symm_symm] using hsame)
      (by
        intro i _
        change 0 ≤ i.val ∧ i.val ≤ n-1
        have := i.isLt
        omega)
    unfold displacement
    simpa only [Equiv.symm_symm] using hh
  have hbudget : leftPeak A n+((positiveSourceFamily p L++[E]).map (fun B => B.size/2)).sum ≤ n/2 := by
    have hcap := twice_left_peak_le_support A n
    rw [hS] at hcap
    have hncard : (Q*Equiv.swap u v).support.card ≤ n := by
      simpa using Finset.card_le_univ (Q*Equiv.swap u v).support
    omega
  let K : ℤ := (n/2 : ℕ)-(leftPeak A n : ℤ)-
    (((positiveSourceFamily p L++[E]).map (fun B => B.size/2)).sum : ℕ)
  have hK : 0 ≤ K := by dsimp only [K]; omega
  obtain ⟨w,hw,hlen⟩ := shell_all_cursor_word (by omega) p hm hc Q C
    (hCs.trans (by rw [hS])) hbelowG hfactor start finish K hK hgap hgapExt
    (by
      intro hne hboth
      obtain ⟨w,hw,hl⟩ := htwo hne hboth
      refine ⟨w,hw,?_⟩
      dsimp only [K]
      linarith)
  have hlen' : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
      (∑ i, |displacement (Q*Equiv.swap u v) i|)+(n/2 : ℕ)-
      (leftPeak A n : ℤ)-(((positiveSourceFamily p L++[E]).map (fun B => B.size/2)).sum : ℕ) := by
    dsimp only [K] at hlen
    linarith
  refine ⟨E,Q,C,w,hEo,hEs,hrev,hapart,hcover,hbelow,hbelowG,hC,?_,hpeak,?_,hfactor,hother,hcount,hdiscount,hpairsCount,htwo,hgap,hgapExt,hstar,hIQ,hMassQ,hcombined,hI,hMass,hw,hlen'⟩
  · exact hCs.trans (by rw [hS])
  · intro i hi
    apply hagree i
    rwa [← hCs]

#print axioms exists_shell_joined_rank_word
end LRX.FiniteCuts

import LRX.PacketComponentDefectBound
import LRX.ComponentPacketPartition

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

theorem component_packet_support_in_source (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n) (hr : root ∈ componentRoots p) :
    (canonicalRootPacket p root).support ⊆ sourcePackets p := by
  intro i hi
  obtain ⟨him,hcore⟩ := (mem_canonical_packet_support p root i).mp hi
  apply (mem_source_packets p i).mpr
  refine ⟨(mem_support_inverse p i).mp him,?_⟩
  intro j hji
  have hjmove : p.symm j ≠ j := by
    intro hjfix
    have he := fixed_service_path p hjfix hji
    subst j
    exact (mem_support_inverse p i).mp him hjfix
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hpath := (CycleFootprint.service_path_load_path hd hcore.1).trans
    (CycleFootprint.load_path_symm _ (CycleFootprint.service_path_load_path hd hji))
  exact hcore.2.trans (component_root_reaches hn p hm root hr j hjmove hpath)

theorem component_packet_list_source_product (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (roots : List (Fin n))
    (hnd : roots.Nodup) (hr : ∀ r, r ∈ roots ↔ r ∈ componentRoots p) :
    (roots.map (canonicalRootPacket p)).prod=sourceTarget p := by
  classical
  have hdis := component_packet_list_disjoint p roots hnd (fun r h => (hr r).mp h)
  apply Equiv.ext
  intro i
  by_cases hi : i ∈ sourcePackets p
  · have hmove := ((mem_source_packets p i).mp hi).1
    obtain ⟨r,hrr,hpath⟩ := component_roots_cover p i hmove
    have hri := component_root_reaches hn p hm r hrr i hmove hpath
    have his := (mem_source_packets p i).mp hi
    have hc : PrunedLift.InCore p (displacement p.symm) r i := ⟨hri,his.2 r hri⟩
    have hip := (mem_canonical_packet_support p r i).mpr ⟨(mem_support_inverse p i).mpr hmove,hc⟩
    have he := Equiv.Perm.eq_on_support_mem_disjoint
      (List.mem_map.mpr ⟨r,(hr r).mpr hrr,rfl⟩) hdis i hip
    rw [← he]
    simp only [canonicalRootPacket,PrunedLift.permutation_apply,
      (PrunedLift.mem_core p (displacement p.symm) r i).mpr hc,ite_eq_left,
      sourceTarget,hi]
  · have hall : ∀ q ∈ roots.map (canonicalRootPacket p), q i=i := by
      intro q hq
      obtain ⟨r,hrr,rfl⟩ := List.mem_map.mp hq
      apply Equiv.Perm.notMem_support.mp
      intro hh
      exact hi (component_packet_support_in_source hn p hm r ((hr r).mp hrr) hh)
    have aux (qs : List (State n)) (hh : ∀ q ∈ qs, q i=i) : qs.prod i=i := by
      induction qs with
      | nil => rfl
      | cons q qs ih =>
        simp only [List.prod_cons,Equiv.Perm.mul_apply]
        rw [ih (fun z hz => hh z (List.mem_cons_of_mem _ hz))]
        exact hh q (by simp)
    rw [aux _ hall]
    simp [sourceTarget,PrunedLift.permutation_apply,hi]

noncomputable def fillingTarget (p : State n) : State n :=
  PrunedLift.permutation p (sourcePackets p)ᶜ (PrunedLift.complement_invariant p _ (source_packets_invariant p))

theorem filling_target_cycle_factors (p : State n) :
    Equiv.Perm.cycleFactorsFinset (fillingTarget p).symm=fillingCycles p := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨hcy,hact⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc
    have hout : ∀ i ∈ c.support, i ∉ sourcePackets p := by
      intro i hi hs
      have hfix : (fillingTarget p).symm i=i := by
        simp [fillingTarget,PrunedLift.permutation_symm_apply,hs]
      have hneq := Equiv.Perm.mem_support.mp hi
      exact hneq ((hact i hi).trans hfix)
    apply Finset.mem_filter.mpr
    refine ⟨Equiv.Perm.mem_cycleFactorsFinset_iff.mpr ⟨hcy,?_⟩,Finset.disjoint_left.mpr hout⟩
    intro i hi
    have hh := hact i hi
    simpa [fillingTarget,PrunedLift.permutation_symm_apply,hout i hi] using hh
  · intro hc
    obtain ⟨hc,hdis⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcy,hact⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc
    apply Equiv.Perm.mem_cycleFactorsFinset_iff.mpr
    refine ⟨hcy,?_⟩
    intro i hi
    have hout : i ∉ sourcePackets p := fun hh => Finset.disjoint_left.mp hdis hi hh
    simpa [fillingTarget,PrunedLift.permutation_symm_apply,hout] using hact i hi

theorem cycle_factor_count_symm (q : State n) :
    (Equiv.Perm.cycleFactorsFinset q.symm).card=q.cycleFactorsFinset.card := by
  have hh := congrArg Multiset.card (Equiv.Perm.cycleType_inv q)
  simpa only [Equiv.Perm.cycleType,Multiset.card_map,Finset.card_val,Equiv.Perm.inv_def] using hh

theorem source_filling_cycle_count_partition (p : State n) :
    p.cycleFactorsFinset.card=(sourceTarget p).cycleFactorsFinset.card+(fillingCycles p).card := by
  classical
  have hd := PrunedLift.permutation_disjoint p (sourcePackets p) (source_packets_invariant p)
  have hp := PrunedLift.permutation_partition p (sourcePackets p) (source_packets_invariant p)
  change (sourceTarget p).Disjoint (fillingTarget p) at hd
  change sourceTarget p*fillingTarget p=p at hp
  have hcount : p.cycleFactorsFinset.card=(sourceTarget p).cycleFactorsFinset.card+
      (fillingTarget p).cycleFactorsFinset.card := by
    calc
      _ = (sourceTarget p*fillingTarget p).cycleFactorsFinset.card := congrArg (fun q : State n => q.cycleFactorsFinset.card) hp.symm
      _ = _ := by rw [hd.cycleFactorsFinset_mul_eq_union,Finset.card_union_of_disjoint hd.disjoint_cycleFactorsFinset]
  have hfill : (fillingTarget p).cycleFactorsFinset.card=(fillingCycles p).card := by
    rw [← cycle_factor_count_symm (fillingTarget p),filling_target_cycle_factors]
  rw [hfill] at hcount
  exact hcount

/-- The four nonfilling cycles are exactly two cycles in each actual
packet. All roots, disjointness and the product identity are derived. -/
theorem source_packet_cycles_exact_two_of_four (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (hgeom : ExactDefectTwoComponentWindows p)
    (hK : p.cycleFactorsFinset.card=(fillingCycles p).card+4) :
    ∀ root ∈ componentRoots p, (canonicalRootPacket p root).cycleFactorsFinset.card=2 := by
  classical
  obtain ⟨a,b,hab,hroots⟩ := Finset.card_eq_two.mp (show (componentRoots p).card=2 by omega)
  have ha : a ∈ componentRoots p := by rw [hroots]; simp
  have hb : b ∈ componentRoots p := by rw [hroots]; simp
  have hprod := component_packet_list_source_product (by omega) p (by omega) [a,b]
    (by simp [hab]) (by intro r; rw [hroots]; simp)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at hprod
  have hdis := distinct_component_packets_disjoint p a b ha hb hab
  have hsum : (sourceTarget p).cycleFactorsFinset.card=
      (canonicalRootPacket p a).cycleFactorsFinset.card+(canonicalRootPacket p b).cycleFactorsFinset.card := by
    calc
      _ = (canonicalRootPacket p a*canonicalRootPacket p b).cycleFactorsFinset.card :=
        congrArg (fun q : State n => q.cycleFactorsFinset.card) hprod.symm
      _ = _ := by rw [hdis.cycleFactorsFinset_mul_eq_union,Finset.card_union_of_disjoint hdis.disjoint_cycleFactorsFinset]
  have hpartition := source_filling_cycle_count_partition p
  have hsource : (sourceTarget p).cycleFactorsFinset.card=4 := by omega
  have hcaps := exact_defect_two_windows_packet_cycles_le_two p hmaj hgeom
  have hA : (canonicalRootPacket p a).cycleFactorsFinset.card=2 := by have := hcaps a ha; have := hcaps b hb; omega
  have hB : (canonicalRootPacket p b).cycleFactorsFinset.card=2 := by have := hcaps a ha; have := hcaps b hb; omega
  intro root hr
  have hcases : root=a ∨ root=b := by rw [hroots] at hr; simpa using hr
  rcases hcases with rfl | rfl
  · exact hA
  · exact hB

theorem exact_defect_two_windows_packet_defect_eq_two (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hgeom : ExactDefectTwoComponentWindows p)
    (hK : ∀ root ∈ componentRoots p, (canonicalRootPacket p root).cycleFactorsFinset.card=2) :
    ∀ root ∈ componentRoots p, cycleDefect (canonicalRootPacket p root)=2 := by
  classical
  obtain ⟨a,b,A,B,_,hroots,_,_,hAw,hBw,_,hAm,hBm,_,hAZ,hBZ⟩ := hgeom
  intro root hr
  have hmove : root ∈ p.support := (Finset.mem_filter.mp hr).1
  have hlow := packet_strong_cycle_defect_bound p hmaj root hmove
  rw [hK root hr] at hlow
  norm_num at hlow
  have hupper : cycleDefect (canonicalRootPacket p root) ≤ 2 := by
    have hcases : root=a ∨ root=b := by rw [hroots] at hr; simpa using hr
    rcases hcases with rfl | rfl
    · have hh := packet_defect_le_matched_component p _ A hAw hAm
      rw [hAZ] at hh
      exact hh
    · have hh := packet_defect_le_matched_component p _ B hBw hBm
      rw [hBZ] at hh
      exact hh
  omega

#print axioms component_packet_list_source_product
#print axioms source_filling_cycle_count_partition
#print axioms source_packet_cycles_exact_two_of_four
#print axioms exact_defect_two_windows_packet_defect_eq_two
end LRX.FiniteCuts

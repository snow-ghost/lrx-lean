import LRX.ZeroEnergyShallowPacket

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The actual strong core at zero is exactly the source vertices of the
initial nontrivial component. -/
theorem prefix_root_core_eq (p : State n) (hm : 2 ≤ (componentRoots p).card)
    (hc : 2 ≤ (componentSet p 0).card) :
    PrunedLift.core p (displacement p.symm) 0=prefixSourceCore p := by
  classical
  have hproper := component_card_lt_of_multiple_roots p hm 0
  have hends := prefix_component_source_ends p hc hproper
  have hzero := (mem_source_packets p 0).mp hends.1
  have hl : componentLeft p 0=0 := by
    have hh := component_left_bound p 0 0 Relation.ReflTransGen.refl
    apply Fin.ext
    change (componentLeft p 0).val=0
    change (componentLeft p 0).val ≤ 0 at hh
    omega
  have hroot : (0 : Fin n) ∈ componentRoots p := by
    have hh := nontrivial_component_left_root p 0 hc
    rwa [hl] at hh
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  ext i
  rw [PrunedLift.mem_core]
  change PrunedLift.InCore p (displacement p.symm) 0 i ↔ _
  simp only [prefixSourceCore,Finset.mem_filter]
  constructor
  · intro hi
    have him : p.symm i ≠ i := by
      intro hh
      have he := fixed_service_path p hh hi.2
      subst i
      exact hzero.1 hh
    have his : i ∈ sourcePackets p := (mem_source_packets p i).mpr ⟨him,by
      intro j hj
      exact hi.2.trans (hzero.2 j (hj.trans hi.2))⟩
    refine ⟨his,?_⟩
    apply (zero_component_prefix p i).mp
    exact (CycleFootprint.mem_component _ _ _).mpr (CycleFootprint.service_path_load_path hd hi.1)
  · rintro ⟨his,hiL⟩
    have hs := (mem_source_packets p i).mp his
    have hip := (CycleFootprint.mem_component _ _ _).mp ((zero_component_prefix p i).mpr hiL)
    have hreach := component_root_reaches (by have := NeZero.pos n; have := (Finset.card_le_univ (componentSet p 0)); simp only [Fintype.card_fin] at this; omega)
      p hm 0 hroot i hs.1 hip
    exact ⟨hreach,hs.2 0 hreach⟩

/-- No fixed vertex remains in the initial root core, so the packet's
support is the exact source core used by the area-window geometry. -/
theorem prefix_root_packet_support (p : State n) (hm : 2 ≤ (componentRoots p).card)
    (hc : 2 ≤ (componentSet p 0).card) :
    (canonicalRootPacket p 0).support=prefixSourceCore p := by
  classical
  have he := prefix_root_core_eq p hm hc
  ext i
  rw [mem_support_inverse]
  change (PrunedLift.permutation p (PrunedLift.core p (displacement p.symm) 0)
    (PrunedLift.core_invariant p (displacement p.symm) 0)).symm i ≠ i ↔ _
  rw [PrunedLift.permutation_symm_apply]
  by_cases hi : i ∈ PrunedLift.core p (displacement p.symm) 0
  · rw [if_pos hi]
    have his : i ∈ prefixSourceCore p := by rwa [← he]
    have hmoving := ((mem_source_packets p i).mp (Finset.mem_filter.mp his).1).1
    exact ⟨fun _ => his,fun _ => hmoving⟩
  · rw [if_neg hi]
    have his : i ∉ prefixSourceCore p := by rwa [← he]
    simp only [ne_eq,not_true_eq_false,false_iff]
    exact his

/-- The physical extreme vertices of the initial component belong to the
actual packet support. Its right endpoint is the component size minus one. -/
theorem prefix_root_packet_extremes (p : State n) (hm : 2 ≤ (componentRoots p).card)
    (hc : 2 ≤ (componentSet p 0).card) :
    (0 : Fin n) ∈ (canonicalRootPacket p 0).support ∧
      componentRight p 0 ∈ (canonicalRootPacket p 0).support ∧
      (componentRight p 0).val+1=(componentSet p 0).card := by
  have hproper := component_card_lt_of_multiple_roots p hm 0
  obtain ⟨hz,hr,hw⟩ := prefix_component_source_ends p hc hproper
  rw [prefix_root_packet_support p hm hc]
  refine ⟨Finset.mem_filter.mpr ⟨hz,by change 0 < (componentSet p 0).card; omega⟩,
    Finset.mem_filter.mpr ⟨hr,by omega⟩,hw⟩

#print axioms prefix_root_core_eq
#print axioms prefix_root_packet_support
#print axioms prefix_root_packet_extremes
end LRX.FiniteCuts

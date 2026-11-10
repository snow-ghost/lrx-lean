import LRX.ComponentPacketPartition
import LRX.JoinedSourcePeak

/-! M4: the global source half-peak belongs to a real component packet.
This connects numerical U to the exact services already constructed. -/
namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Every vertex of the strong core of a real component root is a source. -/
theorem component_core_is_source (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hr : root ∈ componentRoots p) (i : Fin n)
    (hi : PrunedLift.InCore p (displacement p.symm) root i) : i ∈ sourcePackets p := by
  have hmov := component_root_moved p root hr
  have hs := component_universal_source p root hmov
    (fun j hj hp => component_root_reaches hn p hm root hr j hj hp)
  have hroot := (mem_source_packets p root).mp hs
  apply (mem_source_packets p i).mpr
  refine ⟨?_,?_⟩
  · intro hh
    have he := fixed_service_path p hh hi.2
    subst i
    exact hmov hh
  · intro j hj
    exact hi.2.trans (hroot.2 j (hj.trans hi.2))

theorem source_forward_iff (p : State n) (e : ℕ) (i : Fin n) :
    i ∈ forward (sourceTarget p).symm e ↔
      i ∈ sourcePackets p ∧ i ∈ forward p.symm e := by
  classical
  simp only [mem_forward,sourceTarget,PrunedLift.permutation_symm_apply]
  by_cases hi : i ∈ sourcePackets p <;> simp [hi]

theorem packet_forward_iff (p : State n) (root : Fin n) (e : ℕ) (i : Fin n) :
    i ∈ forward (canonicalRootPacket p root).symm e ↔
      PrunedLift.InCore p (displacement p.symm) root i ∧ i ∈ forward p.symm e := by
  classical
  simp only [mem_forward,canonicalRootPacket,PrunedLift.permutation_symm_apply,
    PrunedLift.mem_core]
  by_cases hi : PrunedLift.InCore p (displacement p.symm) root i <;> simp [hi]

/-- Any canonical arrow crossing a cut connects its origin to that cut's port. -/
theorem forward_arrow_load_path (p : State n) (port i : Fin n)
    (hi : i ∈ forward p.symm (port.val+1)) :
    CycleFootprint.LoadPath (displacement p.symm) i port := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hh := (mem_forward p.symm (port.val+1) i).mp hi
  exact finite_load_path_interval p (CycleFootprint.arrow_target_load_path hd i) port
    (by omega) (by omega)

/-- The whole source load at a component port is the load of its real packet. -/
theorem component_packet_forward_eq (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (root port : Fin n)
    (hr : root ∈ componentRoots p)
    (hp : CycleFootprint.LoadPath (displacement p.symm) root port) :
    forward (canonicalRootPacket p root).symm (port.val+1)=
      forward (sourceTarget p).symm (port.val+1) := by
  classical
  ext i
  rw [packet_forward_iff,source_forward_iff]
  constructor
  · rintro ⟨hc,hf⟩
    exact ⟨component_core_is_source hn p hm root hr i hc,hf⟩
  · rintro ⟨hs,hf⟩
    have hi := (mem_source_packets p i).mp hs
    have hip := forward_arrow_load_path p port i hf
    have hri := component_root_reaches hn p hm root hr i hi.1
      (hp.trans (CycleFootprint.load_path_symm _ hip))
    exact ⟨⟨hri,hi.2 root hri⟩,hf⟩

/-- Global source peak U is attained in an actual component packet; no
absence-of-fillings or structural classification premise is needed. -/
theorem exists_component_packet_peak_ge_source (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hpos : 0 < sourceHalfPeak p) :
    ∃ root ∈ componentRoots p,
      sourceHalfPeak p ≤ leftPeak (canonicalRootPacket p root).symm n := by
  classical
  obtain ⟨port,_,_,hload⟩ := left_peak_port (sourceTarget p).symm n le_rfl hpos
  have hpositive : 0 < (forward (sourceTarget p).symm (port.val+1)).card := by
    change 0 < halfLoad (sourceTarget p).symm (port.val+1)
    rw [hload]
    exact hpos
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hpositive
  obtain ⟨hs,hf⟩ := (source_forward_iff p (port.val+1) i).mp hi
  have hmove := ((mem_source_packets p i).mp hs).1
  obtain ⟨root,hr,hri⟩ := component_roots_cover p i hmove
  have hp := hri.trans (forward_arrow_load_path p port i hf)
  have he := component_packet_forward_eq hn p hm root port hr hp
  have he' : halfLoad (canonicalRootPacket p root).symm (port.val+1)=sourceHalfPeak p := by
    change (forward (canonicalRootPacket p root).symm (port.val+1)).card=_
    rw [he]
    exact hload
  refine ⟨root,hr,?_⟩
  rw [← he']
  exact Finset.le_sup (Finset.mem_range.mpr (by have := port.isLt; omega))

#print axioms component_packet_forward_eq
#print axioms exists_component_packet_peak_ge_source
end LRX.FiniteCuts

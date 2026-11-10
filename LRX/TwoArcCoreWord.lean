module

public import LRX.IncidentArcPorts

@[expose] public section

/-! Both arcs need only contain incident packet ports. One positive port
anywhere on the circle supplies the combined saving needed by the budget. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem two_arc_incident_packet_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (start finish : Fin n) (hne : start ≠ finish)
    (hboth : ∀ dir : Bool, ∃ port : Fin n, IncidentPacketPort p d 0 port ∧
      (arcCoordinate dir start port).val ≤ (arcCoordinate dir start finish).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  classical
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := FiniteWindow.majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  obtain ⟨cycles,hcycles,hout,hcycleports,hcount⟩ := ZeroGap.arc_cycle_partition p d start finish hne
  obtain ⟨ports,hincident,hport,hload⟩ := incident_arc_ports_with_saving hd hroot start finish hne hboth
  have hfamilies : ∀ dir : Bool, ∃ all : List (ExactService n),
      all.Pairwise (fun a b => a.service.target.Disjoint b.service.target) ∧
      (all.map (fun a => a.service.target)).prod=p ∧
      (∀ i, (all.map (fun a => a.displacement i)).sum=d i) ∧
      (∀ a ∈ all, (arcCoordinate dir start a.service.port).val ≤ (arcCoordinate dir start finish).val) ∧
      ((all.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ) ≤
        (∑ i : Fin n, |d i|)-2*((cycles dir).length : ℤ)-portLoad d (ports dir) := by
    intro dir
    obtain ⟨r,hr,hp⟩ := hincident dir
    exact ZeroGap.arc_packet_service_family_load hn hd hshort hroot hcover dir start finish
      (cycles dir) (hcycles dir) (hout dir) (hcycleports dir) r (ports dir) hr hp (hport dir)
  choose services hdis ht hdisp hports hrot using hfamilies
  apply two_arc_service_word hn hd hm 0 start finish hne services hdis ht hdisp hports
  have hleft := hrot true
  have hright := hrot false
  omega

theorem two_arc_core_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (start finish : Fin n)
    (hboth : ∀ dir : Bool, ∃ r : Fin n, PrunedLift.InCore p d 0 r ∧
      (arcCoordinate dir start r).val ≤ (arcCoordinate dir start finish).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  by_cases heq : start=finish
  · subst finish
    obtain ⟨r,hr,hpos⟩ := hboth true
    have he : r=start := by
      apply sub_eq_zero.mp
      apply Fin.ext
      simp only [arcCoordinate,ite_true,sub_self,Fin.val_zero] at hpos
      simpa only [Fin.val_zero] using (show (r-start).val=0 by omega)
    subst r
    have hshort (i : Fin n) : |d i| < (n : ℤ) := by
      have := FiniteWindow.majorized_short hd hm i
      have := abs_nonneg (d i)
      omega
    exact FiniteGaps.packet_vertex_sharp_word hn hd hm start
      (PrunedLift.nonzero_reachable hd hshort 0 start hroot hr.1)
      (PrunedLift.packet_cover_reroot p d 0 start hcover hr.1 hr.2)
  · apply two_arc_incident_packet_word hn hd hm hroot hcover start finish heq
    intro dir
    obtain ⟨r,hr,hpos⟩ := hboth dir
    exact ⟨r,⟨r,hr,Or.inl rfl⟩,hpos⟩

#print axioms two_arc_incident_packet_word
#print axioms two_arc_core_word
end LRX.RotationWords

module

public import LRX.ActualPeakFourSizes

@[expose] public section

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A moving vertex in a component of at most two positions is already
in an original source packet. No filling vertex can remain there. -/
theorem two_vertex_component_source (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (i : Fin n) (hi : p.symm i ≠ i)
    (hsmall : (componentSet p i).card ≤ 2) : i ∈ sourcePackets p := by
  classical
  by_contra hout
  obtain ⟨r,hr,hri⟩ := component_roots_cover p i hi
  have hrs : r ∈ sourcePackets p := component_universal_source p r (component_root_moved p r hr)
    (fun x hx hp => component_root_reaches hn p hm r hr x hx hp)
  have hprev : p.symm i ∉ sourcePackets p := by
    intro hh
    apply hout
    apply source_packets_predecessor_closed p i (p.symm i) _ hh
    exact Or.inl ((Equiv.Perm.SameCycle.refl p.symm i).apply_right)
  have hroot : r ∈ componentSet p i := (CycleFootprint.mem_component _ _ _).mpr
    (CycleFootprint.load_path_symm _ hri)
  have hii : i ∈ componentSet p i := (CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hip : p.symm i ∈ componentSet p i := by
    have hh := CycleFootprint.component_invariant hd i (p.symm i)
    rw [Equiv.apply_symm_apply] at hh
    exact hh.mp hii
  have hriNe : r ≠ i := fun h => hout (h ▸ hrs)
  have hrpNe : r ≠ p.symm i := fun h => hprev (h ▸ hrs)
  have hcard : ({r,i,p.symm i} : Finset (Fin n)).card=3 := by
    simp [hriNe,hrpNe,Ne.symm hi]
  have hsub : ({r,i,p.symm i} : Finset (Fin n)) ⊆ componentSet p i := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hh := Finset.card_le_card hsub
  omega

#print axioms two_vertex_component_source
end LRX.FiniteCuts

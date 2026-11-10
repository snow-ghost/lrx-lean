module

public import LRX.TwoArcPacketWord

@[expose] public section

namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def IncidentPacketPort (p : State n) (d : Fin n → ℤ) (root port : Fin n) : Prop :=
  ∃ r, PrunedLift.InCore p d root r ∧ (port=r ∨ port+1=r)

theorem positive_root_incident_port (p : State n) (d : Fin n → ℤ) (hroot : d 0 ≠ 0) :
    ∃ port : Fin n, AdmissiblePacketPort p d 0 port := by
  have hcore : PrunedLift.InCore p d 0 0 := ⟨Relation.ReflTransGen.refl,Relation.ReflTransGen.refl⟩
  rcases lt_or_gt_of_ne hroot with hneg | hpos
  · have hp := CycleFootprint.arrow_edge_positive d 0 (-1) (by simp only [Fin.val_zero,Nat.cast_zero,zero_add]; omega)
      (by simp only [Fin.val_zero,Nat.cast_zero,zero_add]; omega)
    refine ⟨(-1 : Fin n),0,hcore,Or.inr (by ring),?_⟩
    simpa using hp
  · have hp := CycleFootprint.arrow_edge_positive d 0 0 (by simp) (by simp only [Fin.val_zero,Nat.cast_zero,zero_add]; omega)
    exact ⟨0,0,hcore,Or.inl rfl,by simpa using hp⟩

theorem incident_arc_ports_with_saving {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hroot : d 0 ≠ 0) (start finish : Fin n) (hne : start ≠ finish)
    (hboth : ∀ dir : Bool, ∃ port : Fin n, IncidentPacketPort p d 0 port ∧
      (arcCoordinate dir start port).val ≤ (arcCoordinate dir start finish).val) :
    ∃ ports : Bool → Fin n,
      (∀ dir, IncidentPacketPort p d 0 (ports dir)) ∧
      (∀ dir, (arcCoordinate dir start (ports dir)).val ≤ (arcCoordinate dir start finish).val) ∧
      2 ≤ portLoad d (ports true)+portLoad d (ports false) := by
  classical
  choose base hb hr using hboth
  obtain ⟨good,r,hcore,hincident,hpos⟩ := positive_root_incident_port p d hroot
  have hgood : IncidentPacketPort p d 0 good := ⟨r,hcore,hincident⟩
  have hload := positive_port_load_ge_two hd good hpos
  by_cases hg : (arcCoordinate true start good).val ≤ (arcCoordinate true start finish).val
  · refine ⟨fun dir => if dir then good else base false,?_,?_,?_⟩
    · intro dir; cases dir
      · exact hb false
      · exact hgood
    · intro dir; cases dir
      · exact hr false
      · exact hg
    · have hb0 := port_load_nonneg d (base false)
      simp only [ite_true,Bool.false_eq_true,ite_false]
      omega
  · have hg' := arc_not_forward_is_reverse start finish good hne hg
    refine ⟨fun dir => if dir then base true else good,?_,?_,?_⟩
    · intro dir; cases dir
      · exact hgood
      · exact hb true
    · intro dir; cases dir
      · exact hg'
      · exact hr true
    · have hb0 := port_load_nonneg d (base true)
      simp only [ite_true,Bool.false_eq_true,ite_false]
      omega

#print axioms positive_root_incident_port
#print axioms incident_arc_ports_with_saving
end LRX.RotationWords

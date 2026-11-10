import LRX.MaximumCutRoutes

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem disconnected_load_zero_port (d : Fin n → ℤ) (a b : Fin n)
    (hnot : ¬CycleFootprint.LoadPath d a b) : ∃ z : Fin n, portLoad d z=0 := by
  classical
  by_contra hh
  push_neg at hh
  have hpos (z : Fin n) : 0 < portLoad d z := by have := port_load_nonneg d z; have := hh z; omega
  exact hnot (CycleFootprint.positive_load_path d hpos a b)

theorem phase_zero_cut_multiple_components (p : State n) (c : Fin n) (d : Fin n → ℤ)
    (hd : AffineLift.IsLift p (c : ℤ) d) (a b z : Fin n)
    (ha : d a ≠ 0) (hb : d b ≠ 0) (hnot : ¬CycleFootprint.LoadPath d a b) (hz : portLoad d z=0) :
    1 < (componentRoots (localTarget p c (z+1))).card := by
  classical
  let r := z+1
  let q := localTarget p c r
  have hcan := phase_zero_cut_canonical c z hd hz
  change localDisplacement d r=displacement q.symm at hcan
  have hm (x : Fin n) (hx : d x ≠ 0) : q.symm (x-r) ≠ x-r := by
    intro he
    have hh := congrFun hcan (x-r)
    simp only [localDisplacement,AffineLift.rotation_power_apply,Fin.cast_val_eq_self,sub_add_cancel,
      displacement,he,sub_self] at hh
    exact hx hh
  obtain ⟨u,hu,hua⟩ := component_roots_cover q (a-r) (hm a ha)
  obtain ⟨v,hv,hvb⟩ := component_roots_cover q (b-r) (hm b hb)
  have huv : u ≠ v := by
    intro he
    have hp := (CycleFootprint.load_path_symm _ hua).trans (he ▸ hvb)
    rw [← hcan] at hp
    have hh := (load_path_recenter d r (a-r) (b-r)).mp hp
    exact hnot (by simpa only [sub_add_cancel] using hh)
  exact Finset.one_lt_card.mpr ⟨u,hu,v,hv,huv⟩

#print axioms phase_zero_cut_multiple_components
end LRX.FiniteCuts

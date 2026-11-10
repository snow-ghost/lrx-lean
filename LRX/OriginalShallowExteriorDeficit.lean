module

public import LRX.ActualShallowExteriorDeficit

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The actual zero cut at a component boundary preserves total cycle defect. -/
theorem component_cut_cycle_defect (p : State n) (root : Fin n) :
    cycleDefect (localTarget p 0 (componentLeft p root))=cycleDefect p := by
  let q := localTarget p 0 (componentLeft p root)
  have hmass := component_cut_displacement_mass p root
  rw [displacement_mass_inverse,displacement_mass_inverse] at hmass
  have hI := inversion_number_zero_recenter p (componentLeft p root-1) (component_left_port_zero p root)
  simp only [sub_add_cancel] at hI
  have hs : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  have hk : q.cycleFactorsFinset.card=p.cycleFactorsFinset.card := by
    have hh := congrArg Multiset.card
      (Equiv.Perm.cycleType_conj (σ := p) (τ := (rotation (componentLeft p root))⁻¹))
    dsimp only [q]
    rw [local_target_zero]
    simpa only [Equiv.Perm.cycleType,Multiset.card_map,Finset.card_val,inv_inv] using hh
  change cycleDefect q=cycleDefect p
  unfold cycleDefect
  rw [hmass,hI,hs,hk]

#print axioms component_cut_cycle_defect
end LRX.FiniteCuts

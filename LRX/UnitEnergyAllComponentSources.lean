module

public import LRX.PrefixSaturatedDefectNoFillings
public import LRX.FillingCycleCountRecenter
public import LRX.ComponentCutSingletonCount

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The actual saturated unit-energy structure has no non-source moving
positions in any nontrivial component. The normalization data are derived. -/
theorem unit_energy_all_component_sources (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (hf : n-p.support.card=2)
    (he : canonicalEnergyDeficit p=1) (hZ : cycleDefect p=4)
    (hfixed : isolatedVertices p=p.supportᶜ)
    (hK : p.cycleFactorsFinset.card=(fillingCycles p).card+4) :
    ∀ root : Fin n, 2 ≤ (componentSet p root).card →
      ∀ i ∈ componentSet p root, i ∈ sourcePackets p := by
  classical
  intro root hsize
  let r := componentLeft p root
  let q := localTarget p 0 r
  have hcan := component_cut_canonical_displacement p root
  change localDisplacement (displacement p.symm) r=displacement q.symm at hcan
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← hcan]
    exact majorized_recenter hmaj r
  have hroots : (componentRoots q).card=(componentRoots p).card := by
    rw [component_roots_card_eq_blocks,component_roots_card_eq_blocks]
    exact component_cut_nontrivial_count p root
  have hqc : (componentRoots q).card=1+1 := by omega
  have hs : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using
      (Equiv.Perm.card_support_conj (σ := (rotation r)⁻¹) (τ := p))
  have hqf : n-q.support.card=2 := by omega
  have hqe : canonicalEnergyDeficit q=1 := by
    dsimp only [q,r]
    unfold canonicalEnergyDeficit
    rw [component_cut_displacement_mass]
    exact he
  have hqZ : cycleDefect q=4 := by
    dsimp only [q,r]
    rw [component_cut_cycle_defect,hZ]
  have hiso := component_cut_isolated_card p root
  change (isolatedVertices q).card=(isolatedVertices p).card at hiso
  have hisop : (isolatedVertices p).card=2 := by
    rw [hfixed,Finset.card_compl,Fintype.card_fin,hf]
  have hsub : isolatedVertices q ⊆ q.supportᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (isolated_vertex_fixed q i hi))
  have hqfixed : isolatedVertices q=q.supportᶜ := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_compl,Fintype.card_fin]
    omega)
  have hcycles := cycle_factor_count_recenter p r
  change q.cycleFactorsFinset.card=p.cycleFactorsFinset.card at hcycles
  have hfill := filling_cycle_count_recenter p r hcan
  change (fillingCycles q).card=(fillingCycles p).card at hfill
  have hqK : q.cycleFactorsFinset.card=(fillingCycles q).card+4 := by omega
  have hgeom := unit_energy_defect_four_component_windows q hqm hqc hqf hqe hqZ hqfixed
  have hPackets := source_packet_cycles_exact_two_of_four hn q hqm hqc hgeom hqK
  have hPacketDefects := exact_defect_two_windows_packet_defect_eq_two q hqm hgeom hPackets
  have hzero : (componentSet q 0).card=(componentSet p root).card := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have heq : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← heq] at hh
  have hcover := unit_energy_prefix_sources_cover q hqm hqc (by omega) hqf hqe hqfixed hgeom hPacketDefects
  intro i hi
  have hpath := (CycleFootprint.load_path_symm _ (component_left_path p root)).trans
    ((CycleFootprint.mem_component _ _ _).mp hi)
  have hqpath := (load_path_recenter (displacement p.symm) r 0 (i-r)).mpr (by
    simpa only [zero_add,sub_add_cancel] using hpath)
  rw [hcan] at hqpath
  have hiq : i-r ∈ componentSet q 0 := (CycleFootprint.mem_component _ _ _).mpr hqpath
  have hsource := (source_packets_recenter p r hcan (i-r)).mp (hcover (i-r) hiq)
  simpa only [RotationWords.rotation,AffineLift.rotation_power_apply,Fin.cast_val_eq_self,sub_add_cancel] using hsource

#print axioms unit_energy_all_component_sources
end LRX.FiniteCuts

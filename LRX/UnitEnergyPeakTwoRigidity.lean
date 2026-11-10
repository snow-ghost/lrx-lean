import LRX.SignedSelectionDeficit
import LRX.ZeroEnergyPeakRigidity
import LRX.UnitEnergyNoUnitArrows
import LRX.EventDefectParity

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem two_component_unit_energy_bridge_two_structure (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (hf : n-p.support.card=2)
    (he : canonicalEnergyDeficit p=1)
    (hB : bridgeBudget (componentBridges p hc)=2) :
    isolatedVertices p=p.supportᶜ ∧ 4 ≤ cycleDefect p := by
  classical
  have hsub : isolatedVertices p ⊆ p.supportᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (isolated_vertex_fixed p i hi))
  have hcard : p.supportᶜ.card=2 := by simpa only [Finset.card_compl,Fintype.card_fin] using hf
  have hbudget := two_component_twice_bridge_budget hn p hmax hc
  rw [hB] at hbudget
  have hfixed : isolatedVertices p=p.supportᶜ := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨hfixed,two_component_nonunit_defect_ge_four p hc ?_⟩
  intro root hroot i hi
  have him := component_support_of_all_fixed_isolated p hfixed root hroot hi
  have hmove : p.symm i ≠ i := (mem_support_inverse p i).mp him
  have hnon : displacement p.symm i ≠ 0 := by
    intro hz
    apply hmove
    apply Fin.ext
    unfold displacement at hz
    omega
  have hunit := unit_energy_two_fixed_no_unit_arrow p hmaj hf he i
  have hapos := abs_pos.mpr hnon
  omega

/-- The unit-energy peak has only two exact structural possibilities.
The budget-one possibility has zero defect and admits existing shell routing. -/
theorem two_component_unit_energy_peak_two_rigidity (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (hpos : 1 ≤ peakExcess p hc)
    (hf : n-p.support.card=2) (he : canonicalEnergyDeficit p=1)
    (hU : sourceHalfPeak p=2) :
    (bridgeBudget (componentBridges p hc)=1 ∧ cycleDefect p=0 ∧ peakExcess p hc=1) ∨
    (bridgeBudget (componentBridges p hc)=2 ∧ cycleDefect p=4 ∧ peakExcess p hc=1 ∧
      isolatedVertices p=p.supportᶜ) := by
  let C := (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
    (p.support.card : ℤ)+fillingHalfPeakSum p
  have hweak := aggregate_source_filling_defect (by omega) p hmaj (by omega)
  have hstrong := aggregate_source_filling_strong_defect (by omega) p hmaj (by omega)
  dsimp only at hstrong
  rw [hc] at hweak hstrong
  norm_num only [Nat.cast_add,Nat.cast_one] at hweak hstrong
  have hw : -2 ≤ C := hweak
  have hs : cycleDefect p-4 ≤ 2*C := by
    simpa only [cycleDefect,displacement_mass_inverse,C] using hstrong
  have hnon : 0 ≤ cycleDefect p := by
    have hh := finite_depth_rank p
    unfold cycleDefect
    omega
  have hact := unpaid_two_component_activity (by omega) p hmaj hmax hc hpos
  dsimp only at hact
  rw [hf,hU] at hact
  have hn4 := unit_energy_reserve_size_mod_four p he
  have hN := choose_two_half_identity n
  have hsize : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by omega
  have hsupport : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  have hfixed : (p.support.card : ℤ)=(n : ℤ)-2 := by omega
  have hprice : peakExcess p hc=2*(bridgeBudget (componentBridges p hc) : ℤ)-3-C := by
    unfold peakExcess
    rw [hU]
    dsimp only [C,canonicalEnergyDeficit] at *
    norm_num only [Nat.cast_ofNat]
    nlinarith only [he,hN,hsize,hfixed]
  have hB : bridgeBudget (componentBridges p hc)=1 ∨ bridgeBudget (componentBridges p hc)=2 := by
    dsimp only [canonicalEnergyDeficit] at he
    omega
  rcases hB with hB | hB
  · left
    exact ⟨hB,by omega,by omega⟩
  · obtain ⟨hfixed,hdef⟩ := two_component_unit_energy_bridge_two_structure (by omega) p hmaj hmax hc hf he hB
    right
    exact ⟨hB,by omega,by omega,hfixed⟩

#print axioms two_component_unit_energy_bridge_two_structure
#print axioms two_component_unit_energy_peak_two_rigidity
end LRX.FiniteCuts

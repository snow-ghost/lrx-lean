module

public import LRX.TwoWindowCycleDefect

@[expose] public section

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Exact two-component geometry upgrades the local unit lemma to total
defect at least four. All windows and their coverage are extracted internally. -/
theorem two_component_nonunit_defect_ge_four (p : State n)
    (hc : (componentRoots p).card=1+1)
    (hno : ∀ root : Fin n, 2 ≤ (componentSet p root).card →
      ∀ i ∈ componentSet p root, 2 ≤ |displacement p.symm i|) :
    4 ≤ cycleDefect p := by
  classical
  obtain ⟨a,b,hab,hroots⟩ := Finset.card_eq_two.mp (show (componentRoots p).card=2 by omega)
  have ha : a ∈ componentRoots p := by rw [hroots]; simp
  have hb : b ∈ componentRoots p := by rw [hroots]; simp
  have hac := component_root_card_ge_two p a ha
  have hbc := component_root_card_ge_two p b hb
  obtain ⟨A,hAs,hAw,hAm,hAZ⟩ := exists_nonunit_component_defect p a hac (hno a hac)
  obtain ⟨B,hBs,hBw,hBm,hBZ⟩ := exists_nonunit_component_defect p b hbc (hno b hbc)
  have hap : A.Apart B := by
    intro i hiA hiB
    have hai := (CycleFootprint.mem_component _ _ _).mp ((hAw i).mp hiA)
    have hbi := (CycleFootprint.mem_component _ _ _).mp ((hBw i).mp hiB)
    exact hab (component_roots_unique p ha hb (hai.trans (CycleFootprint.load_path_symm _ hbi)))
  have hcover (i : Fin n) (hi : p.symm i ≠ i) : Contains A.window i ∨ Contains B.window i := by
    obtain ⟨r,hr,hri⟩ := component_roots_cover p i hi
    rw [hroots] at hr
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact Or.inl ((hAw i).mpr ((CycleFootprint.mem_component _ _ _).mpr hri))
    · exact Or.inr ((hBw i).mpr ((CycleFootprint.mem_component _ _ _).mpr hri))
  have hprod := two_matched_windows_product p.symm A B hap hAm hBm hcover
  have hsum := cycle_defect_two_windows A B hap
  rw [← hprod,cycle_defect_inverse] at hsum
  change 2 ≤ cycleDefect A.filling at hAZ
  change 2 ≤ cycleDefect B.filling at hBZ
  omega

/-- Total actual defect in the remaining unit-energy high-peak regime. -/
theorem two_component_unit_energy_high_peak_defect_four (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (hpos : 1 ≤ peakExcess p hc)
    (hf : n-p.support.card=2)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=1)
    (hU : 3 ≤ sourceHalfPeak p) : 4 ≤ cycleDefect p := by
  have hh := two_component_unit_energy_high_peak_structure hn p hmaj hmax hc hpos hf he hU
  exact two_component_nonunit_defect_ge_four p hc hh.2.2

#print axioms two_component_nonunit_defect_ge_four
#print axioms two_component_unit_energy_high_peak_defect_four
end LRX.FiniteCuts

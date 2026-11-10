import LRX.UnitEnergyPeakTwoRigidity

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The two actual nontrivial components have an exact factorization
into disjoint matching windows with defect two each. -/
def ExactDefectTwoComponentWindows (p : State n) : Prop :=
    ∃ (a b : Fin n) (A B : FillingWindow n),
      a ≠ b ∧ componentRoots p={a,b} ∧
      A.size=(componentSet p a).card ∧ B.size=(componentSet p b).card ∧
      (∀ i, Contains A.window i ↔ i ∈ componentSet p a) ∧
      (∀ i, Contains B.window i ↔ i ∈ componentSet p b) ∧
      A.Apart B ∧ A.Matches p.symm ∧ B.Matches p.symm ∧
      p.symm=permutation A.window A.filling*permutation B.window B.filling ∧
      cycleDefect A.filling=2 ∧ cycleDefect B.filling=2

theorem two_component_nonunit_defect_four_windows (p : State n)
    (hc : (componentRoots p).card=1+1)
    (hZ : cycleDefect p=4)
    (hno : ∀ root : Fin n, 2 ≤ (componentSet p root).card →
      ∀ i ∈ componentSet p root, 2 ≤ |displacement p.symm i|) :
    ExactDefectTwoComponentWindows p := by
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
  exact ⟨a,b,A,B,hab,hroots,hAs,hBs,hAw,hBw,hap,hAm,hBm,hprod,by omega,by omega⟩

/-- All hypotheses of the exact window decomposition follow from the
remaining unit-energy structural case, with no supplied local certificates. -/
theorem unit_energy_defect_four_component_windows (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (hf : n-p.support.card=2)
    (he : canonicalEnergyDeficit p=1) (hZ : cycleDefect p=4)
    (hfixed : isolatedVertices p=p.supportᶜ) : ExactDefectTwoComponentWindows p := by
  apply two_component_nonunit_defect_four_windows p hc hZ
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

#print axioms two_component_nonunit_defect_four_windows
#print axioms unit_energy_defect_four_component_windows
end LRX.FiniteCuts

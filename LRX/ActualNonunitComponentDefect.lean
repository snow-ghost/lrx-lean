module

public import LRX.ZeroDefectUnitArrow
public import LRX.UnitEnergyNoUnitArrows

@[expose] public section

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The unit-defect lemma applies to an actual invariant filling by matching
its physical arrows, without assuming local full support separately. -/
theorem matched_nonunit_window_defect (p : State n) (A : FillingWindow n)
    (hsize : 0 < A.size) (hm : A.Matches p)
    (hno : ∀ i, Contains A.window i → 2 ≤ |displacement p i|) :
    2 ≤ (∑ i, |displacement A.filling i|)-(inversionNumber A.filling : ℤ)-
      (A.filling.support.card : ℤ)+(A.filling.cycleFactorsFinset.card : ℤ) := by
  classical
  letI : NeZero A.size := ⟨by omega⟩
  have hdisp (i : Fin A.size) : displacement p (embed A.window i)=displacement A.filling i := by
    unfold displacement
    rw [hm i]
    simp only [embed,Nat.cast_add]
    omega
  have hmin (i : Fin A.size) : 2 ≤ |displacement A.filling i| := by
    rw [← hdisp]
    exact hno _ (contains_embed A.window i)
  have hfull : A.filling.support=Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    apply Equiv.Perm.mem_support.mpr
    intro hh
    have h := hmin i
    simp only [displacement,hh,sub_self,abs_zero] at h
    omega
  exact full_support_nonunit_defect_ge_two A.filling hfull (fun i => by have := hmin i; omega)

/-- An actual component all of whose arrows have length at least two admits
its canonical window with cycle defect at least two. -/
theorem exists_nonunit_component_defect (p : State n) (root : Fin n)
    (hc : 2 ≤ (componentSet p root).card)
    (hno : ∀ i ∈ componentSet p root, 2 ≤ |displacement p.symm i|) :
    ∃ A : FillingWindow n, A.size=(componentSet p root).card ∧
      (∀ i, Contains A.window i ↔ i ∈ componentSet p root) ∧ A.Matches p.symm ∧
      2 ≤ (∑ i, |displacement A.filling i|)-(inversionNumber A.filling : ℤ)-
        (A.filling.support.card : ℤ)+(A.filling.cycleFactorsFinset.card : ℤ) := by
  obtain ⟨A,hsize,hwhere,hm⟩ := exists_component_filling_window p root
  exact ⟨A,hsize,hwhere,hm,matched_nonunit_window_defect p.symm A (by omega) hm
    (fun i hi => hno i ((hwhere i).mp hi))⟩

#print axioms matched_nonunit_window_defect
#print axioms exists_nonunit_component_defect
end LRX.FiniteCuts

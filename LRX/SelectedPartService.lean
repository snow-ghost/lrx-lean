import LRX.CyclePartSelection
import LRX.PeriodicRemainingService

/-! Exact removal and service of a selected finite part of a periodic lift. -/
namespace LRX.CyclePart
open scoped BigOperators
open RotationWords
variable {n : ℕ}

theorem displacement_split (selected : State n) (d : Fin n → ℤ)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ)) (i : Fin n) :
    PrunedLift.displacement selected.supportᶜ d i+
      ((selected.symm i : ℤ)-(i : ℤ))=d i := by
  by_cases hi : i ∈ selected.support
  · simp [PrunedLift.displacement,hi,hfinite i hi]
  · have hf : selected i=i := Equiv.Perm.notMem_support.mp hi
    have hfi : selected.symm i=i := by apply selected.injective; simpa using hf.symm
    simp [PrunedLift.displacement,hi,hfi]

theorem absolute_split (selected : State n) (d : Fin n → ℤ)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ)) (i : Fin n) :
    |PrunedLift.displacement selected.supportᶜ d i|+
      |(selected.symm i : ℤ)-(i : ℤ)|=|d i| := by
  by_cases hi : i ∈ selected.support
  · simp [PrunedLift.displacement,hi,hfinite i hi]
  · have hf : selected i=i := Equiv.Perm.notMem_support.mp hi
    have hfi : selected.symm i=i := by apply selected.injective; simpa using hf.symm
    simp [PrunedLift.displacement,hi,hfi]

theorem mass_split (selected : State n) (d : Fin n → ℤ)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ)) :
    (∑ i, |PrunedLift.displacement selected.supportᶜ d i|)+
      (∑ i, |(selected.symm i : ℤ)-(i : ℤ)|)=∑ i, |d i| := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => absolute_split selected d hfinite i)

variable [NeZero n]

#print axioms displacement_split
#print axioms mass_split
end LRX.CyclePart

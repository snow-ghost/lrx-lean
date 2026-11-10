module

public import LRX.SourceReversalComponentEquality
public import LRX.ComponentInversionBudget

@[expose] public section

namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Exact joint price needs no shortness or width bound. -/
theorem reverse_windows_inversion_price (As : List (FillingWindow n)) (p : State n)
    (hmatch : ∀ A ∈ As, A.Matches p) (hapart : As.Pairwise FillingWindow.Apart) :
    (inversionNumber (reverseWindows As p) : ℤ) =
      (inversionNumber p : ℤ) + (As.map FillingWindow.deficit).sum := by
  induction As generalizing p with
  | nil => simp [reverseWindows]
  | cons A As ih =>
    have hm := hmatch A (List.mem_cons_self ..)
    obtain ⟨hA,hAs⟩ := List.pairwise_cons.mp hapart
    have hmAs : ∀ B ∈ As, B.Matches (A.reverseIn p) := by
      intro B hB
      exact FillingWindow.matches_after_apart A B p (hA B hB)
        (hmatch B (List.mem_cons_of_mem _ hB))
    have htail := ih (A.reverseIn p) hmAs hAs
    have hstep := replace_inversion_price A.window p A.filling Fin.revPerm hm
    rw [inversion_number_reversal] at hstep
    have hstep' : (inversionNumber (A.reverseIn p) : ℤ)+(inversionNumber A.filling : ℤ) =
        (inversionNumber p : ℤ)+(A.size.choose 2 : ℤ) := by exact_mod_cast hstep
    simp only [reverseWindows,List.map_cons,List.sum_cons]
    rw [show A.deficit = (A.size.choose 2 : ℤ)-(inversionNumber A.filling : ℤ) from rfl]
    omega
end LRX.FiniteWindow

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow
variable {n : ℕ} [NeZero n]

/-- Retain individual component sizes in the inversion incidence count. -/
theorem inversion_budget_of_component_sizes (p : State n) :
    2*(inversionNumber p : ℤ) ≤ ∑ i : Fin n, (((componentSet p i).card : ℤ)-1) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => inversion_incidence_le_component p i)
  simp only [Finset.sum_add_distrib] at h
  have he : (∑ i : Fin n, ∑ j : Fin n, inversionIndicator p j i) =
      (∑ i : Fin n, ∑ j : Fin n, inversionIndicator p i j) := Finset.sum_comm
  rw [he,sum_inversion_indicator] at h
  simpa only [← two_mul] using h

#print axioms inversion_budget_of_component_sizes
end LRX.FiniteCuts

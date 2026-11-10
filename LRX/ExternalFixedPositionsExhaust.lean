module

public import LRX.WindowFamilyFixedCount

@[expose] public section

namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ}

/-- A matching disjoint family containing the full fixed count contains
 every fixed position of the original permutation. -/
theorem full_fixed_count_family_moves_outside (As : List (FillingWindow n)) (p : State n)
    (hm : ∀ A ∈ As, A.Matches p) (hd : As.Pairwise FillingWindow.Apart)
    (hf : (As.map (fun A => A.size-A.filling.support.card)).sum=n-p.support.card)
    (i : Fin n) (hi : i ∉ familyPositions As) : p i ≠ i := by
  classical
  let F := familyPositions As \ p.support
  let G := Finset.univ \ p.support
  have hsub : F ⊆ G := Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _)
  have hF : F.card=n-p.support.card := (window_family_fixed_count As p hm hd).trans hf
  have hG : G.card=n-p.support.card := by
    dsimp only [G]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  have hEq : F=G := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro hfix
  have hiG : i ∈ G := by
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_univ _,fun h => Equiv.Perm.mem_support.mp h hfix⟩
  rw [← hEq] at hiG
  exact hi (Finset.mem_sdiff.mp hiG).1

#print axioms full_fixed_count_family_moves_outside
end LRX.FiniteWindow

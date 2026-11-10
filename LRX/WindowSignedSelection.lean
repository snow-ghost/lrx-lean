module

public import LRX.SignedSelectionDeficit
public import LRX.WindowSelectedEnergy

@[expose] public section

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Selected local arrows are embedded into the original permutation injectively. -/
theorem matching_window_selected_mass (A : FillingWindow n) (p : State n)
    (hm : A.Matches p) (S : Finset (Fin A.size)) :
    (S.image (embed A.window)).card=S.card ∧
    (∑ i ∈ S.image (embed A.window), |displacement p i|)=
      ∑ i ∈ S, |displacement A.filling i| := by
  classical
  refine ⟨Finset.card_image_of_injective _ (embed_injective A.window),?_⟩
  rw [Finset.sum_image (fun i _ j _ h => embed_injective A.window h)]
  apply Finset.sum_congr rfl
  intro i _
  rw [matching_window_displacement A.window p A.filling hm]

#print axioms matching_window_selected_mass
end LRX.FiniteWindow

import LRX.ActualExteriorPairSigns

namespace LRX.FiniteCuts
open FiniteWindow

/-- An overapproximation containing every local permutation of sizes 2..5. -/
def smallExteriorCatalogue : List (Σ b : ℕ, State b) :=
  (List.range 4).flatMap fun j =>
    (permsOfList (List.finRange (j+2))).map fun σ => ⟨j+2,σ⟩

theorem local_map_mem_catalogue (b : ℕ) (σ : State b) (hb0 : 2 ≤ b) (hb1 : b ≤ 5) :
    (⟨b,σ⟩ : Σ b : ℕ, State b) ∈ smallExteriorCatalogue := by
  have hp : σ ∈ permsOfList (List.finRange b) :=
    mem_permsOfList_of_mem (fun i _ => by simp)
  have he : b-2+2=b := by omega
  unfold smallExteriorCatalogue
  apply List.mem_flatMap.mpr
  refine ⟨b-2,List.mem_range.mpr (by omega),?_⟩
  rw [he]
  exact List.mem_map.mpr ⟨σ,hp,rfl⟩

theorem catalogue_member_size (z : Σ b : ℕ, State b) (hz : z ∈ smallExteriorCatalogue) :
    2 ≤ z.1 ∧ z.1 ≤ 5 := by
  obtain ⟨j,hj,hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨σ,_,rfl⟩ := List.mem_map.mp hz
  have hj4 := List.mem_range.mp hj
  dsimp only
  omega

#print axioms local_map_mem_catalogue
#print axioms catalogue_member_size
end LRX.FiniteCuts

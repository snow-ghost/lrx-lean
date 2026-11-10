import LRX.WindowFamilySelectedEnergy

/-! Exact local energy sums retain the sharper balanced-subset square filter. -/
namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n : ℕ}

theorem window_family_selected_mass (As : List (FillingWindow n)) (p : State n)
    (hm : ∀ A ∈ As, A.Matches p) (hd : As.Pairwise FillingWindow.Apart) :
    (∑ i ∈ familyPositions As, |displacement p i|)=
      (As.map (fun A => ∑ i, |displacement A.filling i|)).sum := by
  classical
  induction As with
  | nil => simp [familyPositions]
  | cons A As ih =>
    obtain ⟨hA,hAs⟩ := List.pairwise_cons.mp hd
    have hmA := hm A (List.mem_cons_self ..)
    have hmAs := fun B hB => hm B (List.mem_cons_of_mem _ hB)
    have hdis : Disjoint (windowPositions A.window) (familyPositions As) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      obtain ⟨B,hB,hBi⟩ := (mem_family_positions As i).mp hj
      exact hA B hB i (Finset.mem_filter.mp hi).2 hBi
    rw [familyPositions,Finset.sum_union hdis,sum_window_positions,ih hmAs hAs]
    simp only [List.map_cons,List.sum_cons]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [matching_window_displacement A.window p A.filling hmA]

/-- The exact selected energy, rather than its squared-width relaxation. -/
theorem window_family_exact_energy_deficit (As : List (FillingWindow n)) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p))
    (hm : ∀ A ∈ As, A.Matches p) (hd : As.Pairwise FillingWindow.Apart) :
    let V := (As.map (fun A => A.size)).sum
    let a := ((familyPositions As ∪ p.support)ᶜ).card
    let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p i|)
    ((V : ℤ)+(a : ℤ))^2 ≤
      4*(eps+(As.map (fun A => ∑ i, |displacement A.filling i|)).sum)+(n%2 : ℕ) := by
  obtain ⟨hcard,hbalance,_⟩ := window_family_selected_energy As p hm hd
  have hh := balanced_subset_area_deficit p hmaj (familyPositions As) hbalance
  rw [hcard,window_family_selected_mass As p hm hd] at hh
  exact hh

#print axioms window_family_selected_mass
#print axioms window_family_exact_energy_deficit
end LRX.FiniteWindow

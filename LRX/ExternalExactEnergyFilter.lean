import LRX.ActualPeakProfileFilters

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

/-- Apply the balanced subset bound to exterior windows alone. -/
theorem suffix_exact_energy_filter (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (L : ℕ) (hLn : L ≤ n)
    (hcut : ∀ i : Fin n, (p i).val<L ↔ i.val<L) :
    let t := (nontrivialSuffixComponents p L).card
    let v := ∑ C ∈ nontrivialSuffixComponents p L, C.card
    let eps : ℤ := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    (v : ℤ)^2 ≤ 4*eps+(n%2 : ℕ)+2*(exteriorSquareBound t v-(v%2 : ℕ)) := by
  classical
  let As := suffixComponentFamily p L
  let v := ∑ C ∈ nontrivialSuffixComponents p L, C.card
  let a := ((familyPositions As ∪ Equiv.Perm.support p.symm)ᶜ).card
  obtain ⟨hm,hd⟩ := area_window_family_spec p L hLn hcut
  have hmext : ∀ A ∈ As, A.Matches p.symm :=
    fun A hA => hm A (List.mem_append_right _ hA)
  have hdext : As.Pairwise FillingWindow.Apart := (List.pairwise_append.mp hd).2.1
  have he := window_family_exact_energy_deficit As p.symm hmaj hmext hdext
  have hv := suffix_component_family_size_sum p L
  change ((As.map (fun A => A.size)).sum)=v at hv
  dsimp only at he
  rw [hv] at he
  have hb := (suffix_component_square_energy_bounds p L).2
  change 2*(As.map (fun A => ∑ i, |displacement A.filling i|)).sum ≤
    exteriorSquareBound (nontrivialSuffixComponents p L).card v-(v%2 : ℕ) at hb
  have hva : 0 ≤ (v : ℤ)*(a : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  change ((v : ℤ)+(a : ℤ))^2 ≤ _ at he
  dsimp only
  nlinarith only [he,hb,hva,sq_nonneg (a : ℤ)]

/-- This further necessary scalar filter requires no unpaid-peak hypothesis. -/
theorem actual_peak_external_energy_filter (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (root : Fin n) :
    let r := actualPeakProfile p root
    r.exterior^2 ≤ 4*r.eps+r.parity+2*(r.E2-r.exterior%2) := by
  let q := localTarget p 0 (componentLeft p root)
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hLn : (componentSet p root).card ≤ n := by
    simpa using Finset.card_le_univ (componentSet p root)
  have h := suffix_exact_energy_filter q hqm (componentSet p root).card hLn
    (component_recenter_cut p root).1
  dsimp only at h ⊢
  have hmass : (∑ i, |displacement q.symm i|)=(∑ i, |displacement p.symm i|) :=
    component_cut_displacement_mass p root
  rw [hmass] at h
  rw [actual_peak_profile_E2,actual_peak_profile_exterior_mod]
  exact h

#print axioms suffix_exact_energy_filter
#print axioms actual_peak_external_energy_filter
end LRX.FiniteCuts

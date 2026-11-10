import LRX.StrongPacketEventBudget
import LRX.LinearSortingTrace

namespace LRX.ZeroGap
open scoped BigOperators
variable {n : ℕ} [NeZero n]

noncomputable def componentCycles (events : List (Event n)) (p : State n) (root : Fin n) :
    Finset (State n) := by
  classical
  exact p.cycleFactorsFinset.filter (fun c => c.support ⊆ eventComponent events root)

/-- A cycle meeting an event component is wholly contained in it. -/
theorem cycle_support_in_component (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p) (root : Fin n)
    (c : State n) (hc : c ∈ p.cycleFactorsFinset) (i : Fin n)
    (hi : i ∈ c.support) (hir : i ∈ eventComponent events root) :
    c.support ⊆ eventComponent events root := by
  intro j hj
  have hcycle := (cycle_root_same_cycle hc hi).symm.trans (cycle_root_same_cycle hc hj)
  exact (mem_eventComponent _ _ _).mpr (((mem_eventComponent _ _ _).mp hir).trans
    (cycle_event_reachable events p hprod hcycle.inv))

/-- Collapsing the roots of all cycles in one actual event component gives
its cycle-count lower bound directly in the global factorization defect. -/
theorem component_cycle_defect_budget (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p) (root : Fin n) :
    2*((componentCycles events p root).card : ℤ)-2 ≤
      (events.length : ℤ)-(p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ) := by
  classical
  let inside := componentCycles events p root
  let outside := p.cycleFactorsFinset \ inside
  let roots := p.supportᶜ.toList ++ outside.toList.map cycleRoot ++ [root]
  have hsub : inside ⊆ p.cycleFactorsFinset := Finset.filter_subset _ _
  have hparts : outside.card+inside.card=p.cycleFactorsFinset.card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hcover : ∀ i : Fin n, ∃ r ∈ roots, EventReaches events r i := by
    intro i
    by_cases hi : i ∈ eventComponent events root
    · refine ⟨root,?_,(mem_eventComponent _ _ _).mp hi⟩
      simp [roots]
    · by_cases hs : i ∈ p.support
      · obtain ⟨c,hc,hic⟩ := Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hs
        have hout : c ∈ outside := by
          apply Finset.mem_sdiff.mpr
          refine ⟨hc,?_⟩
          intro hcin
          exact hi ((Finset.mem_filter.mp hcin).2 hic)
        refine ⟨cycleRoot c,?_,cycle_event_reachable events p hprod (cycle_root_same_cycle hc hic).inv⟩
        simp only [roots,List.mem_append,List.mem_map,Finset.mem_toList,List.mem_singleton]
        exact Or.inl (Or.inr ⟨c,hout,rfl⟩)
      · refine ⟨i,?_,Relation.ReflTransGen.refl⟩
        simp only [roots,List.mem_append,Finset.mem_toList,Finset.mem_compl]
        exact Or.inl (Or.inl hs)
  have hbound := strong_root_cover_count events p hprod roots hcover
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  simp only [roots,List.length_append,List.length_map,Finset.length_toList,
    Finset.card_compl,Fintype.card_fin,List.length_singleton] at hbound
  change 2*(inside.card : ℤ)-2 ≤ _
  omega

#print axioms cycle_support_in_component
#print axioms component_cycle_defect_budget
end LRX.ZeroGap

import LRX.EventSublistRankBound
import LRX.SwapOrbitMerge
import LRX.EventTreeBranchCounts
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Edgewise path replacement extends to all event paths. -/
theorem event_reaches_of_edge_paths {xs ys : List (Event n)}
    (hstep : ∀ a b, EventEdge xs a b → EventReaches ys a b)
    {a b : Fin n} (h : EventReaches xs a b) : EventReaches ys a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact ih.trans (hstep _ _ he)

/-- A spanning forest is extracted as a subsequence of actual events.
Its product has one permutation orbit on each graph component. -/
theorem exists_spanning_event_forest (events : List (Event n)) :
    ∃ part : List (Event n), part.Sublist events ∧
      (∀ a b, EventReaches events a b ↔ EventReaches part a b) ∧
      (∀ a b, EventReaches part a b → (part.map eventSwap).prod.SameCycle a b) := by
  classical
  induction events with
  | nil =>
    refine ⟨[],List.Sublist.refl _,fun _ _ => Iff.rfl,?_⟩
    intro a b h
    induction h with
    | refl => exact Equiv.Perm.SameCycle.refl _ _
    | tail hp he ih => obtain ⟨e,he,_⟩ := he; simp at he
  | cons e rest ih =>
    obtain ⟨part,hsub,hreach,hcycle⟩ := ih
    have htail (a b : Fin n) (he : EventEdge rest a b) : EventReaches part a b :=
      (hreach a b).mp (Relation.ReflTransGen.single he)
    by_cases hjoin : EventReaches part e.1 e.2
    · have hsub' : part.Sublist (e::rest) := hsub.cons _
      refine ⟨part,hsub',?_,hcycle⟩
      intro a b
      constructor
      · apply event_reaches_of_edge_paths
        intro x y hx
        obtain ⟨f,hf,hor⟩ := hx
        rcases List.mem_cons.mp hf with hf | hf
        · subst f
          rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact hjoin
          · exact event_reaches_symm _ hjoin
        · exact htail x y ⟨f,hf,hor⟩
      · exact event_reaches_mono (fun _ h => hsub'.subset h)
    · let q := (part.map eventSwap).prod
      have hnot : ¬q.SameCycle e.1 e.2 := by
        intro hh
        exact hjoin (cycle_event_reachable part q rfl hh.inv)
      have hsub' : (e::part).Sublist (e::rest) := hsub.cons₂ _
      refine ⟨e::part,hsub',?_,?_⟩
      · intro a b
        constructor
        · apply event_reaches_of_edge_paths
          intro x y hx
          obtain ⟨f,hf,hor⟩ := hx
          rcases List.mem_cons.mp hf with hf | hf
          · subst f
            exact Relation.ReflTransGen.single ⟨e,by simp,hor⟩
          · exact event_reaches_mono (fun _ h => List.mem_cons_of_mem _ h) (htail x y ⟨f,hf,hor⟩)
        · exact event_reaches_mono (fun _ h => hsub'.subset h)
      · intro a b hab
        change (Equiv.swap e.1 e.2*q).SameCycle a b
        have hstep (x y : Fin n) (hx : EventEdge (e::part) x y) :
            (Equiv.swap e.1 e.2*q).SameCycle x y := by
          obtain ⟨f,hf,hor⟩ := hx
          rcases List.mem_cons.mp hf with hf | hf
          · subst f
            have hh := swap_distinct_orbits_same_cycle q e.1 e.2 hnot
            rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
            · exact hh
            · exact hh.symm
          · exact same_cycle_after_orbit_merge q e.1 e.2 hnot
              (hcycle x y (Relation.ReflTransGen.single ⟨f,hf,hor⟩))
        induction hab with
        | refl => exact Equiv.Perm.SameCycle.refl _ _
        | tail hp he ih => exact ih.trans (hstep _ _ he)

/-- Strong root-cover inequality. The spanning forest and its permutation
orbits are derived internally, without supplied packet defect additivity. -/
theorem strong_root_cover_count (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p) (roots : List (Fin n))
    (hcover : ∀ i : Fin n, ∃ r ∈ roots, EventReaches events r i) :
    2*n+p.cycleFactorsFinset.card ≤ events.length+p.support.card+2*roots.length := by
  obtain ⟨part,hsub,hreach,hcycle⟩ := exists_spanning_event_forest events
  let q := (part.map eventSwap).prod
  obtain ⟨hqprod,hqlen⟩ := exact_event_word_spec q
  have hcover' : ∀ i : Fin n, ∃ r ∈ roots, EventReaches (exactEventWord q) r i := by
    intro i
    obtain ⟨r,hr,hi⟩ := hcover i
    exact ⟨r,hr,cycle_event_reachable _ q hqprod (hcycle r i ((hreach r i).mp hi)).inv⟩
  have hroot := root_cover_count (exactEventWord q) roots hcover'
  have hrank := event_sublist_rank_bound hsub p q hprod rfl
  have hmin := cycle_root_count (p := q) (events := part) rfl
  have hqi : (q⁻¹).cycleFactorsFinset.card=q.cycleFactorsFinset.card := by
    have hh := congrArg Multiset.card (Equiv.Perm.cycleType_inv q)
    simpa only [Equiv.Perm.cycleType,Multiset.card_map,Finset.card_val] using hh
  omega

#print axioms exists_spanning_event_forest
#print axioms strong_root_cover_count
end LRX.ZeroGap

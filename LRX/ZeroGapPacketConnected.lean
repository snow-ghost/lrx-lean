module

public import LRX.ZeroGapComponentOrder
public import LRX.PacketCoreBalance
public import LRX.ZeroGapComponentSize

@[expose] public section

/-! Every strongly connected service packet lies in one component of the
actual zero-gap sorting events. -/
namespace LRX.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem service_edge_component_order {p : State n} {d : Fin n → ℤ}
    {events : List (Event n)} (hprod : (events.map eventSwap).prod=p)
    (hsep : events.Pairwise LaterOutside)
    (htravel : ∀ i, Travel events i (p.symm i) (d i)) {i j : Fin n}
    (he : BufferProgram.ServiceEdge p d i j) :
    EventReaches events i j ∨ componentTime events j < componentTime events i := by
  rcases he with hc | ⟨hj,ht⟩
  · exact Or.inl (cycle_event_reachable events p hprod hc)
  · by_cases hr : EventReaches events i j
    · exact Or.inl hr
    · exact Or.inr ((htravel i).other_component_time_lt hsep ht hr)

theorem service_path_component_order {p : State n} {d : Fin n → ℤ}
    {events : List (Event n)} (hprod : (events.map eventSwap).prod=p)
    (hsep : events.Pairwise LaterOutside)
    (htravel : ∀ i, Travel events i (p.symm i) (d i)) {i j : Fin n}
    (hp : PrunedLift.Reaches p d i j) :
    EventReaches events i j ∨ componentTime events j < componentTime events i := by
  induction hp with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail k j hp he ih =>
    have he' := service_edge_component_order hprod hsep htravel he
    rcases ih with hr | ht <;> rcases he' with hr' | ht'
    · exact Or.inl (hr.trans hr')
    · exact Or.inr (by rwa [← component_time_eq hr] at ht')
    · exact Or.inr (by rwa [component_time_eq hr'] at ht)
    · exact Or.inr (lt_trans ht' ht)

theorem core_event_reachable {p : State n} {d : Fin n → ℤ}
    {events : List (Event n)} (hprod : (events.map eventSwap).prod=p)
    (hsep : events.Pairwise LaterOutside)
    (htravel : ∀ i, Travel events i (p.symm i) (d i)) {root i : Fin n}
    (hi : PrunedLift.InCore p d root i) : EventReaches events root i := by
  rcases service_path_component_order hprod hsep htravel hi.1 with hr | ht
  · exact hr
  · rcases service_path_component_order hprod hsep htravel hi.2 with hr | ht'
    · exact event_reaches_symm events hr
    · omega

#print axioms core_event_reachable
end LRX.ZeroGap

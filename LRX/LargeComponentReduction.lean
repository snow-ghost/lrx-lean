import LRX.SmallComponentSharpWord
import LRX.MaximalCanonicalReduction

namespace LRX

/-- After the small-component branch, only canonical maps having a component
larger than half the circle remain to be routed sharply. -/
def LargeComponentCanonicalSharpRouting : Prop :=
  ∀ (n : ℕ) [NeZero n], 4 ≤ n → ∀ (q : State n) (m : ℕ),
    0 < m → (FiniteCuts.componentRoots q).card = m+1 →
    AffineLift.Majorized (FiniteCuts.displacement q.symm) → FiniteCuts.MaximalZeroCut q →
    (∃ a : Fin n, (n+1)/2 < (FiniteCuts.componentSet q a).card) →
    ∀ start finish : Fin n, ∃ w : List Letter,
      eval w = (RotationWords.rotation start)⁻¹ * q * RotationWords.rotation finish ∧
      w.length ≤ n.choose 2

theorem maximal_canonical_of_large_component (pay : LargeComponentCanonicalSharpRouting) :
    MaximalCanonicalSharpRouting := by
  intro n _ hn q m hm hcm hmaj hmax start finish
  by_cases hsmall : ∀ a : Fin n, (FiniteCuts.componentSet q a).card ≤ (n+1)/2
  · exact FiniteCuts.small_components_sharp_word hn q hsmall start finish
  · have hlarge : ∃ a : Fin n, (n+1)/2 < (FiniteCuts.componentSet q a).card := by
      simpa only [not_forall,not_le] using hsmall
    exact pay n hn q m hm hcm hmaj hmax hlarge start finish

theorem nonzero_routing_of_large_component (pay : LargeComponentCanonicalSharpRouting) :
    NonzeroLiftRouting :=
  nonzero_routing_of_maximal_canonical (maximal_canonical_of_large_component pay)

#print axioms maximal_canonical_of_large_component
#print axioms nonzero_routing_of_large_component
end LRX

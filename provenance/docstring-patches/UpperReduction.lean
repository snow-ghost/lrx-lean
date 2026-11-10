import LRX.ZeroLift
import LRX.ExactDiameter

/-! Reduction of the upper bound to routing of nonzero majorized lifts.
Phase selection and normalization are proved from the input permutation; the
zero-displacement branch is closed by a paid word. The routing proposition
`NonzeroLiftRouting` is proved in `LRX.SharpDiameterAll` (`LRX.nonzero_lift_routing`). -/
namespace LRX
open AffineLift

/-- Routing proposition: a short literal word for each nonzero, majorized,
balanced lift of a permutation with its fixed finite end cursor.
Stated as a `Prop`; proved as `LRX.nonzero_lift_routing`. -/
def NonzeroLiftRouting : Prop :=
  ∀ (n : ℕ) [NeZero n], 4 ≤ n → ∀ (p : State n) (c : Fin n) (d : Fin n → ℤ),
    IsLift p (c : ℤ) d → Majorized d → (∃ i, d i ≠ 0) →
    ∃ w : List Letter, eval w = p ∧ w.length ≤ n.choose 2

/-- The general upper theorem follows from the routing proposition. -/
theorem sharp_upper_of_nonzero_routing (route : NonzeroLiftRouting) :
    SharpDiameterTheorem := by
  intro n _ hn
  apply ediam_le_of_words
  intro p
  obtain ⟨c, d, hd, hm⟩ := exists_cyclic_lift p
  by_cases hnonzero : ∃ i, d i ≠ 0
  · exact route n hn p c d hd hm hnonzero
  · have hz : d = fun _ => 0 := by
      funext i
      by_contra h
      exact hnonzero ⟨i, h⟩
    subst d
    exact zero_lift_sharp_word hn hd


#print axioms sharp_upper_of_nonzero_routing
end LRX

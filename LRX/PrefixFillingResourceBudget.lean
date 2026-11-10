import LRX.OriginalFillingResourceBudget
import LRX.PositiveFillingResourceMonotone

/-! M4: apply the derived scalar budget to the actual internal windows of
the large component, without replacing them by the full-map window family. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n k : ℕ} [NeZero n]

theorem original_unpaid_prefix_filling_budget (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    ((positiveSourceFamily (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).map FillingWindow.resource).sum ≤ scalarFillingBudget p root := by
  have hL : (componentSet p root).card ≤ n := by simpa using Finset.card_le_univ (componentSet p root)
  exact (positive_filling_resource_mono _ _ n hL).trans
    (original_unpaid_scalar_filling_budget hn p hmaj hmax hc hk root hlarge hpos)

theorem original_unpaid_prefix_filling_filters (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    let As := positiveSourceFamily (localTarget p 0 (componentLeft p root)) (componentSet p root).card
    let T := scalarFillingBudget p root
    (As.map (fun A => (A.size : ℤ))).sum ≤ 2*T+
      (As.map (fun A => ((A.size-A.filling.support.card : ℕ) : ℤ))).sum-
      2*(As.map (fun A => cycleDefect A.filling)).sum ∧
    (As.map (fun A => ∑ i, |displacement A.filling i|)).sum ≤ 2*T*(T+1) ∧
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤ 4*T^2+2*T+
      (As.map (fun A => (A.size : ℤ))).sum := by
  exact filling_family_resource_budget _ _
    (original_unpaid_prefix_filling_budget hn p hmaj hmax hc hk root hlarge hpos)

#print axioms original_unpaid_prefix_filling_budget
#print axioms original_unpaid_prefix_filling_filters
end LRX.FiniteCuts

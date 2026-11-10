import LRX.ShallowShellWindowFamily
import LRX.AdjacentBoundaryPrice

namespace LRX.FiniteCuts
open FiniteWindow FiniteRankOrder
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- A second real nontrivial component supplies at least two exterior positions. -/
theorem prefix_multiple_components_exterior_size (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hm : 2 ≤ (componentRoots p).card) :
    2 ≤ n-(componentSet p 0).card := by
  let L := (componentSet p 0).card
  have hproper := component_card_lt_of_multiple_roots p hm 0
  have hcount := prefix_component_root_count p L hc (zero_component_prefix p)
  have hmin := nontrivial_suffix_size_sum p L
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  have hsum := suffix_component_parameter_sum p L hproper.le hcut
  change 2 ≤ n-L
  omega

#print axioms prefix_multiple_components_exterior_size
end LRX.FiniteCuts

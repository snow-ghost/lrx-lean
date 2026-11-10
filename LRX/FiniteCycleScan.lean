import LRX.FiniteCycleProfile
import LRX.OrderedPortRoute

/-! A paid monotone scan of the finite cycles accessible from the left.
The list contains actual disjoint cycles and every service word is constructed. -/
namespace LRX.FiniteCuts
open RotationWords
variable {b : ℕ} [NeZero b]

omit [NeZero b] in
theorem inverse_targets_disjoint (l : List (State b))
    (hd : l.Pairwise Equiv.Perm.Disjoint) :
    (l.map (fun q => q⁻¹)).Pairwise Equiv.Perm.Disjoint := by
  exact List.pairwise_map.mpr (hd.imp (fun h => h.inv_left.inv_right))

omit [NeZero b] in
theorem inverse_cycle_product (l : List (State b))
    (hd : l.Pairwise Equiv.Perm.Disjoint) :
    (l.map (fun q => q⁻¹)).prod=l.prod⁻¹ := by
  rw [List.prod_inv_reverse]
  exact Equiv.Perm.disjoint_prod_perm (inverse_targets_disjoint l hd) (List.reverse_perm _).symm

#print axioms inverse_cycle_product
end LRX.FiniteCuts

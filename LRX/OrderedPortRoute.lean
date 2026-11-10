import LRX.PortRoute
import Mathlib.Data.List.Sort

/-! A monotone traversal of service ports pays at most the length of the
containing interval. Services may be reordered because their targets commute. -/
namespace LRX.RotationWords
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem short_move_le_difference (s t : Fin n) (h : s.val ≤ t.val) :
    min (t-s).val (n-(t-s).val) ≤ t.val-s.val := by
  rw [Fin.sub_val_of_le h]
  exact min_le_left _ _

theorem ordered_walk_cost (s t : Fin n) (services : List (ClosedService n))
    (hst : s.val ≤ t.val)
    (horder : services.Pairwise (fun a b => a.port.val ≤ b.port.val))
    (hrange : ∀ a ∈ services, s.val ≤ a.port.val ∧ a.port.val ≤ t.val) :
    walkCost s t services ≤ t.val-s.val := by
  induction services generalizing s with
  | nil => exact short_move_le_difference s t hst
  | cons a rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp horder
    have ha := hrange a (by simp)
    have hw := ih a.port ha.2 htail (fun r hr =>
      ⟨hhead r hr, (hrange r (by simp [hr])).2⟩)
    have hm := short_move_le_difference s a.port ha.1
    simp only [walkCost]
    omega

#print axioms ordered_walk_cost
end LRX.RotationWords

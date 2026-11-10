module

public import LRX.Cycle11PairEncounter

@[expose] public section

namespace LRX.Cycle11StructuralBridge
open LRX.BlockExchange LRX.Cycle11TwoLabelRepair LRX.Cycle11PairEncounter
variable {α : Type*}

theorem step_perm (op : Op) (s : List α) : (step op s).Perm s := by
  cases op with
  | L => cases s with
    | nil => exact List.Perm.refl _
    | cons x t => simpa [step,left] using List.perm_append_comm t [x]
  | R =>
    have h : (left (right s)).Perm (right s) := by
      cases right s with
      | nil => exact List.Perm.refl _
      | cons x t => simpa [left] using List.perm_append_comm t [x]
    rw [LRX.ReducedPrice.left_right] at h
    exact h.symm
  | X => cases s with
    | nil => exact List.Perm.refl _
    | cons x s => cases s with
      | nil => exact List.Perm.refl _
      | cons y t => exact List.Perm.swap _ _ _

theorem run_perm (w : List Op) (s : List α) : (run w s).Perm s := by
  induction w generalizing s with
  | nil => exact List.Perm.refl _
  | cons op w ih => exact (ih (step op s)).trans (step_perm op s)

theorem map_fixed (f : α → α) (a b : α) (t : List α)
    (hf : ∀ x, x≠a → x≠b → f x=x) (ha : a∉t) (hb : b∉t) : t.map f=t := by
  calc
    t.map f = t.map id := List.map_congr_left (by
      intro x hx
      exact hf x (by intro h;subst x;exact ha hx) (by intro h;subst x;exact hb hx))
    _ = t := List.map_id t

#print axioms run_perm
end LRX.Cycle11StructuralBridge

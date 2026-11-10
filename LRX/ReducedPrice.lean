module

public import LRX.BlockExchange
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace LRX.ReducedPrice
open BlockExchange
variable {α : Type*}

theorem right_left (s : List α) : right (left s) = s := by
  cases s with
  | nil => rfl
  | cons x xs => exact right_append xs x

theorem left_right (s : List α) : left (right s) = s := by
  have h := right_left s.reverse
  simpa [right] using congrArg List.reverse h

def spin : Int → List Op
  | .ofNat n => List.replicate n .L
  | .negSucc n => List.replicate (n+1) .R

end LRX.ReducedPrice

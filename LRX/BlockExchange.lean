import Mathlib.Tactic.Linarith

/-! Concrete L/R/X list semantics and paid macros exchanging a repeated block
with an adjacent atom. Independent namespace; no hypothesis about an optimizer,
affine profiles, or a global diameter theorem. -/
namespace LRX.BlockExchange
variable {α : Type*}

inductive Op where
  | L | R | X

def left : List α → List α
  | [] => []
  | x :: xs => xs ++ [x]
def right (xs : List α) : List α := (left xs.reverse).reverse
def swap : List α → List α
  | x :: y :: xs => y :: x :: xs
  | xs => xs
def step (op : Op) (s : List α) : List α :=
  match op with
  | .L => left s
  | .R => right s
  | .X => swap s
def run : List Op → List α → List α
  | [], s => s
  | op :: ops, s => run ops (step op s)

theorem run_append (u v : List Op) (s : List α) :
    run (u ++ v) s = run v (run u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons op ops ih => simpa [run] using ih (step op s)

theorem right_append (xs : List α) (x : α) : right (xs ++ [x]) = x :: xs := by
  simp [right, left]

end LRX.BlockExchange

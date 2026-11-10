module

public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Algebra.Group.Fin.Basic
import LRX.SharpDiameterAll

/-! Implementation of the independent L/R/X statements in Challenge.
The three moves have unit cost; no quotient by rotations is taken. -/

@[expose] public section

namespace PalomarLRX

/-- Permutations of the n positions. -/
abbrev State (n : ℕ) := Equiv.Perm (Fin n)

/-- The unit-cost moves: 0 = L, 1 = R, 2 = X. -/
def move (n : ℕ) [NeZero n] (c : Fin 3) : State n :=
  if c = 0 then finRotate n
  else if c = 1 then (finRotate n)⁻¹ else Equiv.swap 0 1

/-- Evaluate a literal word by multiplying its generators in list order. -/
def eval {n : ℕ} [NeZero n] (w : List (Fin 3)) : State n :=
  (w.map (move n)).prod

/-- The undirected Cayley graph, with each L/R/X edge of cost one. -/
def graph (n : ℕ) [NeZero n] : SimpleGraph (State n) :=
  SimpleGraph.mulCayley {finRotate n, (finRotate n)⁻¹, Equiv.swap 0 1}

private def encode : LRX.Letter → Fin 3
  | .l => 0
  | .r => 1
  | .x => 2

private theorem move_encode {n : ℕ} [NeZero n] (c : LRX.Letter) :
    move n (encode c) = c.eval := by
  cases c <;> rfl

private theorem eval_encode {n : ℕ} [NeZero n] (w : List LRX.Letter) :
    eval (n := n) (w.map encode) = LRX.eval w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change move n (encode c) * eval (w.map encode) = c.eval * LRX.eval w
    rw [move_encode, ih]

private theorem graph_eq (n : ℕ) [NeZero n] : graph n = LRX.graph n := rfl

/-- Every ordered pair is joined by a word within the sharp bound. -/
theorem boundedRouting (n : ℕ) [NeZero n] (hn : 4 ≤ n) (a b : State n) :
    ∃ w : List (Fin 3), a * eval w = b ∧ w.length ≤ n * (n - 1) / 2 := by
  obtain ⟨w, hw, hlen⟩ :=
    (LRX.ediam_le_iff_words.mp (LRX.sharp_diameter_all n hn)) (a⁻¹ * b)
  refine ⟨w.map encode, ?_, ?_⟩
  · rw [eval_encode, hw, mul_inv_cancel_left]
  · simpa only [List.length_map, Nat.choose_two_right] using hlen

/-- The maximum shortest-path distance is exactly n(n-1)/2, for every n >= 4. -/
theorem exactDiameter (n : ℕ) [NeZero n] (hn : 4 ≤ n) :
    (graph n).diam = n * (n - 1) / 2 := by
  rw [graph_eq]
  exact LRX.exact_diameter_all n hn

end PalomarLRX

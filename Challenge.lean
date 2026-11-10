module

public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Algebra.Group.Fin.Basic

/-!
# Exact diameter with unit-cost L, R, X moves

The vertices are permutations of `Fin n`. L is the cyclic shift `finRotate n`,
R is its inverse, and X exchanges positions 0 and 1. Each letter costs one
move, including R. The graph is the ordinary undirected Cayley graph for
these three generators; rotations are not factored out.

`boundedRouting` asserts a literal word of at most n(n-1)/2 letters between
every ordered pair of vertices. In particular the graph is connected in
the stated range, so its natural-valued diameter has its usual meaning.
`exactDiameter` states that this uniform bound is attained for every n >= 4.
Neither theorem classifies all extremal permutations or supplies an
executable shortest-word solver. The conjecture is recorded in OEIS A186783.
-/

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

/-- Every ordered pair is joined by a word within the sharp bound. -/
theorem boundedRouting (n : ℕ) [NeZero n] (hn : 4 ≤ n) (a b : State n) :
    ∃ w : List (Fin 3), a * eval w = b ∧ w.length ≤ n * (n - 1) / 2 := by
  sorry

/-- The maximum shortest-path distance is exactly n(n-1)/2, for every n >= 4. -/
theorem exactDiameter (n : ℕ) [NeZero n] (hn : 4 ≤ n) :
    (graph n).diam = n * (n - 1) / 2 := by
  sorry

end PalomarLRX

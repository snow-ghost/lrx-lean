module

public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Algebraic part of the reflection swap-graph reduction.
The hypotheses express parity of actual label-pair swaps. Establishing those
hypotheses from concrete LRX words, and no repeated pairs in a shortest word,
are separate obligations, not assumed proved by this module. -/
namespace LRX.LowerBoundSwapGraph
variable {α : Type*}

def color [DecidableEq α] (e : α → α → Bool) (z a : α) : Bool :=
  if a = z then false else !(e z a)

/-- Every graph with odd edge parity on every triple is two disjoint cliques.
Diagonal values are irrelevant: the conclusion is only for distinct vertices. -/
theorem two_cliques [DecidableEq α] (e : α → α → Bool) (z : α)
    (sym : ∀ a b, e a b = e b a)
    (tri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      ((e a b ^^ e a c) ^^ e b c) = true)
    (a b : α) (hab : a ≠ b) :
    e a b = (color e z a == color e z b) := by
  by_cases ha : a = z
  · subst a
    have hb : b ≠ z := Ne.symm hab
    cases he : e z b <;> simp [color, hb, he]
  · by_cases hb : b = z
    · subst b
      rw [sym a z]
      cases he : e z a <;> simp [color, ha, he]
    · have ht := tri z a b (Ne.symm ha) (Ne.symm hb) hab
      simp only [color, ite_eq_right ha, ite_eq_right hb]
      cases hza : e z a <;> cases hzb : e z b <;> cases habv : e a b <;>
        simp_all

#print axioms two_cliques
end LRX.LowerBoundSwapGraph

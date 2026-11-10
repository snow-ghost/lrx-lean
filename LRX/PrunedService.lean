module

public import LRX.PrunedReachability
public import LRX.AffineReducedPrice

@[expose] public section

/-! The retained part of a root star has a literal service and exact price.
Only geometric star coverage, cycle invariance, and retained balance are inputs. -/
namespace LRX.PrunedLift
open scoped BigOperators
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem sum_inverse (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (f : Fin n → ℤ) :
    (∑ i ∈ S, f (p.symm i))=∑ i ∈ S, f i := by
  apply Finset.sum_bij (fun i _ => p.symm i)
  · intro i hi
    exact (inverse_mem_iff p S hS i).mpr hi
  · intro i hi j hj he
    exact p.symm.injective he
  · intro j hj
    exact ⟨p j, (hS j).mpr hj, p.symm_apply_apply j⟩
  · intro i hi
    rfl

omit [NeZero n] in
theorem canonical_balance (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) :
    (∑ i ∈ S, ((p.symm i : ℤ)-(i : ℤ)))=0 := by
  rw [Finset.sum_sub_distrib, sum_inverse p S hS (fun i => (i : ℤ)), sub_self]

#print axioms canonical_balance
end LRX.PrunedLift

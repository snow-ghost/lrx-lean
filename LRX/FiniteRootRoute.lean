module

public import LRX.FiniteCycleScan
public import LRX.FiniteDisplacementSum
public import LRX.FiniteExactAvailability
public import LRX.OrderedExactRoute
public import LRX.PrunedLoad

@[expose] public section

/-! A complete finite-root route directly from a permutation, using its
canonical cycle factorization and an automatic choice of child services. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {b : ℕ}

noncomputable def factorList (p : State b) : List (State b) := p.cycleFactorsFinset.toList

theorem factor_list_spec (p : State b) :
    (∀ q ∈ factorList p, q.IsCycle) ∧
      (factorList p).Pairwise Equiv.Perm.Disjoint ∧ (factorList p).prod=p := by
  classical
  apply (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset (Finset.nodup_toList _)).mp
  simp

variable [NeZero b]

end LRX.FiniteCuts

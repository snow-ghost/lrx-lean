module

public import LRX.FiniteInversionDecomposition

@[expose] public section

namespace LRX.FiniteCuts
variable {n : ℕ}

/-- Delete source row a and target column p(a), independently preserving
the order on the two complements. -/
def contract (p : State (n+1)) (a : Fin (n+1)) : State n :=
  (finSuccAboveEquiv a).trans
    ((p.subtypeEquiv (p := fun i => i ≠ a) (q := fun j => j ≠ p a)
      (fun _ => not_congr p.injective.eq_iff.symm)).trans (finSuccAboveEquiv (p a)).symm)

theorem contract_entry (p : State (n+1)) (a : Fin (n+1)) (i : Fin n) :
    (p a).succAbove (contract p a i)=p (a.succAbove i) := by
  change ((finSuccAboveEquiv (p a)) (contract p a i)).val=p (a.succAbove i)
  simp [contract,Equiv.subtypeEquiv,finSuccAboveEquiv_apply]

#print axioms contract_entry
end LRX.FiniteCuts

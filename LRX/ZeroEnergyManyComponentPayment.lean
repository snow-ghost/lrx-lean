module

public import LRX.ZeroEnergyLastRegime
public import LRX.OddOneWidthSevenPayment

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- The entire zero-energy large-component branch with at least two
external components is paid for all cursors and every size n >= 4. -/
theorem zero_energy_many_component_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (he : canonicalEnergyDeficit p=0) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  rcases zero_energy_sharp_or_last_regime hn p hmaj hmax hc hk root hlarge ht he start finish with h | h
  · exact h
  · obtain ⟨_,hp,hf,_,hv⟩ := h
    exact zero_energy_odd_one_width_seven_sharp_word hn p hmaj hmax hc hk root hlarge ht he hp hf hv start finish

#print axioms zero_energy_many_component_sharp_word
end LRX.FiniteCuts

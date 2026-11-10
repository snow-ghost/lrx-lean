import LRX.ZeroEnergyRemainingRegimes
import LRX.EvenWidthSixPayment

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- All remaining zero-deficit cursor problems now have odd size. -/
theorem zero_energy_sharp_or_two_odd_regimes (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (he : canonicalEnergyDeficit p=0) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (n ≤ 73 ∧ n%2=1 ∧
      (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card).card=2 ∧
      ((n-p.support.card=0 ∧
        (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
          (componentSet p root).card, C.card : ℕ)=5) ∨
        (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
          (componentSet p root).card, C.card : ℕ)=7)) := by
  rcases zero_energy_sharp_or_three_regimes hn p hmaj hmax hc hk root hlarge ht he start finish with h | h
  · exact Or.inl h
  · obtain ⟨hn73,ht2,hrem⟩ := h
    rcases hrem with ⟨hp,hv⟩ | ⟨hp,hv⟩
    · exact Or.inl (zero_energy_even_width_six_sharp_word hn p hmaj hmax hc hk root hlarge ht he hp hv start finish)
    · exact Or.inr ⟨hn73,hp,ht2,hv⟩

#print axioms zero_energy_sharp_or_two_odd_regimes
end LRX.FiniteCuts

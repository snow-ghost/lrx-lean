module

public import LRX.ManyComponentFinalPayment
public import LRX.LargeComponentReduction
public import LRX.TwoComponentPeakTwo

@[expose] public section

namespace LRX
open FiniteCuts RotationWords

/-- The exact remaining routing obligation after the complete t>=2 payment. -/
def TwoComponentPeakTwoSharpRouting : Prop :=
  ∀ (n : ℕ) [NeZero n], 4 ≤ n → ∀ (p : State n),
    AffineLift.Majorized (displacement p.symm) → MaximalZeroCut p →
    ∀ (hc : (componentRoots p).card=1+1) (root : Fin n),
    (n+1)/2 < (componentSet p root).card → ∀ start finish : Fin n,
    start ≠ finish → JoinedPositiveArcs p hc start finish → 1 ≤ peakExcess p hc →
    sourceHalfPeak p=2 →
    ((canonicalEnergyDeficit p=0 ∧ n-p.support.card=n%2) ∨
      (canonicalEnergyDeficit p=1 ∧ n%4=2 ∧ n-p.support.card=2)) →
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2

theorem large_component_routing_of_peak_two (pay : TwoComponentPeakTwoSharpRouting) :
    LargeComponentCanonicalSharpRouting := by
  intro n inst hn p m hm hcm hmaj hmax hlarge start finish
  obtain ⟨root,hroot⟩ := hlarge
  by_cases hm1 : m=1
  · subst m
    rcases two_component_sharp_or_peak_two hn p hmaj hmax hcm root hroot start finish with hw | hr
    · exact hw
    · obtain ⟨hne,hboth,hpos,hU,hcases⟩ := hr
      exact pay n hn p hmaj hmax hcm root hroot start finish hne hboth hpos hU hcases
  · have hcount := component_cut_external_count p root (by omega)
    have ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card).card := by
      omega
    exact many_component_final_sharp_word hn p hmaj hmax hcm hm root hroot ht start finish

theorem nonzero_routing_of_peak_two (pay : TwoComponentPeakTwoSharpRouting) : NonzeroLiftRouting :=
  nonzero_routing_of_large_component (large_component_routing_of_peak_two pay)

#print axioms large_component_routing_of_peak_two
#print axioms nonzero_routing_of_peak_two
end LRX

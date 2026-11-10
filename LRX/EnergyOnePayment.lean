import LRX.ActualEnergyOneCases
import LRX.ActualHighEnergyExclusion
import LRX.EnergyOneParity
import LRX.ZeroEnergyManyComponentPayment
import LRX.EnergyOneCriticalExclusion

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_energy_one_impossible (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=1) : False := by
  let r := actualPeakProfile p root
  have hr := actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos
  have hpar := FinitePeak.energy_one_profile_parity r hr he
  have hp : n%2=0 := by
    have hh := hpar.1
    change ((n%2 : ℕ) : ℤ)=0 at hh
    omega
  have hcases := actual_energy_one_mem_cases hn p hmaj hmax hc hk root hlarge ht hpos he
  change (r.parity,r.fixed,r.eps,r.isolated,r.peak,r.exterior) ∈ FinitePeak.energyOneOuterRows at hcases
  simp only [FinitePeak.energyOneOuterRows,List.mem_cons,List.mem_singleton,
    List.not_mem_nil,or_false,Prod.mk.injEq] at hcases
  have nat_fields {f U v : ℕ} (hF : r.fixed=(f : ℤ)) (hU : r.peak=(U : ℤ))
      (hV : r.exterior=(v : ℤ)) : n-p.support.card=f ∧ sourceHalfPeak p=U ∧
      (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card, C.card : ℕ)=v := by
    change ((n-p.support.card : ℕ) : ℤ)=(f : ℤ) at hF
    change (sourceHalfPeak p : ℤ)=(U : ℤ) at hU
    change ((_ : ℕ) : ℤ)=(v : ℤ) at hV
    exact ⟨by exact_mod_cast hF,by exact_mod_cast hU,by exact_mod_cast hV⟩
  have bad (f : ℕ) (hf : f ≤ 2) (hfix : n-p.support.card=f)
      (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card, C.card : ℕ)=(if f=0 then 4 else 6))
      (hU : f+3 ≤ sourceHalfPeak p) : False := by
    have hbudget := actual_energy_one_defect_peak_budget hn p hmaj hmax hc hk root hlarge ht hpos he hp f hf hfix hv
    have hdef := actual_energy_one_nonempty_global_defect hn p hmaj hmax hc hk root hlarge ht hpos he hp f hf hfix hv
    omega
  rcases hcases with h | h | h | h | h | h
  · obtain ⟨_,hF,_,_,hU,hV⟩ := h
    obtain ⟨hf,hU,hv⟩ := nat_fields (f := 0) (U := 3) (v := 4) hF hU hV
    exact bad 0 (by decide) hf (by simpa using hv) (by omega)
  · obtain ⟨_,hF,_,_,hU,hV⟩ := h
    obtain ⟨hf,hU,hv⟩ := nat_fields (f := 1) (U := 4) (v := 5) hF hU hV
    exact actual_energy_one_empty_shapes_impossible hn p hmaj hmax hc hk root hlarge ht hpos he hp (Or.inl ⟨hf,hv⟩)
  · obtain ⟨_,hF,_,_,hU,hV⟩ := h
    obtain ⟨hf,hU,hv⟩ := nat_fields (f := 1) (U := 4) (v := 6) hF hU hV
    exact bad 1 (by decide) hf (by simpa using hv) (by omega)
  · obtain ⟨_,hF,_,_,hU,hV⟩ := h
    obtain ⟨hf,hU,hv⟩ := nat_fields (f := 2) (U := 4) (v := 6) hF hU hV
    exact actual_energy_one_critical_impossible hn p hmaj hmax hc hk root hlarge ht hpos he hp hf hv hU
  · obtain ⟨_,hF,_,_,hU,hV⟩ := h
    obtain ⟨hf,hU,hv⟩ := nat_fields (f := 2) (U := 5) (v := 6) hF hU hV
    exact bad 2 (by decide) hf (by simpa using hv) (by omega)
  · obtain ⟨_,hF,_,_,hU,hV⟩ := h
    obtain ⟨hf,hU,hv⟩ := nat_fields (f := 2) (U := 5) (v := 7) hF hU hV
    exact actual_energy_one_empty_shapes_impossible hn p hmaj hmax hc hk root hlarge ht hpos he hp (Or.inr ⟨hf,hv⟩)

#print axioms actual_energy_one_impossible
end LRX.FiniteCuts

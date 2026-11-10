import LRX.TwoSizeCoverage
import LRX.ManyCountTwoReduction

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords FiniteWindow
variable {n k : ℕ} [NeZero n]

/-- All actual unpaid M4 profiles now have n<=73 and exterior width<=7. -/
theorem original_unpaid_two_size_cutoff (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc) :
    (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card=2 ∧ n/2 ≤ 36 ∧ n ≤ 73 ∧
    (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ) ≤ 7 := by
  have hb := original_unpaid_many_two_cutoff hn p hmaj hmax hc hk root hlarge ht hpos
  let r := actualPeakProfile p root
  have hrt : r.t=2 := by change ((_ : ℕ) : ℤ)=2; exact_mod_cast hb.1
  have hrm : r.m ≤ 199 := by change ((n/2 : ℕ) : ℤ) ≤ 199; exact_mod_cast hb.2.1
  have hr := actual_unpaid_peak_profile_admissible hn p hmaj hmax hc hk root hlarge ht hpos
  have hcore := actual_unpaid_peak_core_bound hn p hmaj hmax hc hk root hlarge ht hpos
  have he := actual_peak_external_energy_filter p hmaj root
  obtain ⟨hm,hv⟩ := FinitePeak.admissible_two_size_bounds r hr hcore hrt he hrm
  change ((n/2 : ℕ) : ℤ) ≤ 36 at hm
  change ((∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ) : ℤ) ≤ 7 at hv
  exact ⟨hb.1,by omega,by omega,by exact_mod_cast hv⟩

/-- The finite exterior catalogue needs only genuine windows of sizes 2..5. -/
theorem original_unpaid_external_window_size (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (A : FillingWindow n)
    (hA : A ∈ suffixComponentFamily (localTarget p 0 (componentLeft p root))
      (componentSet p root).card) : 2 ≤ A.size ∧ A.size ≤ 5 := by
  have hb := original_unpaid_two_size_cutoff hn p hmaj hmax hc hk root hlarge ht hpos
  have hh := suffix_component_member_size_bound _ _ A hA
  rw [hb.1] at hh
  have hv := hb.2.2.2
  exact ⟨(suffix_component_window_sizes _ _).2 A hA,by omega⟩

#print axioms original_unpaid_two_size_cutoff
#print axioms original_unpaid_external_window_size
end LRX.FiniteCuts

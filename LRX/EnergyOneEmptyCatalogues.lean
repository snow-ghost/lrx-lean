module

public import LRX.WidthSevenChecks.Case25
public import LRX.WidthSevenChecks.Case34
public import LRX.WidthSevenChecks.Case43
public import LRX.WidthSevenChecks.Case52
public import LRX.ZeroEnergyEmptyCatalogues

@[expose] public section

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem energy_one_fixed_one_width_five_empty : filteredExteriorCatalogue 0 1 1 0 5=[] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem energy_one_fixed_two_width_seven_empty : filteredExteriorCatalogue 0 1 2 0 7=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨A,B⟩ hm
  obtain ⟨ha,hb,⟨hw,hf⟩,hc⟩ := (filtered_catalogue_mem_iff A B 0 1 2 0 7).mp hm
  have hfalse := (width_seven_cases A B ha hb hw SevenEmptyGuard
    seven_empty_25 seven_empty_34 seven_empty_43 seven_empty_52) hf
  have hc' : compatibleSignOffsets A B 0 2 1=true := by
    simpa only [Nat.cast_ofNat] using hc
  exact Bool.noConfusion (hc'.symm.trans hfalse)

variable {n k : ℕ} [NeZero n]

theorem actual_energy_one_empty_shapes_impossible (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=1) (hp : n%2=0)
    (hcase :
      (n-p.support.card=1 ∧ (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card, C.card : ℕ)=5) ∨
      (n-p.support.card=2 ∧ (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card, C.card : ℕ)=7)) : False := by
  obtain ⟨A,B,_,_,_,_,hmem⟩ :=
    actual_unpaid_filtered_exterior_pair hn p hmaj hmax hc hk root hlarge ht hpos
  have hm := filtered_catalogue_drop_isolated _ _ _ _ _ _ _ hmem
  rcases hcase with ⟨hf,hv⟩ | ⟨hf,hv⟩
  · rw [hp,he,hf,hv] at hm
    norm_num only [Nat.cast_zero] at hm
    rw [energy_one_fixed_one_width_five_empty] at hm
    simp only [List.not_mem_nil] at hm
  · rw [hp,he,hf,hv] at hm
    norm_num only [Nat.cast_zero] at hm
    rw [energy_one_fixed_two_width_seven_empty] at hm
    simp only [List.not_mem_nil] at hm

#print axioms energy_one_fixed_one_width_five_empty
#print axioms energy_one_fixed_two_width_seven_empty
#print axioms actual_energy_one_empty_shapes_impossible
end LRX.FiniteCuts

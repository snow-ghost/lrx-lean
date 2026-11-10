import LRX.ExteriorUnitPairRigidity

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators

theorem fin_two_support_zero_or_two : ∀ σ : State 2, σ.support.card=0 ∨ σ.support.card=2 := by
  decide +kernel

/-- Even one allowed fixed position cannot make either two-position
exterior map the identity, which would require two fixed positions. -/
theorem filtered_width_four_few_fixed (A B : SmallExteriorMap) (parity eps : ℤ)
    (fixed isolated : ℕ) (hf : fixed ≤ 1)
    (h : (A,B) ∈ filteredExteriorCatalogue parity eps fixed isolated 4) :
    A=unitExteriorMap ∧ B=unitExteriorMap := by
  obtain ⟨ha,hb,⟨hwidth,hfixed⟩,_⟩ := (filtered_catalogue_mem_iff A B parity eps fixed isolated 4).mp h
  have hAs := catalogue_member_size A ha
  have hBs := catalogue_member_size B hb
  rcases A with ⟨a,σ⟩
  rcases B with ⟨b,τ⟩
  dsimp only at hwidth hfixed hAs hBs ⊢
  have ha2 : a=2 := by omega
  have hb2 : b=2 := by omega
  subst a
  subst b
  have hs := fin_two_support_zero_or_two σ
  have ht := fin_two_support_zero_or_two τ
  have hσ := fin_two_full_support_swap σ (by omega)
  have hτ := fin_two_full_support_swap τ (by omega)
  subst σ
  subst τ
  exact ⟨rfl,rfl⟩

theorem odd_unit_pair_sign_check : ∀ f : Fin 2,
    compatibleSignOffsets unitExteriorMap unitExteriorMap 1 (f.val : ℤ) 0=false := by
  decide +kernel

/-- The entire odd zero-energy,width-four catalogue cell is empty. -/
theorem odd_zero_width_four_not_mem (A B : SmallExteriorMap) (fixed isolated : ℕ)
    (hf : fixed ≤ 1) : (A,B) ∉ filteredExteriorCatalogue 1 0 fixed isolated 4 := by
  intro h
  obtain ⟨rfl,rfl⟩ := filtered_width_four_few_fixed A B 1 0 fixed isolated hf h
  have hh := (filtered_catalogue_mem_iff unitExteriorMap unitExteriorMap 1 0 fixed isolated 4).mp h
  have hfalse := odd_unit_pair_sign_check ⟨fixed,by omega⟩
  have ht := hh.2.2.2
  rw [hfalse] at ht
  contradiction

variable {n k : ℕ} [NeZero n]

theorem actual_odd_zero_width_four_impossible (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4) : False := by
  have hfixed := canonical_fixed_activity_square p hmaj
  change (((n-p.support.card : ℕ) : ℤ))^2 ≤ 4*canonicalEnergyDeficit p+(n%2 : ℕ) at hfixed
  rw [he,hp] at hfixed
  norm_num only [Nat.cast_one,mul_zero,zero_add] at hfixed
  have hfi : ((n-p.support.card : ℕ) : ℤ) ≤ 1 := by nlinarith [sq_nonneg (((n-p.support.card : ℕ) : ℤ)-1)]
  have hf : n-p.support.card ≤ 1 := by exact_mod_cast hfi
  obtain ⟨A,B,_,_,_,_,hmem⟩ :=
    actual_unpaid_filtered_exterior_pair hn p hmaj hmax hc hk root hlarge ht hpos
  rw [hp,he,hv] at hmem
  norm_num only [Nat.cast_one] at hmem
  exact odd_zero_width_four_not_mem _ _ _ _ hf hmem

#print axioms fin_two_support_zero_or_two
#print axioms filtered_width_four_few_fixed
#print axioms odd_unit_pair_sign_check
#print axioms odd_zero_width_four_not_mem
#print axioms actual_odd_zero_width_four_impossible
end LRX.FiniteCuts

import LRX.SignedSelectionDeficit

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem zero_energy_even_sign_offsets (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0) :
    positiveSignOffset p=0 ∧ negativeSignOffset p=0 := by
  have hP := positive_selection_deficit p hmaj ∅ (Finset.empty_subset _)
  have hN := negative_selection_deficit p hmaj ∅ (Finset.empty_subset _)
  simp only [Finset.card_empty,Nat.cast_zero,add_zero,Finset.sum_empty,mul_zero,he,hp] at hP hN
  constructor <;> nlinarith [sq_nonneg (positiveSignOffset p),sq_nonneg (negativeSignOffset p)]

theorem zero_energy_unit_selection_card (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (S : Finset (Fin n)) (sign : ℤ) (hsign : sign=1 ∨ sign= -1)
    (hunit : ∀ i ∈ S, displacement p.symm i=sign) : S.card ≤ 2 := by
  classical
  obtain ⟨hP,hN⟩ := zero_energy_even_sign_offsets p hmaj he hp
  have hmass : (∑ i ∈ S, |displacement p.symm i|)=(S.card : ℤ) := by
    calc
      _ = ∑ i ∈ S, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hunit i hi]
        rcases hsign with h | h <;> rw [h] <;> norm_num
      _ = _ := by simp
  have hcap : (S.card : ℤ)^2 ≤ 2*(S.card : ℤ) := by
    rcases hsign with hsign | hsign
    · have hsub : S ⊆ positiveArrowPositions p := by
        intro i hi
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,by rw [hunit i hi,hsign]; norm_num⟩
      have h := positive_selection_deficit p hmaj S hsub
      rw [hP,he,hp,hmass] at h
      nlinarith only [h]
    · have hsub : S ⊆ negativeArrowPositions p := by
        intro i hi
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,by rw [hunit i hi,hsign]; norm_num⟩
      have h := negative_selection_deficit p hmaj S hsub
      rw [hN,he,hp,hmass] at h
      nlinarith only [h]
  by_contra h
  have h3 : (3 : ℤ) ≤ S.card := by omega
  nlinarith [sq_nonneg ((S.card : ℤ)-2)]

/-- Two distinct known unit arrows exhaust the unit arrows of that sign. -/
theorem zero_energy_unit_pair_exhausts (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (a b : Fin n) (hab : a ≠ b) (sign : ℤ) (hsign : sign=1 ∨ sign= -1)
    (ha : displacement p.symm a=sign) (hb : displacement p.symm b=sign)
    (i : Fin n) (hi : displacement p.symm i=sign) : i=a ∨ i=b := by
  classical
  by_contra h
  have hia : i ≠ a := by tauto
  have hib : i ≠ b := by tauto
  have hcard := zero_energy_unit_selection_card p hmaj he hp {a,b,i} sign hsign (by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> assumption)
  have hthree : ({a,b,i} : Finset (Fin n)).card=3 := by
    simp [hab,hia.symm,hib.symm]
  omega

theorem zero_energy_even_full_support (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0) : p.support.card=n := by
  have h := canonical_fixed_activity_square p hmaj
  change (((n-p.support.card : ℕ) : ℤ))^2 ≤ 4*canonicalEnergyDeficit p+(n%2 : ℕ) at h
  rw [he,hp] at h
  have hsquare : (((n-p.support.card : ℕ) : ℤ))^2=0 :=
    le_antisymm (by simpa using h) (sq_nonneg _)
  have hz : ((n-p.support.card : ℕ) : ℤ)=0 := sq_eq_zero_iff.mp hsquare
  have hle : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  omega

#print axioms zero_energy_even_full_support
#print axioms zero_energy_even_sign_offsets
#print axioms zero_energy_unit_selection_card
#print axioms zero_energy_unit_pair_exhausts
end LRX.FiniteCuts

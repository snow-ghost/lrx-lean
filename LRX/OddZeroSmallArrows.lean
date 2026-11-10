import LRX.ZeroEnergyUnitCapacity

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The fixed point balances the two offsets in the odd zero-deficit case. -/
theorem zero_energy_odd_one_fixed_sign_offsets (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1)
    (hf : n-p.support.card=1) :
    positiveSignOffset p=0 ∧ negativeSignOffset p=0 := by
  have hP := positive_selection_deficit p hmaj ∅ (Finset.empty_subset _)
  have hN := negative_selection_deficit p hmaj ∅ (Finset.empty_subset _)
  simp only [Finset.card_empty,Nat.cast_zero,add_zero,Finset.sum_empty,mul_zero,
    he,hp,Nat.cast_one] at hP hN
  have hs := signed_offsets_sum p
  rw [hf,hp] at hs
  norm_num only [Nat.cast_one,sub_self] at hs
  have hPle : positiveSignOffset p ≤ 0 := by
    nlinarith [sq_nonneg (positiveSignOffset p)]
  have hNle : negativeSignOffset p ≤ 0 := by
    nlinarith [sq_nonneg (negativeSignOffset p)]
  constructor <;> omega

/-- Selected arrows of either sign share the same odd capacity. -/
theorem odd_zero_same_sign_capacity (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (S : Finset (Fin n)) (sign : ℤ) (hsign : sign=1 ∨ sign= -1)
    (hs : ∀ i ∈ S, 0 < sign*displacement p.symm i) :
    (S.card : ℤ)*((S.card : ℤ)+1) ≤ 2*∑ i ∈ S, |displacement p.symm i| := by
  obtain ⟨hP,hN⟩ := zero_energy_odd_one_fixed_sign_offsets p hmaj he hp hf
  rcases hsign with hh | hh
  · have hsub : S ⊆ positiveArrowPositions p := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [hh] using hs i hi⟩
    have h := positive_selection_deficit p hmaj S hsub
    simpa only [hP,he,hp,Nat.cast_one,zero_add] using h
  · have hsub : S ⊆ negativeArrowPositions p := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by have h := hs i hi; rw [hh] at h; linarith⟩
    have h := negative_selection_deficit p hmaj S hsub
    simpa only [hN,he,hp,Nat.cast_one,zero_add] using h

theorem odd_zero_unit_unique (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (a i : Fin n) (sign : ℤ) (hsign : sign=1 ∨ sign= -1)
    (ha : displacement p.symm a=sign) (hi : displacement p.symm i=sign) : i=a := by
  classical
  by_contra hia
  change i ≠ a at hia
  have hcard : ({a,i} : Finset (Fin n)).card=2 := by simp [hia.symm]
  have hmass : (∑ j ∈ ({a,i} : Finset (Fin n)), |displacement p.symm j|)=2 := by
    rcases hsign with h | h <;> simp [hia.symm,ha,hi,h]
  have hs : ∀ j ∈ ({a,i} : Finset (Fin n)), 0 < sign*displacement p.symm j := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> rcases hsign with h | h <;> norm_num [ha,hi,h]
  have h := odd_zero_same_sign_capacity p hmaj he hp hf {a,i} sign hsign hs
  rw [hcard,hmass] at h
  norm_num at h

/-- A unit arrow and a double arrow exhaust the latter's sign capacity. -/
theorem odd_zero_double_unique (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (a b i : Fin n) (sign : ℤ) (hsign : sign=1 ∨ sign= -1)
    (ha : displacement p.symm a=sign) (hb : displacement p.symm b=2*sign)
    (hi : displacement p.symm i=2*sign) : i=b := by
  classical
  by_contra hib
  change i ≠ b at hib
  have hsne : sign ≠ 0 := by rcases hsign with h | h <;> omega
  have hab : a ≠ b := by intro h; rw [h,hb] at ha; exact hsne (by omega)
  have hia : i ≠ a := by intro h; rw [h,ha] at hi; exact hsne (by omega)
  have hcard : ({a,b,i} : Finset (Fin n)).card=3 := by simp [hab,hia.symm,hib.symm]
  have hmass : (∑ j ∈ ({a,b,i} : Finset (Fin n)), |displacement p.symm j|)=5 := by
    rcases hsign with h | h <;> simp [hab,hia.symm,hib.symm,ha,hb,hi,h]
  have hs : ∀ j ∈ ({a,b,i} : Finset (Fin n)), 0 < sign*displacement p.symm j := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> rcases hsign with h | h <;> norm_num [ha,hb,hi,h]
  have h := odd_zero_same_sign_capacity p hmaj he hp hf {a,b,i} sign hsign hs
  rw [hcard,hmass] at h
  norm_num at h

#print axioms zero_energy_odd_one_fixed_sign_offsets
#print axioms odd_zero_same_sign_capacity
#print axioms odd_zero_unit_unique
#print axioms odd_zero_double_unique
end LRX.FiniteCuts

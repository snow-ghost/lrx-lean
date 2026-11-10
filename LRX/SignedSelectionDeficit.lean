module

public import LRX.CanonicalActivityDeficit
public import LRX.SourceGapSharpPayment

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

noncomputable def positiveArrowPositions (p : State n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 < displacement p.symm i)
noncomputable def negativeArrowPositions (p : State n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => displacement p.symm i < 0)
noncomputable def positiveSignOffset (p : State n) : ℤ :=
  ((n/2 : ℕ) : ℤ)-(positiveArrowPositions p).card
noncomputable def negativeSignOffset (p : State n) : ℤ :=
  ((n/2 : ℕ) : ℤ)-(negativeArrowPositions p).card
noncomputable def canonicalEnergyDeficit (p : State n) : ℤ :=
  ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)

/-- Arbitrary selected positive arrows satisfy the manuscript sign-prefix bound. -/
theorem positive_selection_deficit (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (S : Finset (Fin n))
    (hS : S ⊆ positiveArrowPositions p) :
    (positiveSignOffset p+(S.card : ℤ))*(positiveSignOffset p+(S.card : ℤ)+(n%2 : ℕ)) ≤
      canonicalEnergyDeficit p+2*(∑ i ∈ S, |displacement p.symm i|) := by
  classical
  have hd := canonical_lift p.symm
  have h := AffineLift.selected_positive_residual (displacement p.symm) hd.1 hmaj S hS
  change (∑ i, |displacement p.symm i|) ≤ 2*(∑ i ∈ S, |displacement p.symm i|)+
    (((positiveArrowPositions p) \ S).card : ℤ)*((n : ℤ)-((positiveArrowPositions p) \ S).card) at h
  rw [Finset.card_sdiff_of_subset hS] at h
  have hcard := Finset.card_le_card hS
  have hcast : (((positiveArrowPositions p).card-S.card : ℕ) : ℤ)=
      ((positiveArrowPositions p).card : ℤ)-(S.card : ℤ) := by omega
  change (∑ i, |displacement p.symm i|) ≤ 2*(∑ i ∈ S, |displacement p.symm i|)+
    (((positiveArrowPositions p).card-S.card : ℕ) : ℤ)*
      ((n : ℤ)-((positiveArrowPositions p).card-S.card : ℕ)) at h
  rw [hcast] at h
  have hn : (n : ℤ)=2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ) := by omega
  unfold positiveSignOffset canonicalEnergyDeficit
  rw [hn] at h ⊢
  nlinarith only [h]

/-- The negative bound uses the same original displacement and energy. -/
theorem negative_selection_deficit (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (S : Finset (Fin n))
    (hS : S ⊆ negativeArrowPositions p) :
    (negativeSignOffset p+(S.card : ℤ))*(negativeSignOffset p+(S.card : ℤ)+(n%2 : ℕ)) ≤
      canonicalEnergyDeficit p+2*(∑ i ∈ S, |displacement p.symm i|) := by
  classical
  have hd := canonical_lift p.symm
  have h := AffineLift.original_selected_negative_residual hd.1 hmaj
    (Function.Embedding.refl (Fin n)) (displacement p.symm) (fun _ => rfl) hd.1 S hS
  change (∑ i, |displacement p.symm i|) ≤ 2*(∑ i ∈ S, |displacement p.symm i|)+
    (((negativeArrowPositions p) \ S).card : ℤ)*((n : ℤ)-((negativeArrowPositions p) \ S).card) at h
  rw [Finset.card_sdiff_of_subset hS] at h
  have hcard := Finset.card_le_card hS
  have hcast : (((negativeArrowPositions p).card-S.card : ℕ) : ℤ)=
      ((negativeArrowPositions p).card : ℤ)-(S.card : ℤ) := by omega
  change (∑ i, |displacement p.symm i|) ≤ 2*(∑ i ∈ S, |displacement p.symm i|)+
    (((negativeArrowPositions p).card-S.card : ℕ) : ℤ)*
      ((n : ℤ)-((negativeArrowPositions p).card-S.card : ℕ)) at h
  rw [hcast] at h
  have hn : (n : ℤ)=2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ) := by omega
  unfold negativeSignOffset canonicalEnergyDeficit
  rw [hn] at h ⊢
  nlinarith only [h]

theorem signed_offsets_sum (p : State n) :
    positiveSignOffset p+negativeSignOffset p=
      ((n-p.support.card : ℕ) : ℤ)-(n%2 : ℕ) := by
  classical
  have hdis : Disjoint (positiveArrowPositions p) (negativeArrowPositions p) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hp := (Finset.mem_filter.mp hi).2
    have hn := (Finset.mem_filter.mp hj).2
    omega
  have hunion : positiveArrowPositions p ∪ negativeArrowPositions p=p.support := by
    ext i
    simp only [positiveArrowPositions,negativeArrowPositions,Finset.mem_union,
      Finset.mem_filter,Finset.mem_univ,true_and,mem_support_inverse]
    constructor
    · intro h hh
      simp only [displacement,hh,sub_self,lt_self_iff_false,or_self] at h
    · intro h
      have hv : (p.symm i).val ≠ i.val := fun hh => h (Fin.ext hh)
      unfold displacement
      omega
  have hcount : (positiveArrowPositions p).card+(negativeArrowPositions p).card=p.support.card := by
    rw [← hunion,Finset.card_union_of_disjoint hdis]
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  unfold positiveSignOffset negativeSignOffset
  omega

theorem sign_offset_interval (x eps parity : ℤ) (he : 0 ≤ eps)
    (hp0 : 0 ≤ parity) (hp1 : parity ≤ 1) (hx : x*(x+parity) ≤ eps) :
    -eps-2 ≤ x ∧ x ≤ eps+2 := by
  constructor
  · by_contra h
    have hx0 : x ≤ -eps-3 := by omega
    have h1 := mul_nonneg (show 0 ≤ -x by omega) (show 0 ≤ -x-2 by omega)
    have h2 := mul_nonneg (show 0 ≤ -x by omega) (show 0 ≤ 1-parity by omega)
    nlinarith only [hx,hx0,h1,h2]
  · by_contra h
    have hx0 : eps+3 ≤ x := by omega
    have h1 := mul_nonneg (show 0 ≤ x by omega) (show 0 ≤ x-1 by omega)
    have h2 := mul_nonneg (show 0 ≤ x by omega) hp0
    nlinarith only [hx,hx0,h1,h2]

theorem actual_sign_offset_bounds (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) :
    (-canonicalEnergyDeficit p-2 ≤ positiveSignOffset p ∧
      positiveSignOffset p ≤ canonicalEnergyDeficit p+2) ∧
    (-canonicalEnergyDeficit p-2 ≤ negativeSignOffset p ∧
      negativeSignOffset p ≤ canonicalEnergyDeficit p+2) := by
  have hp := positive_selection_deficit p hmaj ∅ (Finset.empty_subset _)
  have hn := negative_selection_deficit p hmaj ∅ (Finset.empty_subset _)
  simp only [Finset.card_empty,Nat.cast_zero,add_zero,Finset.sum_empty,mul_zero] at hp hn
  have he : 0 ≤ canonicalEnergyDeficit p := by
    unfold canonicalEnergyDeficit
    have h := majorized_canonical_energy p hmaj
    omega
  exact ⟨sign_offset_interval _ _ _ he (by omega) (by omega) hp,
    sign_offset_interval _ _ _ he (by omega) (by omega) hn⟩

#print axioms positive_selection_deficit
#print axioms negative_selection_deficit
#print axioms signed_offsets_sum
#print axioms actual_sign_offset_bounds
end LRX.FiniteCuts

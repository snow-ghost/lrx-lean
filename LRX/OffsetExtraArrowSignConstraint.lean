module

public import LRX.TwoWindowSignedSelection
public import LRX.ZeroEnergyUnitCapacity

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators

/-- Necessary condition preserving the original sign offset for one arrow outside two windows. -/
def OffsetExtraArrowSignConstraint {a b : ℕ} (σ : State a) (τ : State b)
    (parity eps offset sign len : ℤ) : Prop :=
  ∀ (S : Finset (Fin a)) (T : Finset (Fin b)),
    (∀ i ∈ S, 0 < sign*displacement σ i) →
    (∀ i ∈ T, 0 < sign*displacement τ i) →
    (offset+(S.card : ℤ)+(T.card : ℤ)+1)*(offset+(S.card : ℤ)+(T.card : ℤ)+1+parity) ≤
      eps+2*((∑ i ∈ S, |displacement σ i|)+(∑ i ∈ T, |displacement τ i|)+len)

instance {a b : ℕ} (σ : State a) (τ : State b) (parity eps offset sign len : ℤ) :
    Decidable (OffsetExtraArrowSignConstraint σ τ parity eps offset sign len) := by
  unfold OffsetExtraArrowSignConstraint
  infer_instance

variable {n : ℕ} [NeZero n]

theorem original_same_sign_capacity (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (S : Finset (Fin n)) (sign : ℤ) (hsign : sign=1 ∨ sign= -1)
    (hs : ∀ i ∈ S, 0 < sign*displacement p.symm i) :
    let x := if sign=1 then positiveSignOffset p else negativeSignOffset p
    (x+(S.card : ℤ))*(x+(S.card : ℤ)+(n%2 : ℕ)) ≤
      canonicalEnergyDeficit p+2*∑ i ∈ S, |displacement p.symm i| := by
  rcases hsign with hh | hh
  · have hsub : S ⊆ positiveArrowPositions p := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [hh] using hs i hi⟩
    simpa only [hh,ite_true] using positive_selection_deficit p hmaj S hsub
  · have hsub : S ⊆ negativeArrowPositions p := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by have h := hs i hi; rw [hh] at h; linarith⟩
    simpa only [hh,show (-1 : ℤ) ≠ 1 by omega,ite_false] using negative_selection_deficit p hmaj S hsub

end LRX.FiniteCuts

namespace LRX.FiniteWindow
open FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Insert the genuine extra position into the union of both selected images. -/
theorem actual_offset_extra_arrow_constraint (A B : FillingWindow n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (ha : A.Matches p.symm) (hb : B.Matches p.symm) (hab : A.Apart B)
    (i : Fin n) (hia : ¬Contains A.window i) (hib : ¬Contains B.window i)
    (sign : ℤ) (hsign : sign=1 ∨ sign= -1)
    (hi : 0 < sign*displacement p.symm i) :
    OffsetExtraArrowSignConstraint A.filling B.filling (n%2 : ℕ) (canonicalEnergyDeficit p)
      (if sign=1 then positiveSignOffset p else negativeSignOffset p) sign |displacement p.symm i| := by
  classical
  intro S T hS hT
  let U := S.image (embed A.window) ∪ T.image (embed B.window)
  have hnot : i ∉ U := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp h
      exact hia (hj ▸ contains_embed A.window j)
    · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp h
      exact hib (hj ▸ contains_embed B.window j)
  have hsigns : ∀ j ∈ insert i U, 0 < sign*displacement p.symm j := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · rcases Finset.mem_union.mp hj with hj | hj
      · obtain ⟨a,haS,rfl⟩ := Finset.mem_image.mp hj
        rw [matching_window_displacement A.window p.symm A.filling ha]
        exact hS a haS
      · obtain ⟨b,hbT,rfl⟩ := Finset.mem_image.mp hj
        rw [matching_window_displacement B.window p.symm B.filling hb]
        exact hT b hbT
  have h := original_same_sign_capacity p hmaj (insert i U) sign hsign hsigns
  obtain ⟨hcard,hmass⟩ := two_window_selected_mass A B p.symm ha hb hab S T
  change U.card=S.card+T.card at hcard
  change (∑ j ∈ U, |displacement p.symm j|)=_ at hmass
  rw [Finset.card_insert_of_notMem hnot,Finset.sum_insert hnot,hcard,Nat.cast_add,
    Nat.cast_add,Nat.cast_one,hmass] at h
  dsimp only at h
  nlinarith only [h]

#print axioms LRX.FiniteCuts.original_same_sign_capacity
#print axioms actual_offset_extra_arrow_constraint
end LRX.FiniteWindow

module

public import LRX.WindowSignedSelection

@[expose] public section

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n : ℕ} [NeZero n]

theorem apart_window_selections_disjoint (A B : FillingWindow n) (hab : A.Apart B)
    (S : Finset (Fin A.size)) (T : Finset (Fin B.size)) :
    Disjoint (S.image (embed A.window)) (T.image (embed B.window)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hj
  apply hab (embed A.window a) (contains_embed A.window a)
  rw [← hb]
  exact contains_embed B.window b

theorem two_window_selected_mass (A B : FillingWindow n) (p : State n)
    (ha : A.Matches p) (hb : B.Matches p) (hab : A.Apart B)
    (S : Finset (Fin A.size)) (T : Finset (Fin B.size)) :
    (S.image (embed A.window) ∪ T.image (embed B.window)).card=S.card+T.card ∧
    (∑ i ∈ S.image (embed A.window) ∪ T.image (embed B.window), |displacement p i|)=
      (∑ i ∈ S, |displacement A.filling i|)+(∑ i ∈ T, |displacement B.filling i|) := by
  have hd := apart_window_selections_disjoint A B hab S T
  obtain ⟨hca,hma⟩ := matching_window_selected_mass A p ha S
  obtain ⟨hcb,hmb⟩ := matching_window_selected_mass B p hb T
  exact ⟨by rw [Finset.card_union_of_disjoint hd,hca,hcb],
    by rw [Finset.sum_union hd,hma,hmb]⟩

theorem two_window_positive_selection (A B : FillingWindow n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (ha : A.Matches p.symm) (hb : B.Matches p.symm) (hab : A.Apart B)
    (S : Finset (Fin A.size)) (T : Finset (Fin B.size))
    (hS : ∀ i ∈ S, 0 < displacement A.filling i)
    (hT : ∀ i ∈ T, 0 < displacement B.filling i) :
    (positiveSignOffset p+(S.card : ℤ)+(T.card : ℤ))*
      (positiveSignOffset p+(S.card : ℤ)+(T.card : ℤ)+(n%2 : ℕ)) ≤
      canonicalEnergyDeficit p+2*((∑ i ∈ S, |displacement A.filling i|)+
        (∑ i ∈ T, |displacement B.filling i|)) := by
  classical
  have hs : S.image (embed A.window) ∪ T.image (embed B.window) ⊆ positiveArrowPositions p := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [matching_window_displacement A.window p.symm A.filling ha]
      exact hS j hj
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [matching_window_displacement B.window p.symm B.filling hb]
      exact hT j hj
  have h := positive_selection_deficit p hmaj _ hs
  obtain ⟨hcard,hmass⟩ := two_window_selected_mass A B p.symm ha hb hab S T
  rw [hcard,Nat.cast_add,hmass] at h
  simpa only [add_assoc] using h

theorem two_window_negative_selection (A B : FillingWindow n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (ha : A.Matches p.symm) (hb : B.Matches p.symm) (hab : A.Apart B)
    (S : Finset (Fin A.size)) (T : Finset (Fin B.size))
    (hS : ∀ i ∈ S, displacement A.filling i < 0)
    (hT : ∀ i ∈ T, displacement B.filling i < 0) :
    (negativeSignOffset p+(S.card : ℤ)+(T.card : ℤ))*
      (negativeSignOffset p+(S.card : ℤ)+(T.card : ℤ)+(n%2 : ℕ)) ≤
      canonicalEnergyDeficit p+2*((∑ i ∈ S, |displacement A.filling i|)+
        (∑ i ∈ T, |displacement B.filling i|)) := by
  classical
  have hs : S.image (embed A.window) ∪ T.image (embed B.window) ⊆ negativeArrowPositions p := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [matching_window_displacement A.window p.symm A.filling ha]
      exact hS j hj
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [matching_window_displacement B.window p.symm B.filling hb]
      exact hT j hj
  have h := negative_selection_deficit p hmaj _ hs
  obtain ⟨hcard,hmass⟩ := two_window_selected_mass A B p.symm ha hb hab S T
  rw [hcard,Nat.cast_add,hmass] at h
  simpa only [add_assoc] using h

#print axioms two_window_positive_selection
#print axioms two_window_negative_selection
end LRX.FiniteWindow

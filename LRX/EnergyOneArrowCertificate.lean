module

public import LRX.OffsetExtraArrowSignConstraint
public import LRX.EnergyOneEmptyCatalogues

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem energy_one_nonempty_shape_check : ∀ f : Fin 3,
    (filteredExteriorCatalogue 0 1 f.val 0 (if f.val=0 then 4 else 6)).all (fun z => decide
      ((z.1.1-z.1.2.support.card)+(z.2.1-z.2.2.support.card)=f.val ∧
       ∀ j : Fin 7, let xp := (j.val : ℤ)-3; let xm := (f.val : ℤ)-xp
         LocalPairSignConstraints z.1.2 z.2.2 0 1 xp xm →
         ∀ s : Fin 2, ∀ l : Fin 2, (l.val=0 ∨ f.val=2) →
           ¬OffsetExtraArrowSignConstraint z.1.2 z.2.2 0 1
             (if s.val=0 then xp else xm) (if s.val=0 then 1 else -1) ((l.val : ℤ)+1)))=true := by
  decide +kernel

theorem energy_one_pair_fixed_count (A B : SmallExteriorMap) (f : ℕ) (hf : f ≤ 2)
    (hm : (A,B) ∈ filteredExteriorCatalogue 0 1 f 0 (if f=0 then 4 else 6)) :
    (A.1-A.2.support.card)+(B.1-B.2.support.card)=f := by
  exact (of_decide_eq_true (List.all_eq_true.mp (energy_one_nonempty_shape_check ⟨f,by omega⟩) (A,B) hm)).1

theorem energy_one_pair_forbids_extra (A B : SmallExteriorMap) (f : ℕ) (hf : f ≤ 2)
    (hm : (A,B) ∈ filteredExteriorCatalogue 0 1 f 0 (if f=0 then 4 else 6))
    (xp xm : ℤ) (hsum : xp+xm=(f : ℤ)) (hlo : -3 ≤ xp) (hhi : xp ≤ 3)
    (hc : LocalPairSignConstraints A.2 B.2 0 1 xp xm)
    (sign len : ℤ) (hs : sign=1 ∨ sign= -1) (hl : len=1 ∨ (f=2 ∧ len=2)) :
    ¬OffsetExtraArrowSignConstraint A.2 B.2 0 1
      (if sign=1 then xp else xm) sign len := by
  have hh := (of_decide_eq_true (List.all_eq_true.mp (energy_one_nonempty_shape_check ⟨f,by omega⟩) (A,B) hm)).2
  let j : Fin 7 := ⟨(xp+3).toNat,by omega⟩
  have hj : (j.val : ℤ)-3=xp := by dsimp only [j]; omega
  have hm' : (f : ℤ)-xp=xm := by omega
  have h := hh j
  dsimp only at h
  rw [hj,hm'] at h
  have h' := h hc
  rcases hs with rfl | rfl <;> rcases hl with rfl | ⟨hf2,rfl⟩
  · simpa using h' 0 0 (Or.inl rfl)
  · simpa using h' 0 1 (Or.inr hf2)
  · simpa using h' 1 0 (Or.inl rfl)
  · simpa using h' 1 1 (Or.inr hf2)

#print axioms energy_one_nonempty_shape_check
#print axioms energy_one_pair_fixed_count
#print axioms energy_one_pair_forbids_extra
end LRX.FiniteCuts

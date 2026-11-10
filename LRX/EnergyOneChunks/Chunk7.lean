module

public import LRX.EnergyOneRows

@[expose] public section

namespace LRX.FinitePeak
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem energy_one_outer_chunk_7_m0 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (0 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (0 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m1 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (1 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (1 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m2 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (2 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (2 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m3 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (3 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (3 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m4 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (4 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (4 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m5 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (5 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (5 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m6 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (6 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (6 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m7 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (7 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (7 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m8 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (8 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (8 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m9 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (9 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (9 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m10 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (10 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (10 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m11 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (11 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (11 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m12 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (12 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (12 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m13 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (13 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (13 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m14 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (14 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (14 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m15 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (15 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (15 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m16 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (16 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (16 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m17 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (17 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (17 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m18 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (18 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (18 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m19 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (19 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (19 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m20 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (20 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (20 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m21 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (21 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (21 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m22 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (22 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (22 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m23 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (23 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (23 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m24 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (24 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (24 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m25 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (25 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (25 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m26 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (26 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (26 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m27 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (27 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (27 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m28 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (28 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (28 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m29 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (29 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (29 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m30 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (30 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (30 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m31 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (31 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (31 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m32 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (32 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (32 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m33 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (33 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (33 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m34 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (34 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (34 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m35 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (35 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (35 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

private theorem energy_one_outer_chunk_7_m36 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ¬TwoSizeNecessary (twoProfileOfOuter o (36 : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (36 : ℤ) (x.val : ℤ)).Admissible))=true := by
  decide +kernel

theorem energy_one_outer_chunk_7 :
    ((boundedEnergyOneRows.drop 21).take 3).all (fun o => decide
      (o ∈ energyOneOuterRows ∨ ∀ m : Fin 37,
      ¬TwoSizeNecessary (twoProfileOfOuter o (m.val : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (m.val : ℤ) (x.val : ℤ)).Admissible))=true := by
  apply List.all_eq_true.mpr
  intro o ho
  apply decide_eq_true
  by_cases h : o ∈ energyOneOuterRows
  · exact Or.inl h
  · right
    intro m
    fin_cases m
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m0 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m1 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m2 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m3 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m4 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m5 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m6 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m7 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m8 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m9 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m10 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m11 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m12 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m13 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m14 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m15 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m16 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m17 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m18 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m19 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m20 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m21 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m22 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m23 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m24 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m25 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m26 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m27 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m28 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m29 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m30 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m31 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m32 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m33 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m34 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m35 o ho)).resolve_left h
    · exact (of_decide_eq_true (List.all_eq_true.mp energy_one_outer_chunk_7_m36 o ho)).resolve_left h

#print axioms energy_one_outer_chunk_7
end LRX.FinitePeak

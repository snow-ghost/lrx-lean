module

public import LRX.TwoOuterBounds
public import LRX.ThreeOuterTable

@[expose] public section

namespace LRX.FinitePeak

def twoOuterRows : List OuterRow := [
  (0,0,0,0,1,4),
  (0,0,0,0,2,4),
  (0,0,0,0,2,6),
  (0,0,0,0,2,7),
  (0,0,0,0,3,4),
  (0,0,0,0,3,6),
  (0,0,0,0,3,7),
  (0,0,0,0,3,8),
  (0,0,0,0,3,9),
  (0,0,0,0,4,4),
  (0,0,0,0,4,6),
  (0,0,0,0,4,7),
  (0,0,0,0,4,8),
  (0,0,0,0,4,9),
  (0,0,0,0,4,10),
  (0,0,0,0,4,11),
  (0,0,0,0,5,4),
  (0,0,0,0,5,6),
  (0,0,0,0,5,7),
  (0,0,0,0,5,8),
  (0,0,0,0,5,9),
  (0,0,0,0,5,10),
  (0,0,0,0,5,11),
  (0,0,0,0,5,12),
  (0,0,0,0,5,13),
  (0,0,1,0,1,4),
  (0,0,1,0,1,5),
  (0,0,1,0,2,4),
  (0,0,1,0,2,5),
  (0,0,1,0,2,6),
  (0,0,1,0,2,7),
  (0,0,1,0,3,4),
  (0,0,1,0,3,5),
  (0,0,1,0,3,6),
  (0,0,1,0,3,7),
  (0,0,1,0,3,8),
  (0,0,1,0,3,9),
  (0,0,2,0,1,4),
  (0,1,1,0,1,5),
  (0,1,1,0,2,5),
  (0,1,1,0,2,6),
  (0,1,1,0,2,7),
  (0,1,1,0,3,5),
  (0,1,1,0,3,6),
  (0,1,1,0,3,7),
  (0,1,1,0,3,8),
  (0,1,1,0,3,9),
  (0,1,1,0,4,5),
  (0,1,1,0,4,6),
  (0,1,1,0,4,7),
  (0,1,1,0,4,8),
  (0,1,1,0,4,9),
  (0,1,1,0,4,10),
  (0,1,1,0,4,11),
  (0,1,1,1,3,5),
  (0,1,1,1,4,5),
  (0,1,1,1,4,6),
  (0,1,2,0,1,4),
  (0,1,2,0,2,4),
  (0,1,2,0,2,5),
  (0,1,2,0,2,6),
  (0,2,1,0,2,6),
  (0,2,1,0,2,7),
  (0,2,1,0,3,6),
  (0,2,1,0,3,7),
  (0,2,1,0,3,8),
  (0,2,1,0,3,9),
  (0,2,1,0,4,6),
  (0,2,1,0,4,7),
  (0,2,1,0,4,8),
  (0,2,1,0,4,9),
  (0,2,1,0,4,10),
  (0,2,1,0,4,11),
  (0,2,1,0,5,6),
  (0,2,1,0,5,7),
  (0,2,1,0,5,8),
  (0,2,1,0,5,9),
  (0,2,1,0,5,10),
  (0,2,1,0,5,11),
  (0,2,1,0,5,12),
  (0,2,1,0,5,13),
  (0,2,1,1,4,6),
  (0,2,1,1,5,6),
  (0,2,1,1,5,7),
  (0,2,1,1,5,8),
  (0,2,1,2,6,6),
  (0,2,1,2,7,6),
  (0,2,1,2,7,7),
  (0,2,2,0,1,5),
  (0,2,2,0,2,5),
  (0,2,2,0,2,6),
  (0,2,2,0,2,7),
  (0,2,2,0,3,5),
  (0,2,2,0,3,6),
  (0,2,2,0,3,7),
  (0,2,2,0,3,8),
  (0,2,2,0,3,9),
  (0,2,2,1,3,5),
  (0,2,2,2,5,5),
  (0,3,3,0,2,6),
  (1,0,0,0,1,4),
  (1,0,0,0,1,5),
  (1,0,0,0,2,4),
  (1,0,0,0,2,5),
  (1,0,0,0,2,6),
  (1,0,0,0,2,7),
  (1,0,0,0,3,4),
  (1,0,0,0,3,5),
  (1,0,0,0,3,6),
  (1,0,0,0,3,7),
  (1,0,0,0,3,8),
  (1,0,0,0,3,9),
  (1,0,0,0,4,4),
  (1,0,0,0,4,5),
  (1,0,0,0,4,6),
  (1,0,0,0,4,7),
  (1,0,0,0,4,8),
  (1,0,0,0,4,9),
  (1,0,0,0,4,10),
  (1,0,0,0,4,11),
  (1,0,1,0,1,4),
  (1,0,1,0,2,4),
  (1,0,1,0,2,5),
  (1,0,1,0,2,6),
  (1,1,0,0,1,5),
  (1,1,0,0,2,5),
  (1,1,0,0,2,6),
  (1,1,0,0,2,7),
  (1,1,0,0,3,5),
  (1,1,0,0,3,6),
  (1,1,0,0,3,7),
  (1,1,0,0,3,8),
  (1,1,0,0,3,9),
  (1,1,0,0,4,5),
  (1,1,0,0,4,6),
  (1,1,0,0,4,7),
  (1,1,0,0,4,8),
  (1,1,0,0,4,9),
  (1,1,0,0,4,10),
  (1,1,0,0,4,11),
  (1,1,0,0,5,5),
  (1,1,0,0,5,6),
  (1,1,0,0,5,7),
  (1,1,0,0,5,8),
  (1,1,0,0,5,9),
  (1,1,0,0,5,10),
  (1,1,0,0,5,11),
  (1,1,0,0,5,12),
  (1,1,0,0,5,13),
  (1,1,0,1,3,5),
  (1,1,0,1,4,5),
  (1,1,0,1,4,6),
  (1,1,0,1,5,5),
  (1,1,0,1,5,6),
  (1,1,0,1,5,7),
  (1,1,1,0,2,5),
  (1,1,1,0,2,6),
  (1,1,1,0,3,5),
  (1,1,1,0,3,6),
  (1,1,1,0,3,7),
  (1,1,1,0,3,8),
  (1,1,1,1,3,5),
  (1,1,2,0,1,4),
  (1,2,1,0,2,6),
  (1,2,1,0,2,7),
  (1,2,1,0,3,6),
  (1,2,1,0,3,7),
  (1,2,1,0,3,8),
  (1,2,1,0,3,9),
  (1,2,1,0,4,6),
  (1,2,1,0,4,7),
  (1,2,1,0,4,8),
  (1,2,1,0,4,9),
  (1,2,1,0,4,10),
  (1,2,1,0,4,11),
  (1,2,1,1,4,6),
  (1,2,1,2,6,6),
  (1,2,2,0,2,5),
  (1,2,2,0,2,6),
  (1,3,2,0,2,6),
  (1,3,2,0,3,6),
  (1,3,2,0,3,7),
  (1,3,2,0,3,8)]

instance (p f e a U v : ℤ) : Decidable (TwoOuter p f e a U v) := by
  unfold TwoOuter
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem checked_two_outer_00 : ∀ (e : Fin 4) (a : Fin 3) (u : Fin 7) (v : Fin 10),
    TwoOuter 0 0 e.val a.val (u.val+1) (v.val+4) →
    (0,0,(e.val : ℤ),(a.val : ℤ),(u.val : ℤ)+1,(v.val : ℤ)+4) ∈ twoOuterRows := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem checked_two_outer_01 : ∀ (e : Fin 4) (a : Fin 3) (u : Fin 7) (v : Fin 10),
    TwoOuter 0 1 e.val a.val (u.val+1) (v.val+4) →
    (0,1,(e.val : ℤ),(a.val : ℤ),(u.val : ℤ)+1,(v.val : ℤ)+4) ∈ twoOuterRows := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem checked_two_outer_02 : ∀ (e : Fin 4) (a : Fin 3) (u : Fin 7) (v : Fin 10),
    TwoOuter 0 2 e.val a.val (u.val+1) (v.val+4) →
    (0,2,(e.val : ℤ),(a.val : ℤ),(u.val : ℤ)+1,(v.val : ℤ)+4) ∈ twoOuterRows := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem checked_two_outer_03 : ∀ (e : Fin 4) (a : Fin 3) (u : Fin 7) (v : Fin 10),
    TwoOuter 0 3 e.val a.val (u.val+1) (v.val+4) →
    (0,3,(e.val : ℤ),(a.val : ℤ),(u.val : ℤ)+1,(v.val : ℤ)+4) ∈ twoOuterRows := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem checked_two_outer_10 : ∀ (e : Fin 4) (a : Fin 3) (u : Fin 7) (v : Fin 10),
    TwoOuter 1 0 e.val a.val (u.val+1) (v.val+4) →
    (1,0,(e.val : ℤ),(a.val : ℤ),(u.val : ℤ)+1,(v.val : ℤ)+4) ∈ twoOuterRows := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem checked_two_outer_11 : ∀ (e : Fin 4) (a : Fin 3) (u : Fin 7) (v : Fin 10),
    TwoOuter 1 1 e.val a.val (u.val+1) (v.val+4) →
    (1,1,(e.val : ℤ),(a.val : ℤ),(u.val : ℤ)+1,(v.val : ℤ)+4) ∈ twoOuterRows := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem checked_two_outer_12 : ∀ (e : Fin 4) (a : Fin 3) (u : Fin 7) (v : Fin 10),
    TwoOuter 1 2 e.val a.val (u.val+1) (v.val+4) →
    (1,2,(e.val : ℤ),(a.val : ℤ),(u.val : ℤ)+1,(v.val : ℤ)+4) ∈ twoOuterRows := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem checked_two_outer_13 : ∀ (e : Fin 4) (a : Fin 3) (u : Fin 7) (v : Fin 10),
    TwoOuter 1 3 e.val a.val (u.val+1) (v.val+4) →
    (1,3,(e.val : ℤ),(a.val : ℤ),(u.val : ℤ)+1,(v.val : ℤ)+4) ∈ twoOuterRows := by
  decide +kernel

theorem checked_two_outer_table : ∀ (p : Fin 2) (f e : Fin 4) (a : Fin 3) (u : Fin 7) (v : Fin 10),
    TwoOuter p.val f.val e.val a.val (u.val+1) (v.val+4) →
    ((p.val : ℤ),(f.val : ℤ),(e.val : ℤ),(a.val : ℤ),(u.val : ℤ)+1,(v.val : ℤ)+4) ∈ twoOuterRows := by
  intro p f
  fin_cases p <;> fin_cases f
  · exact checked_two_outer_00
  · exact checked_two_outer_01
  · exact checked_two_outer_02
  · exact checked_two_outer_03
  · exact checked_two_outer_10
  · exact checked_two_outer_11
  · exact checked_two_outer_12
  · exact checked_two_outer_13

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem checked_two_outer_sound : twoOuterRows.all (fun r =>
    decide (TwoOuter r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2))=true := by
  decide +kernel

#print axioms checked_two_outer_table
#print axioms checked_two_outer_sound
end LRX.FinitePeak

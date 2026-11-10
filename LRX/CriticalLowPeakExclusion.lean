module

public import LRX.FinitePeakProfile

@[expose] public section

namespace LRX.FinitePeak

def criticalLowProfile (m u x : ℕ) : Profile :=
  ⟨2,m,0,0,0,0,u,4,x⟩

set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem critical_low_peak_check_m0 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 0 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m1 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 1 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m2 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 2 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m3 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 3 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m4 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 4 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m5 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 5 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m6 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 6 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m7 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 7 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m8 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 8 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m9 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 9 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m10 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 10 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m11 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 11 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m12 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 12 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m13 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 13 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m14 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 14 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m15 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 15 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m16 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 16 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m17 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 17 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m18 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 18 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m19 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 19 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m20 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 20 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m21 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 21 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m22 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 22 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m23 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 23 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m24 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 24 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m25 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 25 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m26 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 26 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m27 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 27 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m28 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 28 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m29 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 29 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m30 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 30 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m31 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 31 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m32 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 32 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m33 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 33 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m34 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 34 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m35 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 35 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

private theorem critical_low_peak_check_m36 : ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile 36 u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  decide +kernel

theorem critical_low_peak_check : ∀ m : Fin 37, ∀ u : Fin 4, ∀ x : Fin 65,
    let r := criticalLowProfile m.val u.val x.val
    ¬(r.Admissible ∧ (r.holes=0 ∨ r.holes ≤ 2*r.T-5)) := by
  intro m
  fin_cases m
  · exact critical_low_peak_check_m0
  · exact critical_low_peak_check_m1
  · exact critical_low_peak_check_m2
  · exact critical_low_peak_check_m3
  · exact critical_low_peak_check_m4
  · exact critical_low_peak_check_m5
  · exact critical_low_peak_check_m6
  · exact critical_low_peak_check_m7
  · exact critical_low_peak_check_m8
  · exact critical_low_peak_check_m9
  · exact critical_low_peak_check_m10
  · exact critical_low_peak_check_m11
  · exact critical_low_peak_check_m12
  · exact critical_low_peak_check_m13
  · exact critical_low_peak_check_m14
  · exact critical_low_peak_check_m15
  · exact critical_low_peak_check_m16
  · exact critical_low_peak_check_m17
  · exact critical_low_peak_check_m18
  · exact critical_low_peak_check_m19
  · exact critical_low_peak_check_m20
  · exact critical_low_peak_check_m21
  · exact critical_low_peak_check_m22
  · exact critical_low_peak_check_m23
  · exact critical_low_peak_check_m24
  · exact critical_low_peak_check_m25
  · exact critical_low_peak_check_m26
  · exact critical_low_peak_check_m27
  · exact critical_low_peak_check_m28
  · exact critical_low_peak_check_m29
  · exact critical_low_peak_check_m30
  · exact critical_low_peak_check_m31
  · exact critical_low_peak_check_m32
  · exact critical_low_peak_check_m33
  · exact critical_low_peak_check_m34
  · exact critical_low_peak_check_m35
  · exact critical_low_peak_check_m36


#print axioms critical_low_peak_check
end LRX.FinitePeak

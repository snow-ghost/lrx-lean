module

public import LRX.FinitePeakProfile

@[expose] public section

namespace LRX.FinitePeak

def oddFullFiveLowProfile (m u x : ℕ) : Profile :=
  ⟨2,m,1,0,0,0,u,5,x⟩

set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem odd_full_five_low_peak_check_m0 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 0 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m1 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 1 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m2 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 2 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m3 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 3 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m4 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 4 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m5 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 5 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m6 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 6 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m7 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 7 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m8 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 8 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m9 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 9 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m10 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 10 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m11 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 11 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m12 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 12 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m13 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 13 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m14 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 14 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m15 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 15 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m16 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 16 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m17 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 17 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m18 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 18 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m19 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 19 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m20 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 20 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m21 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 21 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m22 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 22 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m23 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 23 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m24 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 24 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m25 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 25 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m26 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 26 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m27 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 27 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m28 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 28 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m29 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 29 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m30 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 30 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m31 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 31 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m32 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 32 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m33 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 33 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m34 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 34 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m35 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 35 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_full_five_low_peak_check_m36 : ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile 36 u.val x.val
    ¬r.Admissible := by
  decide +kernel

/-- Same complete finite exclusion, with independent kernel checks
for each first coordinate to keep memory below the project limit. -/
theorem odd_full_five_low_peak_check : ∀ m : Fin 37, ∀ u : Fin 3, ∀ x : Fin 65,
    let r := oddFullFiveLowProfile m.val u.val x.val
    ¬r.Admissible := by
  intro m
  fin_cases m
  · exact odd_full_five_low_peak_check_m0
  · exact odd_full_five_low_peak_check_m1
  · exact odd_full_five_low_peak_check_m2
  · exact odd_full_five_low_peak_check_m3
  · exact odd_full_five_low_peak_check_m4
  · exact odd_full_five_low_peak_check_m5
  · exact odd_full_five_low_peak_check_m6
  · exact odd_full_five_low_peak_check_m7
  · exact odd_full_five_low_peak_check_m8
  · exact odd_full_five_low_peak_check_m9
  · exact odd_full_five_low_peak_check_m10
  · exact odd_full_five_low_peak_check_m11
  · exact odd_full_five_low_peak_check_m12
  · exact odd_full_five_low_peak_check_m13
  · exact odd_full_five_low_peak_check_m14
  · exact odd_full_five_low_peak_check_m15
  · exact odd_full_five_low_peak_check_m16
  · exact odd_full_five_low_peak_check_m17
  · exact odd_full_five_low_peak_check_m18
  · exact odd_full_five_low_peak_check_m19
  · exact odd_full_five_low_peak_check_m20
  · exact odd_full_five_low_peak_check_m21
  · exact odd_full_five_low_peak_check_m22
  · exact odd_full_five_low_peak_check_m23
  · exact odd_full_five_low_peak_check_m24
  · exact odd_full_five_low_peak_check_m25
  · exact odd_full_five_low_peak_check_m26
  · exact odd_full_five_low_peak_check_m27
  · exact odd_full_five_low_peak_check_m28
  · exact odd_full_five_low_peak_check_m29
  · exact odd_full_five_low_peak_check_m30
  · exact odd_full_five_low_peak_check_m31
  · exact odd_full_five_low_peak_check_m32
  · exact odd_full_five_low_peak_check_m33
  · exact odd_full_five_low_peak_check_m34
  · exact odd_full_five_low_peak_check_m35
  · exact odd_full_five_low_peak_check_m36

#print axioms odd_full_five_low_peak_check
end LRX.FinitePeak

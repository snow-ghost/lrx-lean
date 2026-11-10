module

public import LRX.FinitePeakProfile

@[expose] public section

namespace LRX.FinitePeak

def oddOneSevenLowProfile (m u x : ℕ) : Profile :=
  ⟨2,m,1,1,0,0,u,7,x⟩

set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem odd_one_seven_low_check_m0 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 0 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m1 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 1 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m2 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 2 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m3 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 3 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m4 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 4 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m5 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 5 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m6 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 6 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m7 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 7 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m8 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 8 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m9 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 9 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m10 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 10 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m11 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 11 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m12 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 12 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m13 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 13 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m14 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 14 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m15 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 15 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m16 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 16 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m17 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 17 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m18 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 18 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m19 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 19 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m20 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 20 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m21 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 21 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m22 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 22 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m23 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 23 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m24 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 24 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m25 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 25 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m26 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 26 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m27 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 27 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m28 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 28 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m29 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 29 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m30 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 30 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m31 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 31 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m32 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 32 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m33 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 33 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m34 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 34 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m35 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 35 u.val x.val
    ¬r.Admissible := by
  decide +kernel

private theorem odd_one_seven_low_check_m36 : ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile 36 u.val x.val
    ¬r.Admissible := by
  decide +kernel

/-- Same complete finite exclusion, with independent kernel checks
for each first coordinate to keep memory below the project limit. -/
theorem odd_one_seven_low_check : ∀ m : Fin 37, ∀ u : Fin 5, ∀ x : Fin 63,
    let r := oddOneSevenLowProfile m.val u.val x.val
    ¬r.Admissible := by
  intro m
  fin_cases m
  · exact odd_one_seven_low_check_m0
  · exact odd_one_seven_low_check_m1
  · exact odd_one_seven_low_check_m2
  · exact odd_one_seven_low_check_m3
  · exact odd_one_seven_low_check_m4
  · exact odd_one_seven_low_check_m5
  · exact odd_one_seven_low_check_m6
  · exact odd_one_seven_low_check_m7
  · exact odd_one_seven_low_check_m8
  · exact odd_one_seven_low_check_m9
  · exact odd_one_seven_low_check_m10
  · exact odd_one_seven_low_check_m11
  · exact odd_one_seven_low_check_m12
  · exact odd_one_seven_low_check_m13
  · exact odd_one_seven_low_check_m14
  · exact odd_one_seven_low_check_m15
  · exact odd_one_seven_low_check_m16
  · exact odd_one_seven_low_check_m17
  · exact odd_one_seven_low_check_m18
  · exact odd_one_seven_low_check_m19
  · exact odd_one_seven_low_check_m20
  · exact odd_one_seven_low_check_m21
  · exact odd_one_seven_low_check_m22
  · exact odd_one_seven_low_check_m23
  · exact odd_one_seven_low_check_m24
  · exact odd_one_seven_low_check_m25
  · exact odd_one_seven_low_check_m26
  · exact odd_one_seven_low_check_m27
  · exact odd_one_seven_low_check_m28
  · exact odd_one_seven_low_check_m29
  · exact odd_one_seven_low_check_m30
  · exact odd_one_seven_low_check_m31
  · exact odd_one_seven_low_check_m32
  · exact odd_one_seven_low_check_m33
  · exact odd_one_seven_low_check_m34
  · exact odd_one_seven_low_check_m35
  · exact odd_one_seven_low_check_m36

#print axioms odd_one_seven_low_check
end LRX.FinitePeak


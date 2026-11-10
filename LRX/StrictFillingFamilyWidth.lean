import LRX.TightFillingResource
import LRX.FillingFamilyResource

namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ}

set_option maxHeartbeats 1200000 in
/-- A nonempty fixed-free nonshort family cannot attain the defect-two
width bound. All sums refer to this same actual family. -/
theorem nonshort_family_strict_width (As : List (FillingWindow n)) (T : ℤ)
    (hf : ∀ A ∈ As, A.filling.support.card=A.size)
    (hmin : ∀ A ∈ As, ∀ i, 3 ≤ |displacement A.filling i|)
    (hbudget : (As.map FillingWindow.resource).sum ≤ T)
    (hwidth : 0 < (As.map (fun A => (A.size : ℤ))).sum)
    (hdef : 2 ≤ (As.map (fun A => cycleDefect A.filling)).sum) :
    (As.map (fun A => (A.size : ℤ))).sum ≤ 2*T-5 := by
  classical
  let K := (As.map FillingWindow.resource).sum
  let Z := (As.map (fun A => cycleDefect A.filling)).sum
  let W := (As.map (fun A => (A.size : ℤ))).sum
  let slack := fun A : FillingWindow n => 2*A.resource-2*cycleDefect A.filling-(A.size : ℤ)
  have hnon (A : FillingWindow n) (hA : A ∈ As) : 0 ≤ slack A := by
    have hh := filling_resource_width_defect A.filling
    rw [hf A hA,Nat.sub_self] at hh
    simp only [Nat.cast_zero,add_zero] at hh
    change 0 ≤ 2*fillingResource A.filling-2*cycleDefect A.filling-(A.size : ℤ)
    omega
  have hidentity (xs : List (FillingWindow n)) :
      (xs.map slack).sum=2*(xs.map FillingWindow.resource).sum-
        2*(xs.map (fun A => cycleDefect A.filling)).sum-
        (xs.map (fun A => (A.size : ℤ))).sum := by
    induction xs with
    | nil => simp
    | cons A xs ih =>
      simp only [List.map_cons,List.sum_cons,ih]
      dsimp only [slack]
      ring
  have hsum := hidentity As
  change (As.map slack).sum=2*K-2*Z-W at hsum
  have hsumNon : 0 ≤ (As.map slack).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hz
    exact hnon A hA
  change K ≤ T at hbudget
  change 0 < W at hwidth
  change 2 ≤ Z at hdef
  change W ≤ 2*T-5
  by_cases hz : 3 ≤ Z
  · omega
  have hZ : Z=2 := by omega
  have hex : ∃ A ∈ As, 0 < A.size := by
    by_contra! hh
    have hm : As.map (fun A => (A.size : ℤ))=As.map (fun _ => (0 : ℤ)) :=
      List.map_congr_left (fun A hA => by have := hh A hA; simp [show A.size=0 by omega])
    have hW : W=0 := by dsimp only [W]; rw [hm]; simp
    omega
  obtain ⟨A,hA,hsize⟩ := hex
  have hznon (B : FillingWindow n) : 0 ≤ cycleDefect B.filling := by
    have hh := finite_depth_rank B.filling
    unfold cycleDefect
    omega
  have hsingle : cycleDefect A.filling ≤ Z := by
    apply List.single_le_sum
    · intro z hz
      obtain ⟨B,_,rfl⟩ := List.mem_map.mp hz
      exact hznon B
    · exact List.mem_map.mpr ⟨A,hA,rfl⟩
  have hs := nonshort_small_defect_strict_width A.filling hsize (hf A hA) (hmin A hA) (hsingle.trans_eq hZ)
  have hslack : 1 ≤ slack A := by
    change 1 ≤ 2*fillingResource A.filling-2*cycleDefect A.filling-(A.size : ℤ)
    linarith only [hs]
  have hsingleSlack : slack A ≤ (As.map slack).sum := by
    apply List.single_le_sum
    · intro z hz
      obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hz
      exact hnon B hB
    · exact List.mem_map.mpr ⟨A,hA,rfl⟩
  linarith only [hsum,hsingleSlack,hslack,hbudget,hZ]

#print axioms nonshort_family_strict_width
end LRX.FiniteWindow

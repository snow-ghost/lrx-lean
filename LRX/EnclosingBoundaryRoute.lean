module

public import LRX.EnclosingSelectedArcWord

@[expose] public section

namespace LRX.RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem service_savings_sum (ss : List (ExactService n)) :
    (ss.map (fun a => (∑ i, |a.displacement i|)-
      (BufferProgram.rotations a.service.word : ℤ))).sum=
    (ss.map (fun a => ∑ i, |a.displacement i|)).sum-
      (ss.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum := by
  induction ss with
  | nil => simp
  | cons a ss ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; ring

end LRX.RotationWords

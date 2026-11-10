module

public import LRX.FiniteRankInverse
public import LRX.PhysicalModel
public import LRX.AffineDeletion

@[expose] public section

namespace LRX.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open FiniteRankOrder
variable {n : ℕ} [NeZero n]

/-- A finite sorting word: every X is an adjacent descent inside the
coordinate window. L/R may cross the coordinate cut. -/
def DescendingWord : List Letter → Configuration n → Prop
  | [], _ => True
  | .l::w, s => DescendingWord w (step .l s)
  | .r::w, s => DescendingWord w (step .r s)
  | .x::w, s =>
      (s.cursor+1).val=s.cursor.val+1 ∧
      (s.tokens (s.cursor+1)).val < (s.tokens s.cursor).val ∧
      DescendingWord w (step .x s)

end LRX.PhysicalModel

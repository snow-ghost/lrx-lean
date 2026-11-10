import LRX.Cycle11StructuralBridge

namespace LRX.Cycle11WordSymmetry
open LRX.BlockExchange LRX.ReducedPrice
variable {α : Type*}

def reflect : List α → List α
  | a::b::t => b::a::t.reverse
  | t => t

theorem reflect_as_reverse (s : List α) : reflect s=run (spin (-2)) s.reverse := by
  change reflect s=run [.R,.R] s.reverse
  cases s with
  | nil => rfl
  | cons a t => cases t <;> simp [reflect,spin,run,step,right,left,List.append_assoc]

end LRX.Cycle11WordSymmetry

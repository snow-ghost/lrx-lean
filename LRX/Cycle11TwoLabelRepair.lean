module

public import LRX.BlockExchange

@[expose] public section

namespace LRX.Cycle11TwoLabelRepair
open LRX.BlockExchange
variable {α β : Type*}

theorem step_map (f : α → β) (op : Op) (s : List α) :
    step op (s.map f) = (step op s).map f := by
  cases op with
  | L => cases s <;> simp [step,left]
  | R => simp only [step,right,←List.map_reverse];
         have h : left (s.reverse.map f) = (left s.reverse).map f := by
           cases s.reverse <;> simp [left]
         rw [h,List.map_reverse]
  | X => cases s with
    | nil => rfl
    | cons a s => cases s <;> rfl

theorem run_map (f : α → β) (w : List Op) (s : List α) :
    run w (s.map f) = (run w s).map f := by
  induction w generalizing s with
  | nil => rfl
  | cons op w ih => simp only [run,step_map,ih]

theorem repair_head (f : α → α) (a b : α) (t : List α)
    (ha : f a=b) (hb : f b=a) (ht : t.map f=t) :
    run [.X] (a::b::t) = (a::b::t).map f := by
  simp [run,step,swap,ha,hb,ht]

#print axioms run_map
#print axioms repair_head
end LRX.Cycle11TwoLabelRepair

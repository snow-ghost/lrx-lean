import LRX.BufferMotion

/-! A concrete move-and-handoff constructor. Congruent contracted endpoints
suffice for handing the buffer to a specified named token. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ}

def transfer (d : ℤ) (j : Fin n) : List (Command n) := move d ++ [.exchange j]

theorem run_transfer (d : ℤ) (j : Fin n) (t : Logical n) :
    logicalRun (transfer d j) t =
      ⟨j, Function.update t.coord t.buffer (t.coord t.buffer+d), t.head+d⟩ := by
  rw [transfer, logicalRun_append, run_move]
  rfl

theorem transfer_valid (d : ℤ) (j : Fin n) (t : Logical n)
    (hhead : (t.coord t.buffer-t.head)%BufferMachine.slots n=0)
    (hne : j ≠ t.buffer)
    (hgoal : Int.ModEq (BufferMachine.slots n) (t.coord t.buffer+d) (t.coord j)) :
    Valid (transfer d j) t := by
  have hzero : Int.ModEq (BufferMachine.slots n) (t.coord t.buffer-t.head) 0 := by
    simpa only [Int.ModEq, Int.zero_emod] using hhead
  have hbuf : Int.ModEq (BufferMachine.slots n) (t.coord t.buffer) t.head := by
    simpa only [sub_add_cancel, zero_add] using hzero.add_right t.head
  have ht := (hgoal.symm.trans (hbuf.add_right d)).sub_right (t.head+d)
  have hc : (t.coord j-(t.head+d))%BufferMachine.slots n=0 := by
    simpa only [Int.ModEq, sub_self, Int.zero_emod] using ht
  apply (valid_append (move d) [.exchange j] t).mpr
  refine ⟨move_valid d t, ?_⟩
  rw [run_move]
  refine ⟨⟨hne, ?_⟩, True.intro⟩
  simpa only [shift, Function.update_of_ne hne] using hc

theorem transfer_rotation_price (d : ℤ) (j : Fin n) :
    rotations (compile (transfer d j)) = d.natAbs := by
  rw [transfer, compile_append, rotations_append, move_rotation_price]
  simp [compile, rotations, word]

#print axioms transfer_rotation_price
end LRX.BufferProgram

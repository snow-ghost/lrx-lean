module

public import LRX.PacketReflectionSymmetry

@[expose] public section

namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem reverse_distance (r s i : Fin n) (hi : (i-r).val ≤ (s-r).val) :
    (s-i).val=(s-r).val-(i-r).val := by
  have he : s-i=(s-r)-(i-r) := by ring
  rw [he]
  exact Fin.sub_val_of_le hi

theorem open_arc_reverse (r s i : Fin n) :
    (0 < (i-r).val ∧ (i-r).val < (s-r).val) ↔
      (0 < (s-i).val ∧ (s-i).val < (s-r).val) := by
  constructor
  · intro h
    rw [reverse_distance r s i (by omega)]
    omega
  · intro h
    have he : i-r=(s-r)-(s-i) := by ring
    rw [he,Fin.sub_val_of_le (le_of_lt h.2)]
    omega

theorem reverse_port_distance (hn : 2 ≤ n) (r s i : Fin n)
    (hi : (i-r).val < (s-r).val) :
    (s-1-i).val=(s-r).val-1-(i-r).val := by
  have he : s-1-i=(s-i)-1 := by ring
  have hd := reverse_distance r s i (le_of_lt hi)
  have hpos : 0 < (s-i).val := by omega
  have hone : (1 : Fin n).val=1 := by
    change 1%n=1
    exact Nat.mod_eq_of_lt (by omega)
  rw [he,Fin.sub_val_of_le (by omega),hone,hd]
  omega

#print axioms open_arc_reverse
#print axioms reverse_port_distance
end LRX.RotationWords

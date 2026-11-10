module

public import LRX.CoveredPacketSharpWord

@[expose] public section

namespace LRX.CycleFootprint
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem connected_load_sharp_word (hn : 4 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (initial : Active p)
    (hconn : ∀ b : Active p, LoadPath d initial.val b.val) (start finish : Fin n) :
    ∃ w : List Letter,
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      w.length ≤ n.choose 2 := by
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := FiniteWindow.majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  obtain ⟨root,hcover⟩ := connected_load_packet hd hshort initial hconn
  have hroot : d root.val ≠ 0 := by
    intro hz
    have hr := AffineLift.lift_residue hd root.val
    simp only [hz,Int.cast_zero,add_zero] at hr
    exact root.property hr.symm
  exact arbitrary_root_covered_packet_word hn hd hm root.val hroot hcover start finish

#print axioms connected_load_sharp_word
end LRX.CycleFootprint

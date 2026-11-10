import LRX.TwoArcPacketWord
import LRX.PacketCoordinateSymmetry

/-! The geometric two-arc case is independent of the chosen packet root. -/
namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem port_load_recenter (d : Fin n → ℤ) (r t : Fin n) :
    portLoad (localDisplacement d r) t=portLoad d (t+r) := by
  simp only [portLoad,localDisplacement,AffineLift.rotation_power_apply,Fin.cast_val_eq_self,add_assoc]

#print axioms port_load_recenter
end LRX.RotationWords

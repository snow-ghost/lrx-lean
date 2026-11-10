import LRX.ArcCycleSelection
import LRX.PacketIncidentSharpWord

/-! Geometric two-arc routing: positive incident packet ports on the two
arcs suffice. Service families and their total saving are constructed. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def AdmissiblePacketPort (p : State n) (d : Fin n → ℤ) (root port : Fin n) : Prop :=
  ∃ r, PrunedLift.InCore p d root r ∧ (port=r ∨ port+1=r) ∧ 0 < portLoad d port

end LRX.RotationWords

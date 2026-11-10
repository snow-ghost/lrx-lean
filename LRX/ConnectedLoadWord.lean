import LRX.LoadComponentSet
import LRX.PacketExactService
import LRX.LoadComponentSet
import LRX.ReducedRouteFrom

/-! Paid words for a single connected load support and for individual
components cut out of an arbitrary lift. -/
namespace LRX.CycleFootprint
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem packet_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (r : Fin n) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r) (start finish : Fin n) :
    ∃ w : List Letter,
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ)=(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-RotationWords.portLoad d r+
        (min (r-start).val (n-(r-start).val) : ℤ)+
        (min (finish-r).val (n-(finish-r).val) : ℤ) := by
  obtain ⟨a,ha,ht,hdisp,hprice⟩ := RotationWords.packet_exact_service hn hd hshort r hroot hcover
  obtain ⟨w,he,hlen⟩ := RotationWords.reduced_route_from hn hd [a] (by simp)
    (by simp [ht]) (by intro i; simp [hdisp]) start finish
  refine ⟨w,he,?_⟩
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
    RotationWords.walkCost,ha] at hlen
  have hz := congrArg (fun k : ℕ => (k : ℤ)) hlen
  push_cast at hz
  omega

end LRX.CycleFootprint

import LRX.InternalGapAnyOrder
import LRX.PacketIncidentSharpWord

namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The geometric internal-gap case includes adjacent packet vertices;
no order of the two cursor positions is assumed. -/
theorem packet_gap_sharp_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d)
    (r s : Fin n) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r)
    (hs : PrunedLift.InCore p d r s) (hrs : 0 < (s-r).val)
    (hgap : ∀ i, 0 < (i-r).val → (i-r).val < (s-r).val → ¬PrunedLift.InCore p d r i)
    (hvisit : (s-r).val=1 ∨ ∃ i x : Fin n, PrunedLift.InCore p d r i ∧
      0 < (x-r).val ∧ (x-r).val < (s-r).val ∧
      BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ))
    (start finish : Fin n) (hx : (start-r).val < (s-r).val)
    (hy : (finish-r).val < (s-r).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  rcases hvisit with hz | ht
  · have hstart : start=r := sub_eq_zero.mp (Fin.ext (by simpa only [Fin.val_zero] using (show (start-r).val=0 by omega)))
    have hfinish : finish=r := sub_eq_zero.mp (Fin.ext (by simpa only [Fin.val_zero] using (show (finish-r).val=0 by omega)))
    subst start
    subst finish
    exact packet_vertex_sharp_word hn hd hm r hroot hcover
  · exact internal_gap_word_any_order hn hd hm r s hroot hcover hs hrs hgap ht start finish hx hy

#print axioms packet_gap_sharp_word
end LRX.FiniteGaps

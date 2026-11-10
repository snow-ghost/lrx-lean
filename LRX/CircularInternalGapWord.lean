import LRX.PacketCoordinateSymmetry
import LRX.ConsecutivePacketGap

/-! Sharp internal-gap words at any physical root, including gaps crossing
position zero. All coordinates used to order cursors are relative to the root. -/
namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem circular_internal_gap_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d)
    (r s : Fin n) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r)
    (hs : PrunedLift.InCore p d r s) (hrs : 0 < (s-r).val)
    (hgap : ∀ i, 0 < (i-r).val → (i-r).val < (s-r).val → ¬PrunedLift.InCore p d r i)
    (hvisit : ∃ i x : Fin n, PrunedLift.InCore p d r i ∧
      0 < (x-r).val ∧ (x-r).val < (s-r).val ∧
      BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ))
    (start finish : Fin n) (hxy : (start-r).val ≤ (finish-r).val)
    (hy : (finish-r).val < (s-r).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  classical
  let q := localTarget p 0 r
  let e := localDisplacement d r
  let S := PrunedLift.core q e 0
  have hcore (i : Fin n) : PrunedLift.InCore q e 0 i ↔ PrunedLift.InCore p d r (i+r) :=
    core_recenter p d r i
  have hnext : next S 0=(s-r).val := by
    apply next_zero_of_consecutive S (s-r)
    · apply (PrunedLift.mem_core q e 0 _).mpr
      apply (hcore _).mpr
      simpa using hs
    · exact hrs
    · intro i hi hpos
      by_contra h
      have hc := (hcore i).mp ((PrunedLift.mem_core q e 0 i).mp hi)
      apply hgap (i+r) (by simpa using hpos) (by simpa using (lt_of_not_ge h)) hc
  have hlocal : AffineLift.IsLift q 0 e := recentered_lift 0 r (by simpa using hd)
  have hm' : AffineLift.Majorized e := majorized_recenter hm r
  have hr' : e 0 ≠ 0 := by simpa [e,local_displacement_zero] using hroot
  have hcover' : PrunedLift.PacketCover q e 0 := packet_cover_recenter p d r hcover
  have hinternal : Internal q e 0 := by
    obtain ⟨i,x,hi,hx0,hxs,ht⟩ := hvisit
    refine ⟨i-r,x-r,?_,?_,?_⟩
    · apply (PrunedLift.mem_core q e 0 _).mpr
      apply (hcore _).mpr
      simpa using hi
    · apply (mem_positions S 0 _).mpr
      simpa only [Fin.val_zero,hnext] using And.intro hx0 hxs
    · apply (touches_recenter d r (i-r) (x-r)).mpr
      simpa [RotationWords.rotation,AffineLift.rotation_power_apply] using ht
  have hy' : (finish-r).val ≤ size S 0 := by
    simp only [size,Fin.val_zero,Nat.sub_zero,hnext]
    omega
  obtain ⟨w,he,hlen⟩ := first_internal_gap_word hn hlocal hm' hr' hcover' hinternal
    (start-r) (finish-r) hxy hy'
  refine ⟨w,?_,hlen⟩
  exact he.trans (shifted_word_target p r start finish)

#print axioms circular_internal_gap_word
end LRX.FiniteGaps

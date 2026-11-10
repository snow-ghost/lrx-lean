import LRX.FirstExteriorGapWord
import LRX.TwoArcPacketSymmetry
import LRX.ConsecutivePacketGap

namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem circular_exterior_gap_word (hn : 7 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d)
    (r s : Fin n) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r)
    (hs : PrunedLift.InCore p d r s) (hrs : 0 < (s-r).val)
    (hgap : ∀ i, 0 < (i-r).val → (i-r).val < (s-r).val → ¬PrunedLift.InCore p d r i)
    (hload : portLoad d r=0)
    (hfixed : ∀ i, 0 < (i-r).val → (i-r).val < (s-r).val → d i=0)
    (start finish : Fin n) (hx : (start-r).val < (s-r).val) (hy : (finish-r).val < (s-r).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  classical
  let q := localTarget p 0 r
  let e := localDisplacement d r
  let S := PrunedLift.core q e 0
  have hcore (i : Fin n) : PrunedLift.InCore q e 0 i ↔ PrunedLift.InCore p d r (i+r) := core_recenter p d r i
  have hnext : next S 0=(s-r).val := by
    apply next_zero_of_consecutive S (s-r)
    · apply (PrunedLift.mem_core q e 0 _).mpr
      apply (hcore _).mpr
      simpa using hs
    · exact hrs
    · intro i hi hpos
      by_contra h
      have hc := (hcore i).mp ((PrunedLift.mem_core q e 0 i).mp hi)
      exact hgap (i+r) (by simpa using hpos) (by simpa using (lt_of_not_ge h)) hc
  have hlocal : AffineLift.IsLift q 0 e := recentered_lift 0 r (by simpa using hd)
  have hm' : AffineLift.Majorized e := majorized_recenter hm r
  have hr' : e 0 ≠ 0 := by simpa [e,local_displacement_zero] using hroot
  have hc' : PrunedLift.PacketCover q e 0 := packet_cover_recenter p d r hcover
  have hl' : portLoad e 0=0 := by simpa only [e,port_load_recenter,zero_add] using hload
  have hf' : ∀ i ∈ positions S 0, e i=0 := by
    intro i hi
    obtain ⟨hi0,his⟩ := (mem_positions S 0 i).mp hi
    have hz := hfixed (i+r) (by simpa using hi0) (by simpa only [add_sub_cancel_right,← hnext] using his)
    simpa only [e,localDisplacement,AffineLift.rotation_power_apply,Fin.cast_val_eq_self] using hz
  have hx' : (start-r).val ≤ size S 0 := by simp only [size,Fin.val_zero,Nat.sub_zero,hnext]; omega
  have hy' : (finish-r).val ≤ size S 0 := by simp only [size,Fin.val_zero,Nat.sub_zero,hnext]; omega
  obtain ⟨w,he,hlen⟩ := first_exterior_gap_word hn hlocal hm' hr' hc' hl' hf' (start-r) (finish-r) hx' hy'
  exact ⟨w,he.trans (shifted_word_target p r start finish),hlen⟩

#print axioms circular_exterior_gap_word
end LRX.FiniteGaps

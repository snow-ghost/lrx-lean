import LRX.CircularInternalGapWord
import LRX.CircularArcCoordinates

/-! Both cursor orders in an internal packet gap have the sharp word bound.
Reflection reverses the order and preserves every letter count. -/
namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords WordReflection
variable {n : ℕ} [NeZero n]

theorem internal_gap_word_any_order (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d)
    (r s : Fin n) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r)
    (hs : PrunedLift.InCore p d r s) (hrs : 0 < (s-r).val)
    (hgap : ∀ i, 0 < (i-r).val → (i-r).val < (s-r).val → ¬PrunedLift.InCore p d r i)
    (hvisit : ∃ i x : Fin n, PrunedLift.InCore p d r i ∧
      0 < (x-r).val ∧ (x-r).val < (s-r).val ∧
      BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ))
    (start finish : Fin n) (hx : (start-r).val < (s-r).val)
    (hy : (finish-r).val < (s-r).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  by_cases hxy : (start-r).val ≤ (finish-r).val
  · exact circular_internal_gap_word hn hd hm r s hroot hcover hs hrs hgap hvisit start finish hxy hy
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := FiniteWindow.majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  have hds := PrunedLift.nonzero_reachable hd hshort r s hroot hs.1
  have hcoverS := PrunedLift.packet_cover_reroot p d r s hcover hs.1 hs.2
  have hd' : AffineLift.IsLift (reflectedTarget p) 0 (reflectedDisplacement d) := by
    simpa using reflected_lift 0 (show AffineLift.IsLift p ((0 : Fin n) : ℤ) d by simpa using hd)
  have hm' := majorized_reflected hd.1 hm
  have hr' : reflectedDisplacement d (reflection s) ≠ 0 := by
    simpa [reflectedDisplacement] using hds
  have hcover' := packet_cover_reflected p d s hcoverS
  have hboundary : PrunedLift.InCore (reflectedTarget p) (reflectedDisplacement d)
      (reflection s) (reflection r) := (core_reflected p d s r).mpr ⟨hs.2,hs.1⟩
  have hdifference (a b : Fin n) : reflection a-reflection b=b-a := by
    simp only [reflection_apply]
    ring
  have hpos' : 0 < (reflection r-reflection s).val := by rwa [hdifference]
  have hgap' : ∀ i, 0 < (i-reflection s).val →
      (i-reflection s).val < (reflection r-reflection s).val →
      ¬PrunedLift.InCore (reflectedTarget p) (reflectedDisplacement d) (reflection s) i := by
    intro i hi0 his hc
    have hother : s-reflection i=i-reflection s := by simp only [reflection_apply]; ring
    have hin := (open_arc_reverse r s (reflection i)).mpr
      ⟨by rwa [hother],by rwa [hother,← hdifference r s]⟩
    have hc' := (core_reflected p d s (reflection i)).mp (by simpa using hc)
    exact hgap (reflection i) hin.1 hin.2 ((PrunedLift.in_core_reroot hs).mp hc')
  have hvisit' : ∃ i x : Fin n,
      PrunedLift.InCore (reflectedTarget p) (reflectedDisplacement d) (reflection s) i ∧
      0 < (x-reflection s).val ∧ (x-reflection s).val < (reflection r-reflection s).val ∧
      BufferProgram.Touches (n : ℤ) (i : ℤ) (reflectedDisplacement d i) (x : ℤ) := by
    obtain ⟨i,x,hi,hx0,hxs,ht⟩ := hvisit
    have hx' := (open_arc_reverse r s x).mp ⟨hx0,hxs⟩
    exact ⟨reflection i,reflection x,
      (core_reflected p d s i).mpr ((PrunedLift.in_core_reroot hs).mpr hi),
      by simpa only [hdifference] using hx'.1,
      by simpa only [hdifference] using hx'.2,(touches_reflected d i x).mpr ht⟩
  have hport (i : Fin n) (hi : (i-r).val < (s-r).val) :
      (-i-reflection s).val=(s-r).val-1-(i-r).val := by
    have he : -i-reflection s=s-1-i := by simp only [reflection_apply]; ring
    rw [he]
    exact reverse_port_distance hn r s i hi
  have hxy' : (-start-reflection s).val ≤ (-finish-reflection s).val := by
    rw [hport start hx,hport finish hy]
    omega
  have hy' : (-finish-reflection s).val < (reflection r-reflection s).val := by
    rw [hport finish hy,hdifference]
    omega
  obtain ⟨w,he,hlen⟩ := circular_internal_gap_word hn hd' hm' (reflection s) (reflection r)
    hr' hcover' hboundary hpos' hgap' hvisit' (-start) (-finish) hxy' hy'
  refine ⟨mirror w,?_,by simpa only [mirror_length] using hlen⟩
  rw [mirror_eval,he]
  exact mirror_word_target p start finish

#print axioms internal_gap_word_any_order
end LRX.FiniteGaps

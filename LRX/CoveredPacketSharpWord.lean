import LRX.PartitionExteriorGapWord
import LRX.PacketExteriorReduction
import LRX.Small
import LRX.WordMetric

/-! Sharp words for every cursor pair under the explicit packet cover hypothesis.
The hypothesis is retained: this does not yet prove NonzeroLiftRouting. -/
namespace LRX
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem covered_packet_sharp_word_large (hn : 7 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  rcases FiniteGaps.sharp_word_or_exterior_gap (by omega) hd hm hroot hcover start finish with h | h
  · exact h
  · obtain ⟨a,ha,_,_,hload,hfixed,hx,hy⟩ := h
    exact FiniteGaps.partition_exterior_gap_word hn hd hm hroot hcover a ha hload hfixed start finish hx hy

theorem covered_packet_sharp_word (hn : 4 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  by_cases hlarge : 7 ≤ n
  · exact covered_packet_sharp_word_large hlarge hd hm hroot hcover start finish
  · exact ediam_le_iff_words.mp (sharp_ediam_small n hn (by omega)) _

theorem arbitrary_root_covered_packet_word (hn : 4 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (root : Fin n) (hroot : d root ≠ 0)
    (hcover : PrunedLift.PacketCover p d root) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  have hd' := recentered_lift 0 root (show AffineLift.IsLift p ((0 : Fin n) : ℤ) d by simpa using hd)
  have hm' := majorized_recenter hm root
  have hr' : localDisplacement d root 0 ≠ 0 := by simpa only [local_displacement_zero] using hroot
  have hc' := packet_cover_recenter p d root hcover
  obtain ⟨w,he,hlen⟩ := covered_packet_sharp_word hn hd' hm' hr' hc' (start-root) (finish-root)
  exact ⟨w,he.trans (shifted_word_target p root start finish),hlen⟩

#print axioms covered_packet_sharp_word_large
#print axioms covered_packet_sharp_word
#print axioms arbitrary_root_covered_packet_word
end LRX

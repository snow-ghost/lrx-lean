import LRX.PacketGapSharpWord
import LRX.PartitionCircularCoordinates

/-! Every internal member of the actual packet partition admits a sharp
word for either cursor order, including its last gap and empty members. -/
namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem partition_gap_sharp_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (a : Fin n) (ha : a ∈ PrunedLift.core p d 0)
    (hvisit : size (PrunedLift.core p d 0) a=0 ∨ Internal p d a)
    (start finish : Fin n)
    (hx : a.val ≤ start.val ∧ start.val < next (PrunedLift.core p d 0) a)
    (hy : a.val ≤ finish.val ∧ finish.val < next (PrunedLift.core p d 0) a) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  classical
  let S := PrunedLift.core p d 0
  let s : Fin n := (next S a : Fin n)
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := FiniteWindow.majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  have hca : PrunedLift.InCore p d 0 a := (PrunedLift.mem_core p d 0 a).mp ha
  have hda := PrunedLift.nonzero_reachable hd hshort 0 a hroot hca.1
  have hcoverA := PrunedLift.packet_cover_reroot p d 0 a hcover hca.1 hca.2
  have hat := lt_next S a
  have htn := next_le S a
  have hlength : (s-a).val=next S a-a.val :=
    cut_interval_endpoint a (next S a) (le_of_lt hat) (next_circular_width hd hshort hroot a)
  have hs : PrunedLift.InCore p d a s := (PrunedLift.in_core_reroot hca).mpr
    ((PrunedLift.mem_core p d 0 s).mp (next_circular_mem S (core_zero p d) a))
  have hpos : 0 < (s-a).val := by rw [hlength]; omega
  have hinside (i : Fin n) : (0 < (i-a).val ∧ (i-a).val < (s-a).val) ↔ i ∈ positions S a := by
    rw [hlength,cut_interval_open a i (next S a) hat htn,mem_positions]
  have hgap : ∀ i, 0 < (i-a).val → (i-a).val < (s-a).val → ¬PrunedLift.InCore p d a i := by
    intro i hi0 his hc
    have hi := (hinside i).mp ⟨hi0,his⟩
    exact gap_avoids_marks S a i hi ((PrunedLift.mem_core p d 0 i).mpr
      ((PrunedLift.in_core_reroot hca).mp hc))
  have hvisit' : (s-a).val=1 ∨ ∃ i x : Fin n, PrunedLift.InCore p d a i ∧
      0 < (x-a).val ∧ (x-a).val < (s-a).val ∧
      BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ) := by
    rcases hvisit with hz | ⟨i,x,hi,hx,ht⟩
    · left
      change next S a-a.val-1=0 at hz
      rw [hlength]
      omega
    · have hxi := (hinside x).mpr hx
      exact Or.inr ⟨i,x,(PrunedLift.in_core_reroot hca).mpr
        ((PrunedLift.mem_core p d 0 i).mp hi),hxi.1,hxi.2,ht⟩
  apply packet_gap_sharp_word hn hd hm a s hda hcoverA hs hpos hgap hvisit' start finish
  · rw [hlength]
    exact (cut_interval_membership a start (next S a) hat htn).mpr hx
  · rw [hlength]
    exact (cut_interval_membership a finish (next S a) hat htn).mpr hy

#print axioms partition_gap_sharp_word
end LRX.FiniteGaps

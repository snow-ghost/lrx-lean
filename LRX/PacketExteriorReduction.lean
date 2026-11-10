import LRX.PacketCursorDichotomy
import LRX.PositiveGapBoundary

/-! All cursor pairs for a covered packet are reduced to an explicitly
zero-load, fixed interior gap, or already admit a sharp literal word. -/
namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem sharp_word_or_exterior_gap (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    ∃ a ∈ PrunedLift.core p d 0,
      0 < size (PrunedLift.core p d 0) a ∧ ¬Internal p d a ∧ portLoad d a=0 ∧
      (∀ i ∈ positions (PrunedLift.core p d 0) a, d i=0) ∧
      (a.val ≤ start.val ∧ start.val < next (PrunedLift.core p d 0) a) ∧
      (a.val ≤ finish.val ∧ finish.val < next (PrunedLift.core p d 0) a) := by
  classical
  rcases cursor_dichotomy (PrunedLift.core p d 0) (core_zero p d) start finish with hboth | hgap
  · left
    apply two_arc_core_word hn hd hm hroot hcover start finish
    intro dir
    obtain ⟨r,hr,hpos⟩ := hboth dir
    exact ⟨r,(PrunedLift.mem_core p d 0 r).mp hr,hpos⟩
  · obtain ⟨a,ha,hx,hy⟩ := hgap
    by_cases hvisit : size (PrunedLift.core p d 0) a=0 ∨ Internal p d a
    · exact Or.inl (partition_gap_sharp_word hn hd hm hroot hcover a ha hvisit start finish hx hy)
    · have hsize : 0 < size (PrunedLift.core p d 0) a := by omega
      have hnot : ¬Internal p d a := fun h => hvisit (Or.inr h)
      have hload : portLoad d a=0 := by
        have hnonneg := port_load_nonneg d a
        by_contra h
        exact hvisit (positive_boundary_internal hd hm hroot hcover a ha (by omega))
      have hshort : |d 0| < (n : ℤ) := by
        have := FiniteWindow.majorized_short hd hm 0
        have := abs_nonneg (d 0)
        omega
      have hmov : p⁻¹ 0 ≠ 0 := fun h => hroot (BufferProgram.fixed_short_displacement hd 0 hshort h)
      refine Or.inr ⟨a,ha,hsize,hnot,hload,?_,hx,hy⟩
      intro i hi
      by_contra hdi
      exact hnot (nonzero_gap_internal hd hcover hmov a ha i hi hdi)

#print axioms sharp_word_or_exterior_gap
end LRX.FiniteGaps

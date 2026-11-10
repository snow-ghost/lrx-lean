import LRX.SignedSelectionDeficit
import LRX.ActualOddShellPayment
import LRX.EvenShellExceptEightNine
import LRX.PacketCoordinateSymmetry

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The zero-energy part of the remaining peak contract for every core parity, with
no extra word length for normalization and no supplied price premise. -/
theorem original_zero_energy_shell_sharp_word_except_eight_nine (hn : 4 ≤ n) (h8 : n ≠ 8) (h9 : n ≠ 9) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hU : sourceHalfPeak p=2)
    (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  let q := localTarget p 0 (componentLeft p root)
  have hzero : (componentSet q 0).card=(componentSet p root).card := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have heq : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← heq] at hh
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hroots : (componentRoots q).card=(componentRoots p).card := by
    rw [component_roots_card_eq_blocks,component_roots_card_eq_blocks]
    exact component_cut_nontrivial_count p root
  have hz := (two_component_zero_energy_unpaid_rigidity (by omega) p hmaj hmax hc root hlarge hpos he).1
  have hzq : cycleDefect q=0 := by
    dsimp only [q]
    rw [component_cut_cycle_defect]
    exact hz
  have hUq : sourceHalfPeak q=2 := by
    dsimp only [q]
    rw [component_cut_source_half_peak,hU]
  have hword : ∃ w : List Letter,
      eval w=(rotation (start-componentLeft p root))⁻¹*q*rotation (finish-componentLeft p root) ∧
      w.length ≤ n.choose 2 := by
    by_cases heven : (prefixSourceCore q).card%2=0
    · exact shell_sharp_word_of_nonpos q hqm (by omega) (by omega) hzq
        (prefix_even_shell_paid_except_eight_nine q hqm (by omega) (by omega) hzq heven hUq h8 h9) _ _
    · exact prefix_odd_shell_sharp_word q hqm (by omega) (by omega)
        hzq (by omega) (by omega) _ _
  obtain ⟨w,hw,hlen⟩ := hword
  refine ⟨w,?_,hlen⟩
  rw [hw]
  exact shifted_word_target p (componentLeft p root) start finish

#print axioms original_zero_energy_shell_sharp_word_except_eight_nine
end LRX.FiniteCuts

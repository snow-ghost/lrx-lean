import LRX.NinePeakReduction
import LRX.NineShellActualWord

namespace LRX
open FiniteCuts RotationWords

theorem nine_zero_energy_peak_routing : NineZeroEnergyPeakRouting := by
  intro p hmaj hmax hc root hlarge start finish hne hboth hpos hU he hf
  let r := componentLeft p root
  let q := localTarget p 0 r
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
  have hz := (two_component_zero_energy_unpaid_rigidity (by decide) p hmaj hmax hc root hlarge hpos he).1
  have hzq : cycleDefect q=0 := by
    dsimp only [q,r]
    rw [component_cut_cycle_defect,hz]
  have hUq : sourceHalfPeak q=2 := by
    dsimp only [q,r]
    rw [component_cut_source_half_peak,hU]
  have heq : canonicalEnergyDeficit q=0 := by
    dsimp only [q,r]
    unfold canonicalEnergyDeficit
    rw [component_cut_displacement_mass]
    exact he
  have hs : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using
      (Equiv.Perm.card_support_conj (σ := (rotation r)⁻¹) (τ := p))
  have hfq : 9-q.support.card=1 := by omega
  have hword : ∃ w : List Letter,
      eval w=(rotation (start-r))⁻¹*q*rotation (finish-r) ∧ w.length ≤ Nat.choose 9 2 := by
    rcases prefix_nine_sharp_or_shell_shape q hqm (by omega) (by omega) hzq hUq (start-r) (finish-r) with hw | hshape
    · exact hw
    · exact prefix_nine_shell_actual_word q hqm (by omega) hzq heq hfq
        hshape.1 hshape.2.1 hshape.2.2 (start-r) (finish-r)
  obtain ⟨w,hw,hlen⟩ := hword
  refine ⟨w,?_,hlen⟩
  rw [hw]
  exact shifted_word_target p r start finish

#print axioms nine_zero_energy_peak_routing
end LRX

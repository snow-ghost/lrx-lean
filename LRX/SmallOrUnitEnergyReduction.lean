module

public import LRX.UnitEnergyBridgeOnePayment
public import LRX.UnitEnergyExactComponentDefects
public import LRX.UnitEnergySourceEquality
public import LRX.PacketComponentDefectBound
public import LRX.SourcePacketCyclePartition
public import LRX.PrefixSaturatedDefectNoFillings
public import LRX.Small
public import LRX.PackedSmall8
public import LRX.FinalPeakTwoReduction
public import LRX.OriginalZeroEnergyExceptEightNine

@[expose] public section

namespace LRX
open FiniteCuts RotationWords

/-- Remaining contract after paying zero energy at every size except eight and nine. -/
def SmallOrUnitEnergyPeakRouting : Prop :=
  ∀ (n : ℕ) [NeZero n], 9 ≤ n → ∀ (p : State n),
    AffineLift.Majorized (displacement p.symm) → MaximalZeroCut p →
    ∀ (hc : (componentRoots p).card=1+1) (root : Fin n),
    (n+1)/2 < (componentSet p root).card → ∀ start finish : Fin n,
    start ≠ finish → JoinedPositiveArcs p hc start finish → 1 ≤ peakExcess p hc →
    sourceHalfPeak p=2 →
    ((canonicalEnergyDeficit p=0 ∧ n-p.support.card=n%2 ∧ n ≤ 9) ∨
      (canonicalEnergyDeficit p=1 ∧ n%4=2 ∧ n-p.support.card=2 ∧
        bridgeBudget (componentBridges p hc)=2 ∧ cycleDefect p=4 ∧ peakExcess p hc=1 ∧
        isolatedVertices p=p.supportᶜ ∧ ExactDefectTwoComponentWindows p ∧
        (fillingHalfPeakSum p=((fillingCycles p).card : ℤ) ∧
          p.cycleFactorsFinset.card=(fillingCycles p).card+4 ∧
          (∀ c ∈ fillingCycles p, leftPeak c n=1)) ∧
        (∀ r ∈ componentRoots p, (canonicalRootPacket p r).cycleFactorsFinset.card=2) ∧
        (∀ r ∈ componentRoots p, cycleDefect (canonicalRootPacket p r)=2) ∧
        (2 ≤ (componentSet p 0).card → ∀ i ∈ componentSet p 0, i ∈ sourcePackets p))) →
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2

theorem peak_two_routing_of_small_or_unit_energy (pay : SmallOrUnitEnergyPeakRouting) :
    TwoComponentPeakTwoSharpRouting := by
  intro n inst hn p hmaj hmax hc root hlarge start finish hne hboth hpos hU hcases
  by_cases hsmall : n ≤ 6
  · have hwords : SharpWordBound n := by
      interval_cases n
      · exact Small4.sharp_words
      · exact Small5.sharp_words
      · exact Small6.sharp_words
    exact hwords ((rotation start)⁻¹*p*rotation finish)
  have hn7 : 7 ≤ n := by omega
  by_cases hn8eq : n=8
  · subst n
    exact PackedSmall8.sharp_words ((rotation start)⁻¹*p*rotation finish)
  rcases hcases with ⟨he,hf⟩ | hunit
  · by_cases hsmall : n=8 ∨ n=9
    · exact pay n (by omega) p hmaj hmax hc root hlarge start finish hne hboth hpos hU
        (Or.inl ⟨he,hf,by omega⟩)
    · exact original_zero_energy_shell_sharp_word_except_eight_nine hn (by omega) (by omega)
        p hmaj hmax hc root hlarge hpos he hU start finish
  · have hn9 : 9 ≤ n := by have := hunit.2.1; omega
    rcases unit_energy_peak_two_sharp_or_defect_four (by have := hunit.2.1; omega)
      p hmaj hmax hc root hlarge hpos hunit.2.2 hunit.1 hU start finish with hw | hr
    · exact hw
    · have hgeom := unit_energy_defect_four_component_windows p hmaj hc hunit.2.2 hunit.1 hr.2.1 hr.2.2.2
      have hS := unit_energy_defect_four_source_equality hn p hmaj hc hpos hunit.2.2 hunit.1 hU hr.1 hr.2.1
      have hPackets := source_packet_cycles_exact_two_of_four hn p hmaj hc hgeom hS.2.1
      have hPacketDefects := exact_defect_two_windows_packet_defect_eq_two p hmaj hgeom hPackets
      have hPrefix : 2 ≤ (componentSet p 0).card → ∀ i ∈ componentSet p 0, i ∈ sourcePackets p := by
        intro hc0
        exact unit_energy_prefix_sources_cover p hmaj hc hc0 hunit.2.2 hunit.1 hr.2.2.2 hgeom hPacketDefects
      exact pay n hn9 p hmaj hmax hc root hlarge start finish hne hboth hpos hU
        (Or.inr ⟨hunit.1,hunit.2.1,hunit.2.2,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,hgeom,hS,hPackets,hPacketDefects,hPrefix⟩)

theorem nonzero_routing_of_small_or_unit_energy (pay : SmallOrUnitEnergyPeakRouting) :
    NonzeroLiftRouting :=
  nonzero_routing_of_peak_two (peak_two_routing_of_small_or_unit_energy pay)

#print axioms peak_two_routing_of_small_or_unit_energy
#print axioms nonzero_routing_of_small_or_unit_energy
end LRX

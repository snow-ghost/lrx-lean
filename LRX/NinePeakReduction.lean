module

public import LRX.SmallOrUnitEnergyReduction
public import LRX.UnitEnergyMassExclusion

@[expose] public section

namespace LRX
open FiniteCuts RotationWords

/-- The single finite routing obligation remaining after all infinite
branches, every other size and the complete unit-energy case. -/
def NineZeroEnergyPeakRouting : Prop :=
  ∀ (p : State 9), AffineLift.Majorized (displacement p.symm) → MaximalZeroCut p →
    ∀ (hc : (componentRoots p).card=1+1) (root : Fin 9),
    (9+1)/2 < (componentSet p root).card → ∀ start finish : Fin 9,
    start ≠ finish → JoinedPositiveArcs p hc start finish → 1 ≤ peakExcess p hc →
    sourceHalfPeak p=2 → canonicalEnergyDeficit p=0 → 9-p.support.card=1 →
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ Nat.choose 9 2

theorem small_or_unit_energy_routing_of_nine (pay : NineZeroEnergyPeakRouting) :
    SmallOrUnitEnergyPeakRouting := by
  intro n inst hn p hmaj hmax hc root hlarge start finish hne hboth hpos hU hcases
  rcases hcases with ⟨he,hf,hsmall⟩ | hunit
  · have hn9 : n=9 := by omega
    subst n
    exact pay p hmaj hmax hc root hlarge start finish hne hboth hpos hU he (by simpa using hf)
  · obtain ⟨he,hmod,hf,hB,hZ,hEx,hfixed,hgeom,hS,hPackets,hPacketDefects,hPrefix⟩ := hunit
    exact False.elim (unit_energy_defect_four_peak_two_impossible (by omega) p hmaj hc hf he hZ hfixed hU hS.2.1)

theorem nonzero_routing_of_nine (pay : NineZeroEnergyPeakRouting) : NonzeroLiftRouting :=
  nonzero_routing_of_small_or_unit_energy (small_or_unit_energy_routing_of_nine pay)

#print axioms small_or_unit_energy_routing_of_nine
#print axioms nonzero_routing_of_nine
end LRX

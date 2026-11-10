import LRX.UnitEnergyExactComponentDefects
import LRX.PeakFourSourceRigidity

namespace LRX.FiniteCuts
open ZeroGap RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Saturation in the remaining unit-energy case leaves exactly four
cycles outside the filling family, whose individual peaks are all one. -/
theorem unit_energy_defect_four_source_equality (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (hpos : 1 ≤ peakExcess p hc)
    (hf : n-p.support.card=2) (he : canonicalEnergyDeficit p=1)
    (hU : sourceHalfPeak p=2) (hB : bridgeBudget (componentBridges p hc)=2)
    (hZ : cycleDefect p=4) :
    fillingHalfPeakSum p=((fillingCycles p).card : ℤ) ∧
      p.cycleFactorsFinset.card=(fillingCycles p).card+4 ∧
      (∀ c ∈ fillingCycles p, leftPeak c n=1) := by
  let C := (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
    (p.support.card : ℤ)+fillingHalfPeakSum p
  have hN := choose_two_half_identity n
  have hn4 := unit_energy_reserve_size_mod_four p he
  have hsize : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by omega
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  have hfixed : (p.support.card : ℤ)=(n : ℤ)-2 := by omega
  have hprice : peakExcess p hc=1-C := by
    unfold peakExcess
    rw [hU,hB]
    dsimp only [C,canonicalEnergyDeficit] at *
    norm_num only [Nat.cast_ofNat]
    nlinarith only [he,hN,hsize,hfixed]
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  obtain ⟨events,hprod,hlen,_,_,hsep,_,htravel⟩ := sorting_events hd (FiniteWindow.majorized_short hd hmaj)
  have hcover := source_packet_strong_event_cover (by omega) p (by omega) events hprod hsep htravel
  have hF : (fun i : Fin n => (i : ℤ)+displacement p.symm i)=(fun i => (p.symm i : ℤ)) := by
    funext i
    simp [displacement]
  have hI : inversionNumber p.symm=inversionNumber p := inversion_number_inverse p
  rw [hF,canonical_inversion_count,hI] at hlen
  have hS := filling_half_peak_sum_ge_count p
  have hZform : C=cycleDefect p-(p.cycleFactorsFinset.card : ℤ)+fillingHalfPeakSum p := by
    simp only [C,cycleDefect,displacement_mass_inverse]
    ring
  rw [hc] at hcover
  have hEq : fillingHalfPeakSum p=((fillingCycles p).card : ℤ) := by omega
  exact ⟨hEq,by omega,filling_cycles_peak_one_of_equality p hEq⟩

#print axioms unit_energy_defect_four_source_equality
end LRX.FiniteCuts

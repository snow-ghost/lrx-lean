module

public import LRX.TwoComponentPeakTwo

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The remaining zero-energy peak forces equality in both event-cover
bounds: the whole original permutation has zero cycle defect. -/
theorem two_component_zero_energy_unpaid_rigidity (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=0) :
    cycleDefect p=0 ∧ bridgeBudget (componentBridges p hc)=1 ∧ peakExcess p hc=1 ∧
      (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
        (p.support.card : ℤ)+fillingHalfPeakSum p= -2 := by
  obtain ⟨hU,hf⟩ := two_component_zero_energy_unpaid_parameters hn p hmaj hmax hc root hlarge hpos he
  let C := (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
    (p.support.card : ℤ)+fillingHalfPeakSum p
  have hweak := aggregate_source_filling_defect (by omega) p hmaj (by omega)
  have hstrong := aggregate_source_filling_strong_defect (by omega) p hmaj (by omega)
  dsimp only at hstrong
  rw [hc] at hweak hstrong
  norm_num only [Nat.cast_add,Nat.cast_one] at hweak hstrong
  have hw : -2 ≤ C := hweak
  have hs : cycleDefect p-4 ≤ 2*C := by
    simpa only [cycleDefect,displacement_mass_inverse,C] using hstrong
  have hnon : 0 ≤ cycleDefect p := by
    have hh := finite_depth_rank p
    unfold cycleDefect
    omega
  have hact := unpaid_two_component_activity (by omega) p hmaj hmax hc hpos
  dsimp only at hact
  rw [hf] at hact
  have hB : bridgeBudget (componentBridges p hc) ≤ 1 := by
    have hp : n%2 ≤ 1 := by omega
    omega
  have hN := choose_two_half_identity n
  have hsize : (n : ℤ)=2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ) := by omega
  have hsupport : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  have hfixed : (p.support.card : ℤ)=(n : ℤ)-(n%2 : ℕ) := by omega
  have hprice : peakExcess p hc=2*(bridgeBudget (componentBridges p hc) : ℤ)-3-C := by
    unfold peakExcess
    rw [hU]
    dsimp only [C]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [he,hN,hsize,hfixed]
  have hC : C= -2 := by omega
  exact ⟨by omega,by omega,by omega,hC⟩

#print axioms two_component_zero_energy_unpaid_rigidity
end LRX.FiniteCuts

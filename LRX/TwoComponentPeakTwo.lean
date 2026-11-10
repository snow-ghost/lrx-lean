module

public import LRX.TwoComponentDefectSum
public import LRX.StrongPacketEventBudget

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- High source peaks in the remaining unit-energy layer are paid by the
strong event cover and the actual defect of both load components. -/
theorem two_component_unit_energy_high_peak_paid (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (hf : n-p.support.card=2)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=1)
    (hU : 3 ≤ sourceHalfPeak p) : peakExcess p hc ≤ 0 := by
  by_contra hnot
  have hpos : 1 ≤ peakExcess p hc := by omega
  have hZ := two_component_unit_energy_high_peak_defect_four hn p hmaj hmax hc hpos hf he hU
  have hZ' : 4 ≤ (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
      (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ) := by
    simpa only [cycleDefect,displacement_mass_inverse] using hZ
  have hstrong := aggregate_source_filling_strong_defect hn p hmaj (by omega)
  dsimp only at hstrong
  rw [hc] at hstrong
  norm_num only [Nat.cast_add,Nat.cast_one] at hstrong
  have hcredit : 0 ≤ (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
      (p.support.card : ℤ)+fillingHalfPeakSum p := by linarith only [hZ',hstrong]
  have hact := unpaid_two_component_activity hn p hmaj hmax hc hpos
  dsimp only at hact
  have hB : 2*(bridgeBudget (componentBridges p hc) : ℤ) ≤ 4 := by
    rw [hf] at hact
    omega
  have hn4 := unit_energy_reserve_size_mod_four p he
  have hsize : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by omega
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  have hf' : (p.support.card : ℤ)=(n : ℤ)-2 := by omega
  have hU' : (3 : ℤ) ≤ sourceHalfPeak p := by exact_mod_cast hU
  have hN := choose_two_half_identity n
  unfold peakExcess at hpos
  nlinarith only [hpos,hcredit,hB,hsize,hf',hU',hN,he]

/-- Every remaining unpaid two-component peak has source peak exactly two.
The two energy regimes still require payment. -/
theorem two_component_sharp_or_peak_two (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (start ≠ finish ∧ JoinedPositiveArcs p hc start finish ∧ 1 ≤ peakExcess p hc ∧
      sourceHalfPeak p=2 ∧
      ((eps=0 ∧ n-p.support.card=n%2) ∨ (eps=1 ∧ n%4=2 ∧ n-p.support.card=2))) := by
  dsimp only
  rcases two_component_sharp_or_nonunit_low_energy hn p hmaj hmax hc root hlarge start finish with hw | hp
  · exact Or.inl hw
  · obtain ⟨hne,hboth,hpos,hcases⟩ := hp
    rcases hcases with ⟨he,hU,hf⟩ | ⟨he,hn4,hf,hUlo,hUhi⟩
    · exact Or.inr ⟨hne,hboth,hpos,hU,Or.inl ⟨he,hf⟩⟩
    · have hU : sourceHalfPeak p=2 := by
        by_contra hh
        have hpaid := two_component_unit_energy_high_peak_paid (by omega) p hmaj hmax hc hf he (by omega)
        omega
      exact Or.inr ⟨hne,hboth,hpos,hU,Or.inr ⟨he,hn4,hf⟩⟩

#print axioms two_component_unit_energy_high_peak_paid
#print axioms two_component_sharp_or_peak_two
end LRX.FiniteCuts

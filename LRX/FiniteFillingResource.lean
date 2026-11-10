module

public import LRX.FiniteFillingEnergyBounds
public import LRX.TwoWindowCycleDefect
public import LRX.GapCostInversionDeficit

@[expose] public section

/-! M4: resource inequalities for actual finite filling permutations.
All peaks, ranks and defects are calculated from the permutation. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

noncomputable def cyclePeakSum (p : State b) : ℕ :=
  ∑ q ∈ p.cycleFactorsFinset, leftPeak q b

noncomputable def fillingResource (p : State b) : ℤ :=
  (b.choose 2 : ℤ)-(inversionNumber p : ℤ)+(cyclePeakSum p : ℤ)

theorem twice_cycle_peak_sum_le_support (p : State b) :
    2*cyclePeakSum p ≤ p.support.card := by
  classical
  unfold cyclePeakSum
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ q ∈ p.cycleFactorsFinset, q.support.card :=
      Finset.sum_le_sum (fun q _ => twice_left_peak_le_support q b)
    _ = _ := cycle_support_card_sum p

theorem peak_le_cycle_peak_sum (p : State b) : leftPeak p b ≤ cyclePeakSum p := by
  classical
  apply Finset.sup_le
  intro e he
  rw [half_load_cycle_sum]
  apply Finset.sum_le_sum
  intro q _
  exact Finset.le_sup he

theorem finite_energy_cycle_peak_sum (p : State b) :
    (∑ i, |displacement p i|) ≤ 2*(cyclePeakSum p : ℤ)*((b : ℤ)-cyclePeakSum p) := by
  have hs := twice_cycle_peak_sum_le_support p
  have hc : p.support.card ≤ b := by simpa using Finset.card_le_univ p.support
  exact finite_energy_peak_upper p _ (peak_le_cycle_peak_sum p) (by omega)

/-- Twice the resource bounds rank, defect and the exact quadratic slack z=b-2S. -/
theorem filling_resource_defect_bound (p : State b) :
    let z : ℤ := (b : ℤ)-2*(cyclePeakSum p : ℤ)
    2*((p.support.card : ℤ)-(p.cycleFactorsFinset.card : ℤ)+cycleDefect p)+z*(z-1) ≤
      2*fillingResource p := by
  have he := finite_energy_cycle_peak_sum p
  have hc := twice_choose_two_int b
  dsimp only
  unfold fillingResource cycleDefect
  nlinarith

/-- The resource already pays half the width, including empty and singleton fillings. -/
theorem filling_resource_half_width (p : State b) : ((b/2 : ℕ) : ℤ) ≤ fillingResource p := by
  have hh := filling_resource_defect_bound p
  have hs := twice_cycle_peak_sum_le_support p
  have hk := twice_cycle_count_le_support p
  have hz := finite_depth_rank p
  have hZ : 0 ≤ cycleDefect p := by unfold cycleDefect; omega
  have hr : (cyclePeakSum p : ℤ) ≤ (p.support.card : ℤ)-(p.cycleFactorsFinset.card : ℤ) := by omega
  dsimp only at hh
  have hb : (b : ℤ)-1 ≤ 2*fillingResource p := by
    nlinarith [sq_nonneg ((b : ℤ)-2*(cyclePeakSum p : ℤ)-1)]
  omega

/-- Fixed-position and cycle-defect corrections to the filling width. -/
theorem filling_resource_width_defect (p : State b) :
    (b : ℤ) ≤ 2*fillingResource p+((b-p.support.card : ℕ) : ℤ)-2*cycleDefect p := by
  have hh := filling_resource_defect_bound p
  have hs := twice_cycle_peak_sum_le_support p
  have hk := twice_cycle_count_le_support p
  have hc : p.support.card ≤ b := by simpa using Finset.card_le_univ p.support
  let z : ℤ := (b : ℤ)-2*(cyclePeakSum p : ℤ)
  have hz : 0 ≤ z := by dsimp only [z]; omega
  have hzprod : 0 ≤ z*(z-1) := by
    by_cases hzero : z=0
    · rw [hzero]; norm_num
    · exact mul_nonneg hz (by omega)
  change 2*((p.support.card : ℤ)-(p.cycleFactorsFinset.card : ℤ)+cycleDefect p)+z*(z-1) ≤
    2*fillingResource p at hh
  have hf : ((b-p.support.card : ℕ) : ℤ)=(b : ℤ)-(p.support.card : ℤ) := by omega
  rw [hf]
  omega

/-- The actual filling's energy is bounded by its own resource. -/
theorem filling_resource_energy (p : State b) :
    (∑ i, |displacement p i|) ≤ 2*fillingResource p*(fillingResource p+1) := by
  have hw := filling_resource_half_width p
  have hk : 0 ≤ fillingResource p := by omega
  have hb : (b : ℤ) ≤ 2*fillingResource p+1 := by omega
  have he := finite_energy_fixed_square p
  have hsq : (b : ℤ)^2 ≤ (2*fillingResource p+1)^2 := by
    have h := mul_nonneg (show 0 ≤ 2*fillingResource p+1-(b : ℤ) by omega)
      (show 0 ≤ 2*fillingResource p+1+(b : ℤ) by positivity)
    nlinarith
  have hraw : 2*(∑ i, |displacement p i|) ≤ 4*fillingResource p*(fillingResource p+1)+1 := by
    nlinarith [sq_nonneg (((b-p.support.card : ℕ) : ℤ))]
  have heven : 4*fillingResource p*(fillingResource p+1)=
      2*(2*fillingResource p*(fillingResource p+1)) := by ring
  rw [heven] at hraw
  omega

/-- The squared-width filter used in the finite M4 search. -/
theorem filling_resource_square_width (p : State b) :
    (b : ℤ)^2 ≤ 4*(fillingResource p)^2+2*fillingResource p+(b : ℤ) := by
  have hw := filling_resource_half_width p
  have hk : 0 ≤ fillingResource p := by omega
  have hb : (b : ℤ) ≤ 2*fillingResource p+1 := by omega
  have h := mul_nonneg (show 0 ≤ 2*fillingResource p+1-(b : ℤ) by omega)
    (show 0 ≤ 2*fillingResource p+(b : ℤ) by positivity)
  nlinarith

/-- Fixed-free fillings retain the sharper defect correction in their energy. -/
theorem filling_resource_fixed_free_energy (p : State b) (hf : p.support.card=b) :
    0 ≤ fillingResource p-cycleDefect p ∧
      (∑ i, |displacement p i|) ≤ 2*(fillingResource p-cycleDefect p)^2 := by
  have hw := filling_resource_width_defect p
  rw [hf,Nat.sub_self,Nat.cast_zero,add_zero] at hw
  have he := finite_energy_fixed_square p
  have hk : 0 ≤ fillingResource p-cycleDefect p := by omega
  refine ⟨hk,?_⟩
  have h := mul_nonneg
    (show 0 ≤ 2*(fillingResource p-cycleDefect p)-(b : ℤ) by omega)
    (show 0 ≤ 2*(fillingResource p-cycleDefect p)+(b : ℤ) by positivity)
  nlinarith [sq_nonneg (((b-p.support.card : ℕ) : ℤ))]

#print axioms filling_resource_defect_bound
#print axioms filling_resource_half_width
#print axioms filling_resource_width_defect
#print axioms filling_resource_energy
#print axioms filling_resource_square_width
#print axioms filling_resource_fixed_free_energy
end LRX.FiniteCuts

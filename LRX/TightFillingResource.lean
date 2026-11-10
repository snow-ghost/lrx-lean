module

public import LRX.BitonicNonshortDefect
public import LRX.FiniteFillingResource

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

theorem cycle_count_le_peak_sum (p : State b) : p.cycleFactorsFinset.card ≤ cyclePeakSum p := by
  classical
  calc
    _ = ∑ _c ∈ p.cycleFactorsFinset, (1 : ℕ) := by simp
    _ ≤ ∑ c ∈ p.cycleFactorsFinset, leftPeak c b := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨i,hi⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
      letI : NeZero b := ⟨by have := i.isLt; omega⟩
      exact moved_global_peak_positive c i (Equiv.Perm.mem_support.mp hi)

theorem cycle_peaks_one_of_sum_eq_count (p : State b)
    (heq : cyclePeakSum p=p.cycleFactorsFinset.card) :
    ∀ c ∈ p.cycleFactorsFinset, leftPeak c b=1 := by
  classical
  have hpos (c : State b) (hc : c ∈ p.cycleFactorsFinset) : 1 ≤ leftPeak c b := by
    obtain ⟨i,hi⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
    letI : NeZero b := ⟨by have := i.isLt; omega⟩
    exact moved_global_peak_positive c i (Equiv.Perm.mem_support.mp hi)
  intro c hc
  have hrest := Finset.sum_le_sum (s := p.cycleFactorsFinset.erase c)
    (f := fun _ => (1 : ℕ)) (g := fun c => leftPeak c b)
    (fun r hr => hpos r (Finset.mem_of_mem_erase hr))
  simp only [Finset.sum_const,Finset.card_erase_of_mem hc,smul_eq_mul,mul_one] at hrest
  have hadd := Finset.sum_erase_add p.cycleFactorsFinset (fun c => leftPeak c b) hc
  let restSum := ∑ r ∈ p.cycleFactorsFinset.erase c, leftPeak r b
  change p.cycleFactorsFinset.card-1 ≤ restSum at hrest
  change restSum+leftPeak c b=cyclePeakSum p at hadd
  have hcard := Finset.card_pos.mpr ⟨c,hc⟩
  have hcpos := hpos c hc
  omega

/-- Equality in the fixed-free width reserve forces every cycle peak to one. -/
theorem tight_filling_width_cycle_peaks (p : State b) (hf : p.support.card=b)
    (ht : (b : ℤ)=2*fillingResource p-2*cycleDefect p) :
    ∀ c ∈ p.cycleFactorsFinset, leftPeak c b=1 := by
  have hh := filling_resource_defect_bound p
  have hs := twice_cycle_peak_sum_le_support p
  have hk := twice_cycle_count_le_support p
  have hks := cycle_count_le_peak_sum p
  rw [hf] at hh hs hk
  let z : ℤ := (b : ℤ)-2*(cyclePeakSum p : ℤ)
  have hz : 0 ≤ z := by dsimp only [z]; omega
  have hzprod : 0 ≤ z*(z-1) := by
    by_cases hzero : z=0
    · rw [hzero]; norm_num
    · exact mul_nonneg hz (by omega)
  change 2*((b : ℤ)-(p.cycleFactorsFinset.card : ℤ)+cycleDefect p)+z*(z-1) ≤
    2*fillingResource p at hh
  have heq : cyclePeakSum p=p.cycleFactorsFinset.card := by omega
  exact cycle_peaks_one_of_sum_eq_count p heq

/-- D3 excludes equality in the width reserve for nonshort defect-two fillings. -/
theorem nonshort_small_defect_strict_width (p : State b) (hb : 0 < b)
    (hf : p.support.card=b) (hmin : ∀ i, 3 ≤ |displacement p i|)
    (hz : cycleDefect p ≤ 2) : (b : ℤ)<2*fillingResource p-2*cycleDefect p := by
  classical
  letI : NeZero b := ⟨by omega⟩
  have hw := filling_resource_width_defect p
  rw [hf,Nat.sub_self] at hw
  simp only [Nat.cast_zero,add_zero] at hw
  by_contra hh
  have heq : (b : ℤ)=2*fillingResource p-2*cycleDefect p := by omega
  have hp := tight_filling_width_cycle_peaks p hf heq
  have hfull : p.support=Finset.univ := Finset.eq_univ_of_card p.support
    (by simpa only [Fintype.card_fin] using hf)
  have hd := full_support_peak_one_nonshort_defect_ge_four p hfull hmin
    (fun c hc => le_of_eq (hp c hc))
  omega

#print axioms cycle_count_le_peak_sum
#print axioms cycle_peaks_one_of_sum_eq_count
#print axioms tight_filling_width_cycle_peaks
#print axioms nonshort_small_defect_strict_width
end LRX.FiniteCuts

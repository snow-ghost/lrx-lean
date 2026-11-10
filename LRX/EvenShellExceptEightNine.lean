import LRX.ActualShellInternalPayment
import LRX.ActualEvenExteriorExceptions

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

theorem prefix_even_exterior_actual_shell_paid_except_eight_nine (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (heven : (prefixSourceCore p).card%2=0) (hU : sourceHalfPeak p=2)
    (hdom : (componentSet p 0).card-(prefixSourceCore p).card < n-(componentSet p 0).card)
    (h8 : n ≠ 8) (h9 : n ≠ 9) : shellE p ≤ 0 := by
  by_contra hbad
  let L := (componentSet p 0).card
  let R := (prefixSourceCore p).card
  let t : ℤ := (n : ℤ)-2*(L : ℤ)+(R : ℤ)
  have hRL : R ≤ L := by
    apply Finset.card_le_card
    intro i hi
    exact (zero_component_prefix p i).mpr (Finset.mem_filter.mp hi).2
  have hLn := component_card_lt_of_multiple_roots p hm 0
  have ht : 0 ≤ t := by dsimp only [t,L,R]; omega
  have hprice := prefix_even_shell_exterior_price p hmaj hm hlarge hz heven
  change shellE p ≤ 2-2*(shellH p-t^2/4) at hprice
  have hquad := prefix_zero_defect_exterior_deficit p hmaj hm hlarge hz
  have htform : (n : ℤ)-2*(L : ℤ)+2*((R/2 : ℕ) : ℤ)=t := by dsimp [t,R]; omega
  change (max 0 ((n : ℤ)-2*(L : ℤ)+2*((R/2 : ℕ) : ℤ)))^2/4 ≤ shellH p at hquad
  rw [htform,max_eq_right ht] at hquad
  have hHeq : shellH p=t^2/4 := by omega
  have hone := prefix_even_exterior_shell_paid_or_small p hmaj hm hlarge hz heven hU hdom 1 0
    (by norm_num) (by change 1 ≤ 1-2*(shellH p-t^2/4)-0; rw [hHeq]; norm_num)
  omega

theorem prefix_even_shell_paid_except_eight_nine (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (heven : (prefixSourceCore p).card%2=0) (hU : sourceHalfPeak p=2)
    (h8 : n ≠ 8) (h9 : n ≠ 9) : shellE p ≤ 0 := by
  by_cases hT : 0 ≤ shellT p
  · exact prefix_even_shell_nonnegative_T_paid p hmaj hm hlarge hz heven hT
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  obtain ⟨b,hb,hdom⟩ := shell_negative_T_dominant_width p hm hc heven (by omega)
  rw [shell_widths_sum p hm hc] at hdom
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hb
    exact prefix_even_internal_actual_shell_paid p hmaj hm hlarge hz heven B hB hdom
  · have hbval : b=n-(componentSet p 0).card := by simpa using hb
    rw [hbval] at hdom
    have hproper := component_card_lt_of_multiple_roots p hm 0
    have hpart := prefix_internal_size_partition p hc hproper
    exact prefix_even_exterior_actual_shell_paid_except_eight_nine p hmaj hm hlarge hz heven hU (by omega) h8 h9

#print axioms prefix_even_exterior_actual_shell_paid_except_eight_nine
#print axioms prefix_even_shell_paid_except_eight_nine
end LRX.FiniteCuts

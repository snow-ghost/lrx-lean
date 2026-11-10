import LRX.ActualEvenExteriorShape
import LRX.ActualOddShellPayment
import LRX.ActualShellInternalPayment

namespace LRX.FiniteCuts
open FiniteWindow RotationWords

/-- Every actual zero-defect size-nine input is already sharp, or its
prefix and source core both have exactly six positions and reserve two. -/
theorem prefix_nine_sharp_or_shell_shape (p : State 9)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (hlarge : (9+1)/2 < (componentSet p 0).card)
    (hz : cycleDefect p=0) (hU : sourceHalfPeak p=2) (start finish : Fin 9) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ Nat.choose 9 2) ∨
    ((componentSet p 0).card=6 ∧ (prefixSourceCore p).card=6 ∧ shellH p=2) := by
  classical
  have hc : 2 ≤ (componentSet p 0).card := by omega
  by_cases heven : (prefixSourceCore p).card%2=0
  · by_cases hpaid : shellE p ≤ 0
    · exact Or.inl (shell_sharp_word_of_nonpos p hmaj hm hlarge hz hpaid start finish)
    have hpos : 0 < shellE p := by omega
    have hT : shellT p < 0 := by
      by_contra hh
      have hpay := prefix_even_shell_nonnegative_T_paid p hmaj hm hlarge hz heven (by omega)
      omega
    obtain ⟨b,hb,hdom⟩ := shell_negative_T_dominant_width p hm hc heven hT
    rw [shell_widths_sum p hm hc] at hdom
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hb
      have hpay := prefix_even_internal_actual_shell_paid p hmaj hm hlarge hz heven B hB hdom
      omega
    · have hbval : b=9-(componentSet p 0).card := by simpa using hb
      rw [hbval] at hdom
      let L := (componentSet p 0).card
      let R := (prefixSourceCore p).card
      let t : ℤ := 9-2*(L : ℤ)+(R : ℤ)
      have hproper := component_card_lt_of_multiple_roots p hm 0
      have hpart := prefix_internal_size_partition p hc hproper
      have hdom' : (componentSet p 0).card-(prefixSourceCore p).card < 9-(componentSet p 0).card := by omega
      have ht : 0 ≤ t := by dsimp only [t,L,R]; omega
      have hprice := prefix_even_shell_exterior_price p hmaj hm hlarge hz heven
      change shellE p ≤ 2-2*(shellH p-t^2/4) at hprice
      have hquad := prefix_zero_defect_exterior_deficit p hmaj hm hlarge hz
      have htform : (9 : ℤ)-2*(L : ℤ)+2*((R/2 : ℕ) : ℤ)=t := by dsimp only [t,R,L]; omega
      change (max 0 ((9 : ℤ)-2*(L : ℤ)+2*((R/2 : ℕ) : ℤ)))^2/4 ≤ shellH p at hquad
      rw [htform,max_eq_right ht] at hquad
      have hHeq : shellH p=t^2/4 := by omega
      have hshape := prefix_even_exterior_shell_unpaid_shape p hmaj hm hlarge hz heven hU hdom' 1 0
        (by norm_num) (by change 1 ≤ 1-2*(shellH p-t^2/4)-0; rw [hHeq]; norm_num) (by norm_num)
      rcases hshape with hbad | hshape
      · omega
      · exact Or.inr ⟨hshape.2.2.1,hshape.2.1,hshape.2.2.2⟩
  · exact Or.inl (prefix_odd_shell_sharp_word p hmaj hm hlarge hz (by omega) (by decide) start finish)

#print axioms prefix_nine_sharp_or_shell_shape
end LRX.FiniteCuts

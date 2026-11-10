import LRX.ActualShellInternalPayment
import LRX.OddShellArithmetic

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

theorem shellH_nonnegative (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) : 0 ≤ shellH p := by
  have hh := prefix_core_balanced_energy_bound p hmaj
  dsimp only [shellH]
  omega

theorem prefix_odd_shell_member_price (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (hodd : (prefixSourceCore p).card%2=1) (b : ℕ) (hb : b ∈ shellWidths p) :
    shellE p ≤ 2-(leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ)-
      2*(((shellWidths p).sum-b : ℕ) : ℤ)-
      2*(shellH p-(2*(b : ℤ)-((shellWidths p).sum : ℤ)-1)^2/4) := by
  let xs := shellWidths p
  let l : ℤ := ((prefixSourceCore p).card/2 : ℕ)
  let c : ℤ := (xs.sum-b : ℕ)
  have hsum := shell_widths_sum p hm hc
  have hbSum : b ≤ xs.sum := List.single_le_sum (fun _ _ => Nat.zero_le _) b hb
  have hR : (prefixSourceCore p).card ≤ n := by simpa using Finset.card_le_univ (prefixSourceCore p)
  have hsize : (n : ℤ)=2*l+c+(b : ℤ)+1 := by
    dsimp only [l,c]
    change b ≤ (shellWidths p).sum at hbSum
    dsimp only [xs]
    omega
  have hsquares := member_square_sum_bound xs b hb
  have hh := odd_shell_member_price_bound n l c (b : ℤ)
    (leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ) (shellH p)
    ((xs.map (fun x : ℕ => (x : ℤ)^2)).sum-(b : ℤ)^2) hsize (by dsimp only [c]; linarith)
  have hcancel : ((xs.map (fun x : ℕ => (x : ℤ)^2)).sum-(b : ℤ)^2)+(b : ℤ)^2=
      (xs.map (fun x : ℕ => (x : ℤ)^2)).sum := by ring
  rw [hcancel] at hh
  have heE : shellE p=3-(leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ)-2*shellH p-(n%2 : ℕ)-
      (2*(((n : ℤ)-2*l)^2/4)-(xs.map (fun x : ℕ => (x : ℤ)^2)).sum) := by
    rw [shellE,shellT_widths]
  have heq : (b : ℤ)-c-1=2*(b : ℤ)-(xs.sum : ℤ)-1 := by dsimp only [c]; omega
  rw [← heE,heq] at hh
  exact hh

theorem prefix_odd_shell_nondominant_paid (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (hodd : (prefixSourceCore p).card%2=1)
    (hbound : ∀ b ∈ shellWidths p, 2*b ≤ (shellWidths p).sum+1) : shellE p ≤ 0 := by
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have hsum := shell_widths_sum p hm hc
  have hproper := component_card_lt_of_multiple_roots p hm 0
  have hpart := prefix_internal_size_partition p hc hproper
  have hout := prefix_multiple_components_exterior_size p hc hm
  have hU := prefix_shell_core_peak_pos p hmaj hm hlarge hz
  have hh := odd_shell_nondominant_paid n (((prefixSourceCore p).card/2 : ℕ) : ℤ)
    (leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ) (shellH p) (shellWidths p)
    (by omega) (by omega) (shellH_nonnegative p hmaj) (by omega) hbound
  simpa only [shellE,shellT_widths] using hh

theorem prefix_odd_internal_actual_shell_paid (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (hodd : (prefixSourceCore p).card%2=1)
    (B : FillingWindow n) (hB : B ∈ positiveSourceFamily p (componentSet p 0).card)
    (hdom : (shellWidths p).sum+1 < 2*B.size) : shellE p ≤ 0 := by
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have hb : B.size ∈ shellWidths p := List.mem_append_left _ (List.mem_map.mpr ⟨B,hB,rfl⟩)
  have hprice := prefix_odd_shell_member_price p hm hc hodd B.size hb
  have hsum := shell_widths_sum p hm hc
  have hout := prefix_multiple_components_exterior_size p hc hm
  have hpart := prefix_internal_size_partition p hc (component_card_lt_of_multiple_roots p hm 0)
  have hbint : B.size ≤ ((positiveSourceFamily p (componentSet p 0).card).map (fun B => B.size)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) B.size (List.mem_map.mpr ⟨B,hB,rfl⟩)
  have hrest : 2 ≤ (shellWidths p).sum-B.size := by omega
  let t : ℤ := 2*(B.size : ℤ)-((shellWidths p).sum : ℤ)-1
  have ht : 1 ≤ t := by dsimp only [t]; omega
  have hgeom := prefix_zero_defect_window_internal_deficit p hmaj hm hlarge hz B hB
  dsimp only at hgeom
  rw [hodd,← hsum,Nat.cast_one,max_eq_right (show 0 ≤ t by omega)] at hgeom
  have hprod : 0 ≤ 8*(t/2)*((n-(componentSet p 0).card : ℕ) : ℤ) := by positivity
  have hquad : t^2/4 ≤ shellH p := by omega
  have hU := prefix_shell_core_peak_pos p hmaj hm hlarge hz
  change shellE p ≤ 2-_-2*_-2*(shellH p-t^2/4) at hprice
  omega

#print axioms prefix_odd_shell_member_price
#print axioms prefix_odd_shell_nondominant_paid
#print axioms prefix_odd_internal_actual_shell_paid
end LRX.FiniteCuts

module

public import LRX.ActualOddShellWidths
public import LRX.PrefixPacketPeakEnergy

@[expose] public section

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- A unit-peak odd core cannot saturate the exterior quadratic reserve
once its half-size is at least two. -/
theorem odd_unit_peak_strict_reserve (l e D H : ℤ)
    (hl : 2 ≤ l) (he : 2 ≤ e) (hetop : e ≤ 2*l-1)
    (hD : D ≤ 4*l) (hH : H=l*(l+1+e)-D) :
    (e-1)^2/4 < H := by
  have hp := mul_nonneg (show 0 ≤ e-2 by omega) (show 0 ≤ 2*l-1-e by omega)
  have hfloor : 4*((e-1)^2/4) ≤ (e-1)^2 := by omega
  have hlprod := mul_nonneg (show 0 ≤ l-2 by omega) (show 0 ≤ l by omega)
  have heprod := mul_nonneg (show 0 ≤ 2*l+1 by omega) (show 0 ≤ e-2 by omega)
  nlinarith

theorem prefix_odd_exterior_actual_shell_paid (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (hodd : (prefixSourceCore p).card%2=1) (hn : 4 ≤ n)
    (hdom : (shellWidths p).sum+1 < 2*(n-(componentSet p 0).card)) : shellE p ≤ 0 := by
  let L := (componentSet p 0).card
  let R := (prefixSourceCore p).card
  let e := n-L
  let l : ℤ := (R/2 : ℕ)
  let t : ℤ := 2*(e : ℤ)-((shellWidths p).sum : ℤ)-1
  have hc : 2 ≤ (componentSet p 0).card := by omega
  have hproper := component_card_lt_of_multiple_roots p hm 0
  have hpart := prefix_internal_size_partition p hc hproper
  have hsum := shell_widths_sum p hm hc
  have hout := prefix_multiple_components_exterior_size p hc hm
  have hb : e ∈ shellWidths p := List.mem_append_right _ (List.mem_cons_self ..)
  have hprice := prefix_odd_shell_member_price p hm hc hodd e hb
  change shellE p ≤ 2-_-2*_-2*(shellH p-t^2/4) at hprice
  have hU := prefix_shell_core_peak_pos p hmaj hm hlarge hz
  have ht : 0 ≤ t := by dsimp only [t,e,L]; omega
  have hquad := prefix_zero_defect_exterior_deficit p hmaj hm hlarge hz
  change (max 0 ((n : ℤ)-2*(L : ℤ)+2*l))^2/4 ≤ shellH p at hquad
  have htform : (n : ℤ)-2*(L : ℤ)+2*l=t := by dsimp only [t,e,L,l,R]; omega
  rw [htform,max_eq_right ht] at hquad
  by_cases hrest : 1 ≤ (shellWidths p).sum-e
  · omega
  have hLR : L=R := by dsimp only [e,L,R] at *; omega
  by_cases hbigU : 2 ≤ leftPeak ((canonicalRootPacket p 0)⁻¹) n
  · omega
  have hUone : leftPeak ((canonicalRootPacket p 0)⁻¹) n=1 := by omega
  have henergy := prefix_packet_peak_energy p hm hc 1 (by omega) (by omega)
  have hL : (L : ℤ)=2*l+1 := by dsimp only [l,R]; omega
  have hN : (n : ℤ)=2*l+1+(e : ℤ) := by dsimp only [e,L]; omega
  have hHform : shellH p=l*(l+1+(e : ℤ))-(∑ i ∈ prefixSourceCore p, |displacement p.symm i|) := by
    change l*((n : ℤ)-l)-_= _
    rw [hN]
    ring
  have hstrict := odd_unit_peak_strict_reserve l (e : ℤ)
    (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) (shellH p)
    (by dsimp only [l,R,e,L] at *; omega) (by dsimp only [e,L]; omega)
    (by dsimp only [e,L] at *; omega) (by norm_num at henergy; rw [hL] at henergy; linarith) hHform
  have hteq : t=(e : ℤ)-1 := by dsimp only [t,e,L,R] at *; omega
  rw [← hteq] at hstrict
  omega

theorem prefix_odd_shell_paid (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (hodd : (prefixSourceCore p).card%2=1) (hn : 4 ≤ n) : shellE p ≤ 0 := by
  classical
  by_cases hb : ∀ b ∈ shellWidths p, 2*b ≤ (shellWidths p).sum+1
  · exact prefix_odd_shell_nondominant_paid p hmaj hm hlarge hz hodd hb
  push Not at hb
  obtain ⟨b,hb,hdom⟩ := hb
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hb
    exact prefix_odd_internal_actual_shell_paid p hmaj hm hlarge hz hodd B hB hdom
  · have hbval : b=n-(componentSet p 0).card := by simpa using hb
    rw [hbval] at hdom
    exact prefix_odd_exterior_actual_shell_paid p hmaj hm hlarge hz hodd hn hdom

theorem prefix_odd_shell_sharp_word (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (hodd : (prefixSourceCore p).card%2=1) (hn : 4 ≤ n) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      w.length ≤ n.choose 2 :=
  shell_sharp_word_of_nonpos p hmaj hm hlarge hz
    (prefix_odd_shell_paid p hmaj hm hlarge hz hodd hn) start finish

#print axioms odd_unit_peak_strict_reserve
#print axioms prefix_odd_exterior_actual_shell_paid
#print axioms prefix_odd_shell_paid
#print axioms prefix_odd_shell_sharp_word
end LRX.FiniteCuts

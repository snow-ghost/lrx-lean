import LRX.ActualShellEvenPayment
import LRX.ShellWidthArithmetic

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

noncomputable def shellWidths (p : State n) : List ℕ :=
  ((positiveSourceFamily p (componentSet p 0).card).map (fun B => B.size))++
    [n-(componentSet p 0).card]

theorem shell_widths_sum (p : State n) (hm : 2 ≤ (componentRoots p).card)
    (hc : 2 ≤ (componentSet p 0).card) :
    (shellWidths p).sum=n-(prefixSourceCore p).card := by
  have hproper := component_card_lt_of_multiple_roots p hm 0
  have hh := prefix_internal_size_partition p hc hproper
  simp only [shellWidths,List.sum_append,List.sum_cons,List.sum_nil,add_zero]
  omega

theorem shellT_widths (p : State n) :
    shellT p=2*(((n : ℤ)-2*(( (prefixSourceCore p).card/2 : ℕ) : ℤ))^2/4)-
      ((shellWidths p).map (fun b : ℕ => (b : ℤ)^2)).sum := by
  simp only [shellT,shellWidths,List.map_append,List.map_map,Function.comp_def,
    List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]

/-- Negative T forces a dominant member of this exact width list. -/
theorem shell_negative_T_dominant_width (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (heven : (prefixSourceCore p).card%2=0) (hT : shellT p < 0) :
    ∃ b ∈ shellWidths p, (shellWidths p).sum < 2*b := by
  classical
  by_contra h
  push_neg at h
  have hbound : ∀ b ∈ shellWidths p, 2*(b : ℤ) ≤ ((shellWidths p).sum : ℤ) := by
    intro b hb
    exact_mod_cast h b hb
  have hcap := half_bounded_square_sum (shellWidths p) ((shellWidths p).sum : ℤ) hbound
  have hsum := shell_widths_sum p hm hc
  have hR : (prefixSourceCore p).card ≤ n := by simpa using Finset.card_le_univ (prefixSourceCore p)
  have hsize : (n : ℤ)-2*(((prefixSourceCore p).card/2 : ℕ) : ℤ)=
      ((shellWidths p).sum : ℤ) := by omega
  have hfloor := floor_square_even_shift n (((prefixSourceCore p).card/2 : ℕ) : ℤ)
  rw [hsize] at hfloor
  have hform := shellT_widths p
  rw [hsize] at hform
  have hpar : ((n%2 : ℕ) : ℤ) ≤ 1 := by omega
  nlinarith

/-- Isolating any member b bounds all other squared widths by their total
width squared. This gives the actual shell price, including parity. -/
theorem prefix_even_shell_member_price (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (heven : (prefixSourceCore p).card%2=0)
    (b : ℕ) (hb : b ∈ shellWidths p) :
    shellE p ≤ 2-2*(shellH p-(2*(b : ℤ)-((n-(prefixSourceCore p).card : ℕ) : ℤ))^2/4) := by
  let xs := shellWidths p
  let l : ℤ := ((prefixSourceCore p).card/2 : ℕ)
  let c : ℤ := (xs.sum-b : ℕ)
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have hsum := shell_widths_sum p hm hc
  have hbSum : b ≤ xs.sum := List.single_le_sum (fun _ _ => Nat.zero_le _) b hb
  have hR : (prefixSourceCore p).card ≤ n := by simpa using Finset.card_le_univ (prefixSourceCore p)
  have hsize : (n : ℤ)=2*l+c+(b : ℤ) := by dsimp only [l,c]; change (shellWidths p).sum=n-(prefixSourceCore p).card at hsum; change b ≤ (shellWidths p).sum at hbSum; dsimp only [xs]; omega
  have hsquares := member_square_sum_bound xs b hb
  have hU : 1 ≤ (leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ) := by
    have hh := prefix_shell_core_peak_pos p hmaj hm hlarge hz
    omega
  have hh := shell_exterior_price_bound n l c (b : ℤ)
    (leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ) (shellH p)
    ((xs.map (fun x : ℕ => (x : ℤ)^2)).sum-(b : ℤ)^2) hsize hU (by dsimp only [c]; linarith)
  have hcancel : ((xs.map (fun x : ℕ => (x : ℤ)^2)).sum-(b : ℤ)^2)+(b : ℤ)^2=
      (xs.map (fun x : ℕ => (x : ℤ)^2)).sum := by ring
  rw [hcancel] at hh
  have heE : shellE p=3-(leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ)-2*shellH p-(n%2 : ℕ)-
      (2*(((n : ℤ)-2*l)^2/4)-(xs.map (fun x : ℕ => (x : ℤ)^2)).sum) := by
    rw [shellE,shellT_widths]
  have heq : (b : ℤ)-c=2*(b : ℤ)-((n-(prefixSourceCore p).card : ℕ) : ℤ) := by
    dsimp only [c,xs]
    omega
  rw [← heE,heq] at hh
  exact hh

#print axioms shell_negative_T_dominant_width
#print axioms prefix_even_shell_member_price
end LRX.FiniteCuts

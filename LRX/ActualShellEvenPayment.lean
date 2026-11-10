import LRX.ActualShellPrice
import LRX.ShellReservePayment
import LRX.PrefixFillingSize

namespace LRX.FiniteWindow
open scoped BigOperators
variable {n : ℕ}

theorem window_size_square_sum_le (As : List (FillingWindow n)) :
    (As.map (fun B => (B.size : ℤ)^2)).sum ≤ (((As.map (fun B => B.size)).sum : ℕ) : ℤ)^2 := by
  induction As with
  | nil => simp
  | cons B As ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    have hB : (0 : ℤ) ≤ B.size := by positivity
    have hs : (0 : ℤ) ≤ ((As.map (fun B => B.size)).sum : ℕ) := by positivity
    nlinarith [mul_nonneg hB hs]

end LRX.FiniteWindow

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem prefix_shell_core_peak_pos (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0) :
    0 < leftPeak ((canonicalRootPacket p 0)⁻¹) n := by
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  obtain ⟨hzero,_,_⟩ := prefix_component_source_ends p hc (component_card_lt_of_multiple_roots p hm 0)
  have hr : (0 : Fin n) ∈ p.support :=
    (mem_support_inverse p 0).mpr ((mem_source_packets p 0).mp hzero).1
  exact cycle_global_peak_positive _ (canonical_root_packet_shallow_of_zero_defect p hmaj 0 hr hz).1.inv

theorem prefix_even_shell_nonnegative_T_paid (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (heven : (prefixSourceCore p).card%2=0) (hT : 0 ≤ shellT p) : shellE p ≤ 0 := by
  have hU := prefix_shell_core_peak_pos p hmaj hm hlarge hz
  have hH := prefix_even_zero_defect_positive_reserve p hmaj hm hlarge hz heven
  change 1 ≤ shellH p at hH
  unfold shellE
  have hp : (0 : ℤ) ≤ (n%2 : ℕ) := by positivity
  omega

theorem prefix_even_shell_exterior_price (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (heven : (prefixSourceCore p).card%2=0) :
    shellE p ≤ 2-2*(shellH p-((n : ℤ)-2*((componentSet p 0).card : ℤ)+
      ((prefixSourceCore p).card : ℤ))^2/4) := by
  let L := (componentSet p 0).card
  let R := (prefixSourceCore p).card
  let l : ℤ := (R/2 : ℕ)
  let c : ℤ := (L : ℤ)-R
  let e : ℤ := (n-L : ℕ)
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have hLn := component_card_lt_of_multiple_roots p hm 0
  have hpart := prefix_internal_size_partition p hc hLn
  have hsizes : ((((positiveSourceFamily p L).map (fun B => B.size)).sum : ℕ) : ℤ)=c := by
    dsimp only [L,R,c]
    omega
  have hsquares := window_size_square_sum_le (positiveSourceFamily p L)
  rw [hsizes] at hsquares
  have hsize : (n : ℤ)=2*l+c+e := by dsimp only [l,c,e,L,R]; omega
  have hU : 1 ≤ (leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ) := by
    have hh := prefix_shell_core_peak_pos p hmaj hm hlarge hz
    omega
  have hh := shell_exterior_price_bound n l c e
    (leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ) (shellH p)
    (((positiveSourceFamily p L).map (fun B => (B.size : ℤ)^2)).sum) hsize hU hsquares
  have heq : e-c=(n : ℤ)-2*(L : ℤ)+(R : ℤ) := by dsimp only [e,c,L]; omega
  rw [heq] at hh
  exact hh

#print axioms prefix_even_shell_nonnegative_T_paid
end LRX.FiniteCuts
